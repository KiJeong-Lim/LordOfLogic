# Connect an editor to LoL

**English** · [한국어](editor.ko.md)

An editor can check an unsaved buffer one command at a time. Send `next` when
the reader advances the cursor. Render the hypotheses and goal from the
`proof` field of the reply.

Build with `cabal build lol` at the repository root. From the same directory,
start `"$(cabal list-bin lol)" --server`. Read and write one UTF-8 JSON object
per line over standard output and standard input. The server sends a `ready`
event before the first request. Keep standard error on a separate stream.
Use a JSON encoder so that line breaks in the source stay inside a single
request.

## Run a proof, undo a step, and replay it

Save the example as `editor_demo.py` and run `python3 editor_demo.py` from
the repository root. It sends the source in the `open` request. You can use
`Demo.lol` as the document path even before saving the file.

```python
import itertools
import json
import subprocess

binary = subprocess.check_output(["cabal", "list-bin", "lol"], text=True).strip()
source = """Theorem copy : forall P : Prop, P -> P.
Proof.
    intros P h.
    exact h.
Qed.
"""

with subprocess.Popen([binary, "--server"], stdin=subprocess.PIPE,
                      stdout=subprocess.PIPE, text=True, encoding="utf-8") as server:
    ready = json.loads(server.stdout.readline())
    assert ready["event"] == "ready" and ready["protocol"] == 2
    ids = itertools.count(1)

    def request(method, **fields):
        identity = next(ids)
        message = {"protocol": 2, "id": identity, "method": method, **fields}
        print(json.dumps(message), file=server.stdin, flush=True)
        reply = json.loads(server.stdout.readline())
        assert reply["id"] == identity
        if reply["status"] == "error":
            raise RuntimeError(reply["error"]["message"])
        return reply

    def reference(reply):
        return {key: reply[key] for key in ("document", "incarnation", "revision", "state")}

    doc = request("open", document="tutorial", revision=1, path="Demo.lol", source=source)
    for _ in range(3):  # Theorem, Proof, intros
        doc = request("next", **reference(doc))

    goal = request("show", **reference(doc))["proof"]
    for binding in reversed(goal["locals"]):
        print(binding["name"], ":", binding["typeDisplay"])
    print("Goal:", goal["display"])

    before_exact = doc["state"]
    doc = request("next", **reference(doc))  # exact h.
    assert request("show", **reference(doc))["proof"]["complete"]
    assert before_exact in doc["retainedStates"]

    doc = request("undo", **reference(doc), target=before_exact)
    print("Goal after undo:", doc["proof"]["display"])
    doc = request("next", **reference(doc))  # exact h. again
    print("Complete after next:", doc["proof"]["complete"])
    doc = request("next", **reference(doc))  # Qed.
    print(*doc["output"])
    request("close", **reference(doc))
    request("shutdown")
```

Expected output

```text
P : Prop
h : P
Goal: P
Goal after undo: P
Complete after next: True
The theorem was admitted.
```

After `intros P h.`, the goal is `P` and the local hypothesis `h` has that
type. The client saves the current **document state** before applying
`exact h.`. A `show` after that step reports `proof.complete` and leaves the
cursor in place. The client then asks `undo` to restore its saved state. The
goal reopens, and the cursor returns to the start of `exact h.`. Sending
`next` with the **new document reference from the undo reply** checks that
same command again.

`Qed.` adds the theorem to the environment and the server returns
`proof: null`. To implement “run to end”, continue sending `next` until you
receive `atEnd: true`. In the example that takes one more `next` after
`Qed.`.

## Edit a buffer

Use increasing positive request IDs throughout the connection. The largest
accepted ID is `9007199254740991`. When addressing an open document, copy
these four fields from the latest document reply.

| Field | Meaning |
| --- | --- |
| `document` | The editor’s name for this buffer. |
| `incarnation` | The ID of the request that opened it. Reopening the same name creates a new incarnation. |
| `revision` | The editor’s version number for the source text. |
| `state` | The server’s checkpoint for command execution. Use the top-level field. The nested `proof.state` belongs to the proof. |

| Editor action | Request |
| --- | --- |
| Add text to the end of the buffer | Send `append` with the document reference, a larger `nextRevision`, and the additional `source`. |
| Edit commands after the execution cursor | Send `replace` with the reference, a larger `nextRevision`, and the **entire new suffix** from the cursor to the end. |
| Edit a command already checked | Send `undo` with the reference and an earlier document state from `retainedStates` as `target`. Use the returned reference for `replace`. |
| Switch buffers | Send `close` with the current reference and `open` the other buffer. A server process holds one open document. |

For example, insert the following call immediately before
`before_exact = doc["state"]`. The first `next` after the edit and the first
`next` after undo will now each run `assumption.`.

```python
    doc = request("replace", **reference(doc), nextRevision=doc["revision"] + 1,
                  source="\nassumption.\nQed.\n")
```

The leading `\n` separates the new tactic from the period at the end of
`intros P h.`. Joining `assumption.` directly to that period would change
the preceding command's token boundary. The server returns
`document-boundary` in that case.

## Handle diagnostics and cancellation

- On `status: "error"`, display `error.message`. A source diagnostic can
  carry `error.range`. Its lines and columns are 1-based, and columns count
  Unicode scalar values. If the reply includes a document reference, use it
  for the next request. `stale-incarnation`, `stale-revision`, and
  `stale-state` identify which part of an outdated reference failed.
- Send one ordinary request at a time. To interrupt a long-running `next`,
  send `cancel` with a new ID and put the running **request ID** in `target`.
  Match both replies by ID. A successful cancellation reply acknowledges
  the request. The original reply determines the outcome and document state.
  `busy` signals an overlapping ordinary request. `not-cancellable` means
  the target is no longer running or is completing an atomic operation.
- The `ready` event advertises `requestByteLimit` for each encoded request
  line. Exceeding it closes the server after a `frame-too-large` error. Use
  `append` to send a large buffer in chunks. The entire source is limited
  to 524,288 characters. For a large goal, check `proof.truncated` and allow
  for `null` display strings.
- For an editor that needs a shorter kernel timeout, launch the server with
  an option such as `--timeout-ms=5000`. The other resource options are
  `--work-limit=N`, `--memory-mib=N` for native memory, and
  `--host-allocation-mib=N` for host allocation.
- At exit, send `shutdown`, read its reply, then wait for the process to
  exit.

Return to the [reference guide](reference.md).
