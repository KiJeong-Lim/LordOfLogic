"""Run ordinary imports through the on-disk cache and the actual Hol kernel."""
from concurrent.futures import ThreadPoolExecutor
from hashlib import sha256
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile

root = Path.cwd()
binary = Path(sys.argv[1]).resolve()
if os.name != "posix":
    print("This platform uses the source loader for every import.")
    sys.exit(0)


def run(file="Client.lol", ok=True, options=(), environment=None):
    result = subprocess.run([binary, *options, file], cwd=work,
                            env=environment or env, capture_output=True,
                            text=True, timeout=15)
    assert (result.returncode == 0) == ok, (file, result.stdout, result.stderr)
    return result.stdout, result.stderr


def hits(log):
    return {line.removeprefix("LoL import cache hit: ") for line in log.splitlines()
            if line.startswith("LoL import cache hit: ")}


def write(name, text):
    (work / name).write_text(text)


with tempfile.TemporaryDirectory(prefix="lol-import-cache-") as tmp:
    work = Path(tmp)
    shutil.copytree(root / "lol" / "hol", work / "lol" / "hol")
    env = dict(os.environ, XDG_CACHE_HOME=str(work / "cache"), LOL_IMPORT_CACHE_TRACE="1")
    env.pop("LOL_IMPORT_CACHE", None)
    storage = work / "cache" / "lord-of-logic" / "imports"
    a = "Axiom P : Prop. Definition d : Prop := P."
    write("A.lol", a)
    write("Left.lol", "Import A. Definition l : Prop := d.")
    write("Right.lol", "Import A. Definition r : Prop := d.")
    initial = "Import Left. Import Right. Check l. Check r."
    write("Client.lol", initial)
    cold, log = run()
    assert not hits(log)
    warm, log = run()
    assert cold == warm and hits(log) == {"A", "Left", "Right"}
    assert len(list(storage.glob("*.loc"))) == 3
    write("Client.lol", initial + " Check missing.")
    assert "missing" in "".join(run(ok=False))
    write("Client.lol", initial)
    write("A.lol", a.replace(":= P", ":= Set"))
    assert not hits(run(ok=False)[1])
    write("A.lol", a + " Axiom extra : Prop.")
    assert not (hits(run()[1]) & {"Left", "Right"})
    assert hits(run()[1]) == {"A", "Left", "Right"}

    entry = next(p for p in storage.glob("*.loc") if '(LoLObject 3 "A"' in p.read_text())
    valid = entry.read_text()
    entry.write_text("damaged cache metadata")
    assert "A" not in hits(run()[1])
    assert entry.read_text() == valid
    # A locally generated yet ill-typed object with a correct checksum must
    # fail at kernel admission. The admitted prefix is discarded before retry.
    key, _, metadata, obj = valid.split("\n", 3)
    changed = obj.replace('(definition (prop) (const "A.P"))', '(definition (prop) (app (const "A.P") (const "A.P")))')
    assert changed != obj
    packet_hash = sha256((key + "\n" + metadata + "\n" + changed).encode()).hexdigest()
    entry.write_text("\n".join((key, packet_hash, metadata, changed)))
    assert "A" not in hits(run()[1])
    assert entry.read_text() == valid
    target = work / "victim"
    target.write_text(valid)
    entry.unlink()
    entry.symlink_to(target)
    assert "A" not in hits(run()[1]) and not entry.is_symlink()
    assert target.read_text() == valid
    storage.chmod(0o777)
    assert not hits(run()[1])
    storage.chmod(0o700)
    assert not hits(run(environment=dict(env, LOL_IMPORT_CACHE="off"))[1])
    for p in storage.glob("*.loc"):
        p.unlink()
    with ThreadPoolExecutor(max_workers=2) as workers:
        outputs = list(workers.map(lambda _: run()[0], range(2)))
    assert outputs == [cold, cold]
    assert hits(run()[1]) == {"A", "Left", "Right"}

    for filename in ("kernel.hol", "elab.hol"):
        program = work / "lol" / "hol" / filename
        original = program.read_text()
        program.write_text(original + "\n% A new source revision.\n")
        assert not hits(run()[1])
        assert hits(run()[1]) == {"A", "Left", "Right"}
        program.write_text(original)
        assert not hits(run()[1])
    run(options=("--emit-object=Export.lolo",))
    standalone, _ = run("Export.lolo", options=("--check-only",))
    assert "Client" in standalone

    # An Import erased by Undo still has to succeed during source execution.
    write("Unused.lol", "Axiom U : Prop.")
    write("Rolled.lol", "Import Unused. Undo. Axiom w : Prop.")
    write("UndoClient.lol", "Import Rolled. Check w.")
    run("UndoClient.lol")
    assert "Rolled" not in hits(run("UndoClient.lol")[1])
    (work / "Unused.lol").unlink()
    run("UndoClient.lol", ok=False)

    # Check a custom program with a transitive Hol import, then change its
    # implementation without touching the LoL file or the directly loaded file.
    write("Helper.hol", 'import lol.hol.tactics.\np_user_tactic "give" (Template :: []) A R :- e_fresh Template R.\n')
    write("Tools.hol", 'import Helper.\n')
    write("Proofs.lol", 'Load Tactics "Tools.hol". Theorem identity : forall P : Prop, P -> P. Proof. intros P h. tactic give (h). Qed.')
    write("ProofClient.lol", "Import Proofs. Check identity.")
    run("ProofClient.lol")
    assert hits(run("ProofClient.lol")[1]) == {"Proofs"}
    write("Helper.hol", 'import lol.hol.tactics.\n')
    assert "Proofs" not in hits(run("ProofClient.lol", ok=False)[1])

    # The second branch of a live document cannot combine two revisions.
    proc = subprocess.Popen([binary, "--server"], cwd=work, env=env,
                            stdin=subprocess.PIPE, stdout=subprocess.PIPE,
                            stderr=subprocess.DEVNULL, text=True)
    try:
        assert json.loads(proc.stdout.readline())["event"] == "ready"

        def request(identity, method, **fields):
            message = dict(protocol=2, id=identity, method=method, **fields)
            proc.stdin.write(json.dumps(message) + "\n")
            proc.stdin.flush()
            return json.loads(proc.stdout.readline())

        state = request(1, "open", document="d", revision=0, path="Editor.lol",
                        source="Import Left. Import Right.")
        assert state["status"] == "ok"
        def current(reply):
            return {key: reply[key] for key in ("document", "incarnation", "revision", "state")}
        state = request(2, "next", **current(state))
        assert state["status"] == "ok", state
        write("A.lol", a + " Axiom changed : Prop.")
        conflict = request(3, "next", **current(state))
        assert conflict["status"] == "error" and "I-VersionConflict" in str(conflict), conflict
        request(4, "shutdown")
    finally:
        proc.stdin.close()
        proc.wait(timeout=8)
print("Source import cache: warm replay, kernel refusal, changed sources, undo, live diamond, tactics, private storage and concurrent publication passed.")
