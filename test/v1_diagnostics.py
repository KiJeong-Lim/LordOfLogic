"""Compare the human and editor reports with the actual failed kernel premises."""
import json
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path


binary = Path(sys.argv[1]).resolve()
kernels = Path.cwd() / "lol/hol"
scheme = "Polymorphic Definition lt@{u v | u < v} : Type@{v} := Type@{u}.\n"


with tempfile.TemporaryDirectory() as directory:
    work = Path(directory)
    shutil.copytree(kernels, work / "lol/hol")

    def run(*arguments, status=1):
        process = subprocess.run([binary, *arguments], cwd=work, capture_output=True,
                                 text=True, timeout=15)
        assert process.returncode == status, (arguments, process)
        return process.stdout + process.stderr

    def source(content):
        (work / "Diagnostic.lol").write_text(content)
        return run("Diagnostic.lol")

    bad = "Definition bad : Type@{0} := Type@{0}.\n"
    expected = ["term: Type@{0}", "has type: Type@{1}", "expected: Type@{0}"]
    mismatch = source(bad)
    assert "[T-Conv]" in mismatch and "1 | Definition bad" in mismatch, mismatch
    assert [line.strip() for line in mismatch.splitlines() if line.startswith("  ")][-3:] == expected, mismatch

    poly = "Inductive N : Set := | z : N. Axiom id : forall {A : Set}, A -> A.\n"
    sort = source(poly + "Check id (fun (x : z) => x).")
    assert "[E-Unify]" in sort and "term: z" in sort and "has type: N" in sort and "expected:" not in sort, sort
    coercion = source(poly + "Definition b : N -> N := fun x => Prop.")
    assert "[E-Unify]" in coercion and "has type: Type@{1}" in coercion and "expected: N" in coercion, coercion

    # An unapplied match binder can be left by either the motive or a branch.
    naturals = "Inductive N : Set := | z : N | s : N -> N.\n"
    for term, detail in [
        ("match n in N k return N with | z => z | s p => p end", "unexpected match binder: fun x => N"),
        ("match n return N with | z => z | s p q => p end", "unexpected match binder: under free names"),
        ("match n return N with | z => z | s => z end", "branch: z"),
        ("match n return N with | z => z end", "missing branch for constructor: s"),
    ]:
        failed = source(naturals + "Check fun n : N => " + term + ".")
        assert "[T-Match]" in failed and detail in failed, failed
    conclusion = source(naturals + "Inductive Misplaced : Set := | c : N.")
    assert "[I-Con]" in conclusion and "constructor result: N" in conclusion, conclusion

    selected = source(scheme + "Check lt@{1 1}.")
    assert "[E-Unify]" in selected and "conflicting universe constraint: 1 < 1" in selected, selected
    required = source(scheme + "Polymorphic Definition forced@{small large | } : Type@{large} := lt@{small large}.")
    assert "required universe constraint: small < large" in required, required

    theorem = "Polymorphic Theorem proof@{left right | } (A : Type@{left}) (B : Type@{right}) : Type@{right}."
    for tactic in ["exact A", "first [exact A | exact B]"]:
        rejected = source(theorem + "\nProof.\n" + tactic + ".\nQed.")
        assert "[E-Declared]" in rejected and "4 | Qed." in rejected, rejected
        assert "required universe constraint: left <= right" in rejected, rejected
    (work / "Diagnostic.lol").write_text(theorem + " Proof. first [exact B | exact A]. Qed.")
    run("Diagnostic.lol", status=0)

    # A binary object has a module and declaration but no source line.
    (work / "Object.lolo").write_text("()")
    def object_error():
        text = run("--check-only", "Object.lolo")
        assert "Object.lolo: error:" in text and "1:1" not in text and " | " not in text, text
        return text
    assert "[I-Object]" in object_error()
    (work / "Object.lol").write_text(scheme + "Definition good : Type@{2} := lt@{1 2}.")
    run("--emit-object=Object.lolo", "Object.lol", status=0)
    obj = (work / "Object.lolo").read_text()
    (work / "Object.lol").unlink()
    assert "(instance 1 2)" in obj and "(le (successor (parameter 0)) (parameter 1))" in obj
    (work / "Object.lolo").write_text(obj.replace("(instance 1 2)", "(instance 1 1)"))
    assert "required universe constraint: 1 < 1" in object_error()
    (work / "Object.lolo").write_text(obj.replace("(le (successor (parameter 0)) (parameter 1))",
        "(le (successor (parameter 0)) (parameter 1)) (le (parameter 1) (parameter 0))"))
    context = object_error()
    assert "[U-Context]" in context and "conflicting universe constraint: v <= u" in context, context

    with subprocess.Popen([binary, "--server"], cwd=work, stdin=subprocess.PIPE,
                          stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True) as editor:
        assert json.loads(editor.stdout.readline())["event"] == "ready"
        def ask(identity, method, **arguments):
            editor.stdin.write(json.dumps({"protocol": 2, "id": identity, "method": method, **arguments}) + "\n")
            editor.stdin.flush()
            reply = json.loads(editor.stdout.readline())
            assert reply["id"] == identity, reply
            return reply

        def state(reply):
            return {key: reply[key] for key in ("document", "revision", "incarnation", "state")}

        first = ask(1, "open", document="bad", path="Diagnostic.lol", revision=0, source=bad)
        assert first["status"] == "ok", first
        result = ask(2, "next", **state(first))["error"]
        assert result["details"] == expected and all(role in result["display"] for role in expected), result
        assert ask(3, "close", **state(first))["status"] == "ok"
        second = ask(4, "open", document="universe", path="Instance.lol", revision=0, source=scheme + "Check lt@{1 1}.")
        assert second["status"] == "ok", second
        good = ask(5, "next", **state(second))
        assert good["status"] == "ok", good
        result = ask(6, "next", **state(good))["error"]
        assert result["details"] == ["conflicting universe constraint: 1 < 1"], result
        assert ask(7, "close", **state(good))["status"] == "ok"
        checked = ask(8, "open", document="proof", path="Proof.lol", revision=0,
                      source=theorem + "\nProof.\nfirst [exact A | exact B].\nQed.")
        for identity in range(9, 12):
            checked = ask(identity, "next", **state(checked))
            assert checked["status"] == "ok", checked
        result = ask(12, "next", **state(checked))["error"]
        assert result["code"] == "E-Declared" and result["details"] == ["required universe constraint: left <= right"], result
        ask(13, "shutdown")
        assert editor.wait(timeout=6) == 0

print("V1 diagnostics: conversion roles, actual universe constraints, source-free object errors, and JSON details passed.")
