"""Compare argument scopes at use sites, including reference identity across modules."""
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile

from rocq_reference import require_release, rocq_binary


root = Path(__file__).resolve().parents[1]
binary = str(Path(sys.argv[1]).resolve())
rocq = rocq_binary()


def run(work, args, accept=True, case=""):
    process = subprocess.run(args, cwd=work, text=True, capture_output=True, timeout=22)
    if (process.returncode == 0) != accept:
        raise AssertionError((case, args, process.stdout, process.stderr))
    return process.stdout


header = """Inductive N : Set := | n : N.
Inductive B : Set := | b : B.
Declare Scope ns.
Declare Scope bs.
Delimit Scope ns with nk.
Delimit Scope bs with bk.
Notation "'token'" := n : ns.
Notation "'token'" := b : bs.
Axiom choose : forall x : N, N.
Axiom binary : forall x y : N, N.
Axiom other : forall x : B, B.
"""
cases = [
    ("bind", "Bind Scope ns with N. Check choose token.", True),
    ("opposite-global", "Open Scope bs. Bind Scope ns with N. Check choose token.", True),
    ("last-binding", "Bind Scope ns with N. Bind Scope bs with N. Check choose token.", False),
    ("add-top", "Bind Scope ns with N. #[add_top] Bind Scope bs with N. Check choose token.", False),
    ("add-bottom", "Bind Scope ns with N. #[add_bottom] Bind Scope bs with N. Check choose token.", True),
    ("manual", "Arguments choose x%nk. Check choose token.", True),
    ("multiple", "Arguments choose x%_ns%_bs. Check choose token.", True),
    ("manual-clear", "Bind Scope ns with N. Arguments choose : clear scopes. Check choose token.", False),
    ("manual-replaces-auto", "Bind Scope ns with N. Arguments binary x y%_ns. Check binary token n.", False),
    ("parentheses", "Arguments binary (x y)%nk. Check binary (token) token.", True),
    ("group-inner", "Arguments binary (x%_ns y)%_bs. Check binary token n.", True),
    ("shallow", "Arguments choose x%nk. Check choose (binary token n).", False),
    ("bounded", "Check (binary token n)%_nk.", False),
    ("unbounded", "Check (binary token n)%nk.", True),
    ("shadow", "Bind Scope ns with N. Check (fun (choose : forall x : N, N) => choose token).", False),
    ("alias", "Bind Scope ns with N. Definition Alias : Set := N. Axiom af : forall x : Alias, Alias. Check af token.", False),
    ("zeta", "Bind Scope ns with N. Axiom zf : forall x : (let t := N in t), N. Check zf token.", True),
    ("definition", "Bind Scope ns with N. Definition picked : N := token.", True),
    ("cast", "Bind Scope ns with N. Check (token : N).", True),
    ("sort-class", """Declare Scope sorts. Notation "'T'" := N : sorts.
Bind Scope sorts with Sortclass. Axiom select : forall A : Set, A. Check select T.""", True),
    ("function-class", """Declare Scope funcs. Notation "'F'" := choose : funcs.
Bind Scope funcs with Funclass. Axiom use : forall f : (forall x : N, N), N. Check use F.""", True),
    ("constructor", "Bind Scope ns with n.", False),
    ("notation-operand", """Bind Scope ns with N.
Notation "'pick' x" := (choose x) (at level 30).
Check pick token.""", True),
    ("captured-before-bind", """Notation "'pick' x" := (choose x) (at level 30).
Bind Scope ns with N. Check pick token.""", False),
    ("captured-before-clear", """Bind Scope ns with N.
Notation "'pick' x" := (choose x) (at level 30).
Arguments choose : clear scopes. Check pick token.""", True),
    ("extra-scopes", """Axiom select : forall A : Set, A.
Arguments select A _%nk : extra scopes. Check select (forall _ : N, N) token.""", True),
    ("missing-extra", """Axiom select : forall A : Set, A.
Arguments select A _%nk _ : extra scopes.""", False),
    ("anonymous-slot", "Arguments choose _%nk. Check choose token.", True),
    ("theorem", "Bind Scope ns with N. Theorem works : N. Proof. exact (choose token). Qed.", True),
    ("implicit", """Definition ident {A : Set} (x : A) : A := x.
Arguments ident {A} x%nk. Check ident token. Check @ident N token.""", True),
]

observing = """Notation "'onlyn'" := n : ns. Bind Scope ns with N.
"""
after = " Bind Scope bs with N. Check choose onlyn."
for label, command, accepted in [
    ("unseen", "", False),
    ("used", "Check choose n.", True),
    ("bare", "Check choose.", True),
    ("explicit-bare", "Check @choose.", False),
    ("explicit-applied", "Check @choose n.", True),
    ("printed", "Print choose.", True),
    ("assumptions", "Print Assumptions choose.", False),
    ("definition-lookup", "Definition selected : forall _ : N, N := choose.", True),
    ("shadowed-lookup", "Check (fun (choose : N) => choose).", False),
    ("proof-query", "Theorem localProof : N. Proof. Check choose n. exact n. Qed.", False),
    ("proof-term", "Theorem localProof : N. Proof. exact (choose n). Qed.", False),
    ("proof-header", """Axiom K : forall x : N, Prop. Axiom fact : forall x : N, K x.
Theorem z : K (choose n). Proof. exact (fact (choose n)). Qed.""", True),
    ("section-lookup", "Section S. Check choose n. End S.", False),
]:
    cases.append((label, observing + command + after, accepted))

with tempfile.TemporaryDirectory(prefix="argument-scopes-") as tmp:
    work = Path(tmp)
    shutil.copytree(root / "lol/hol", work / "lol/hol")
    require_release(run(work, [rocq, "--print-version"]))
    for label, suffix, accept in cases:
        source = header + suffix
        (work / "Shapes.lol").write_text(source)
        (work / "Shapes.v").write_text(source)
        run(work, [rocq, "compile", *([] if "Proof." in source else ["-noinit"]), "Shapes.v"], accept, label)
        run(work, [binary, "Shapes.lol"], accept, label)

    policy = "Bind Scope ns with N. Arguments other x%bk."
    (work / "Shapes.lol").write_text(header + policy)
    (work / "Use.lol").write_text("Import Shapes. Check choose token. Check other token.")
    run(work, [binary, "Use.lol"])
    run(work, [binary, "--emit-object=Use.lolo", "Use.lol"])
    printed = run(work, [binary, "--explicit", "Shapes.lol"])
    (work / "Shapes.lol").write_text(printed)
    run(work, [binary, "Use.lol"])
    (work / "Shapes.lol").unlink()
    (work / "Use.lol").unlink()
    run(work, [binary, "--check-only", "Use.lolo"])
    chronology = header + """
Axiom secret : forall x : N, N.
Local Arguments secret x%_ns.
Arguments secret : simpl never.
Notation "'pre' x" := (choose x) (at level 30).
Local Bind Scope ns with N.
Axiom late : forall x : N, N.
Notation "'auto' x" := (choose x) (at level 30).
Arguments choose : clear scopes.
Notation "'cleared' x" := (choose x) (at level 30).
Arguments other x%bk.
Abbreviation named x := (other x) (x in scope bs).
"""
    clients = [
        ("private-argument", "Check secret token.", False),
        ("prior-declaration", "Check choose token.", False),
        ("later-declaration", "Check late token.", True),
        ("priority-top", "#[add_top] Bind Scope bs with N. Check late token.", False),
        ("priority-bottom", "#[add_bottom] Bind Scope bs with N. Check late token.", True),
        ("prior-notation", "Check pre token.", False),
        ("bound-notation", "Check auto token.", True),
        ("cleared-notation", "Check cleared token.", False),
        ("scoped-abbreviation", "Check named token.", True),
    ]
    (work / "Shape.v").write_text(chronology)
    run(work, [rocq, "compile", "-noinit", "-Q", str(work), "", "Shape.v"], case="scope library")
    for label, body, accept in clients:
        (work / "Client.v").write_text("Require Import Shape. " + body)
        run(work, [rocq, "compile", "-noinit", "-Q", str(work), "", "Client.v"], accept, label)

    (work / "Shape.lol").write_text(chronology)
    run(work, [binary, "--emit-object=Shape.lolo", "Shape.lol"])
    for form in ("source", "explicit-source"):
        if form != "source":
            source = "Shape.lol"
            explicit = run(work, [binary, "--explicit", source], case=form)
            (work / "Shape.lol").write_text(explicit)
        for label, body, accept in clients:
            (work / "Client.lol").write_text("Import Shape. " + body)
            run(work, [binary, "Client.lol"], accept, form + " " + label)
    (work / "Shape.lol").unlink()
    run(work, [binary, "--check-only", "Shape.lolo"], case="scheduled grammar from source-free object")
    mixture = header + """Bind Scope ns with N.
Axiom K : forall _ : N, Set.
Axiom supply : forall s : N, K s.
Section S.
Context (s : N).
Axiom mixed : forall x : N, K s.
Definition mixedDef (x : N) : K s := supply s.
Theorem mixedThm (x : N) : K s. Proof. exact (supply s). Qed.
Inductive Family (x : N) : Set :=
| pack : forall _ : K s, Family x
| more : forall _ : Family x, Family x.
Axiom reset : forall x : N, K s.
Arguments reset x%_ns.
Global Arguments mixed x%_ns.
Global Arguments mixedDef x%_ns.
Global Arguments mixedThm x%_ns.
Global Arguments Family x%_ns.
End S.
"""
    mixed_clients = [
        ("both", "Check mixed token token. Check mixedDef token token. Check mixedThm token token. Check Family token token.", True),
        ("changed-manual", "#[add_top] Bind Scope bs with N. Check mixed n token.", True),
        ("default-local", "#[add_top] Bind Scope bs with N. Check reset n token.", False),
        ("changed-automatic", "#[add_top] Bind Scope bs with N. Check mixed token n.", False),
    ]
    (work / "Mixed.v").write_text(mixture)
    run(work, [rocq, "compile", "-Q", str(work), "", "Mixed.v"], case="mixed section scopes")
    for label, body, accept in mixed_clients:
        (work / "Client.v").write_text("Require Import Mixed. " + body)
        run(work, [rocq, "compile", "-Q", str(work), "", "Client.v"], accept, label)
    (work / "Mixed.lol").write_text(mixture)
    for form in ("source", "explicit"):
        if form == "explicit":
            printed = run(work, [binary, "--explicit", "Mixed.lol"])
            (work / "Mixed.lol").write_text(printed)
        for label, body, accept in mixed_clients:
            (work / "Client.lol").write_text("Import Mixed. " + body)
            run(work, [binary, "Client.lol"], accept, form + " " + label)
        run(work, [binary, "--emit-object=Mixed.lolo", "Mixed.lol"])
        run(work, [binary, "--check-only", "Mixed.lolo"])
    cachelib = header + observing + """Check choose n.
Bind Scope bs with N.
Notation "'held' x" := (choose x) (at level 40).
"""
    (work / "Memo.v").write_text(cachelib)
    run(work, [rocq, "compile", "-noinit", "-Q", str(work), "", "Memo.v"])
    (work / "Memo.lol").write_text(cachelib)
    for check, accepted in [("Check held onlyn.", True), ("Check choose onlyn.", False)]:
        (work / "Client.v").write_text("Require Import Memo. " + check)
        run(work, [rocq, "compile", "-noinit", "-Q", str(work), "", "Client.v"], accepted, check)
    for form in ("source", "explicit"):
        if form == "explicit":
            printed = run(work, [binary, "--explicit", "Memo.lol"])
            assert "Print choose." in printed, printed
            (work / "Memo.lol").write_text(printed)
        for check, accepted in [("Check held onlyn.", True), ("Check choose onlyn.", False)]:
            (work / "Client.lol").write_text("Import Memo. " + check)
            run(work, [binary, "Client.lol"], accepted, form + " " + check)
        run(work, [binary, "--emit-object=Memo.lolo", "Memo.lol"])
        run(work, [binary, "--check-only", "Memo.lolo"])

    exported = run(work, [binary, "--rocq", "Memo.lol"])
    (work / "Memo_export.v").write_text(exported)
    run(work, [rocq, "compile", "-noinit", "Memo_export.v"], case="observations erase from checked Rocq export")

    for label, probe in [
        ("undone", "Check choose n.\nUndo."),
        ("failed", "Check choose b."),
        ("search", "Search choose."),
    ]:
        script = header + observing.replace(". Bind", ".\nBind") + probe + "\nBind Scope bs with N.\nCheck choose onlyn.\n:quit\n"
        reply = subprocess.run([binary, "--interactive"], cwd=work, input=script,
                               timeout=12, capture_output=True, text=True)
        assert reply.returncode == 0 and "No interpretation" in reply.stdout, (label, reply.stdout, reply.stderr)
        assert reply.stdout.count("error:") == (2 if label == "failed" else 1), reply.stdout
        if label == "failed":
            assert "[LoL-KernelError]" in reply.stdout, reply.stdout
        if label == "undone":
            assert "The previous document state was restored." in reply.stdout, reply.stdout
    print("PASS argument scopes: {} single files, {} ordinary and {} discharged Rocq clients, source, explicit text and checked objects".format(len(cases), len(clients), len(mixed_clients)))
