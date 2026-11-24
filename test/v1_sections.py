"""Discharge section assumptions through proofs, imports, objects and undo."""
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile

from rocq_reference import require_release, rocq_binary


root = Path(__file__).resolve().parents[1]
binary = str(Path(sys.argv[1]).resolve())


def run(work, *args, source=None, accepted=True):
    proc = subprocess.run(args, cwd=work, input=source, text=True,
                          capture_output=True, timeout=25)
    if (proc.returncode == 0) != accepted:
        raise AssertionError((args, proc.stdout, proc.stderr))
    return proc.stdout + proc.stderr


fixture = """Section Outer.
Context (P : Prop) (Discarded_section_type : Set) (p : P).
Theorem captured : P.
Proof. assumption. Qed.
Theorem through_proof : P := captured.
Theorem independent : forall X : Prop, X -> X :=
    fun (X : Prop) (x : X) => x.
Section Inner.
Variables Q : Prop.
Hypothesis q : Q.
Definition take (f : P -> Q -> P) : P := f p q.
End Inner.
Definition witness : P := through_proof.
End Outer.
"""

checks = """Definition check_proof : forall (P : Prop), P -> P := @captured.
Definition check_steps : forall (P : Prop), P -> P := @witness.
Definition check_unused : forall X : Prop, X -> X := @independent.
Definition check_nested : forall (P : Prop) (p : P) (Q : Prop),
    Q -> (P -> Q -> P) -> P := @take.
Print Assumptions through_proof.
"""

inductives = """Section Data.
Context {A : Set}.
Inductive chain : Set := | done : chain | link : A -> chain -> chain.
Fixpoint count (n : chain) {struct n} : chain :=
    match n with
    | done => done
    | link x tail => count tail
    end.
#[projections(primitive)] Record pair : Set :=
    pack { fst : A ; snd : A }.
Definition first (r : pair) : A := r.(fst).
End Data.
Definition check_family : forall A : Set, Set := @chain.
Definition check_count : forall A : Set, @chain A -> @chain A := @count.
Definition check_field : forall A : Set, @pair A -> A := @first.
"""


def library_equivalence(work, lol):
    theories = work / "lol/theories"
    theories.mkdir()
    for name in ["Logic", "Nat", "Bool", "List"]:
        shutil.copy(root / "lol/theories" / (name + ".lol"), theories)
    original = (root / "lol/theories/ListRelations.lol").read_text()
    header = original[:original.index("Fixpoint Exists")]
    baseline = original[original.index("Theorem Forall_head"):original.index("Theorem Forall_impl")]
    sectioned = """Section Universal_list.
Context (A : Set) (P : A -> Prop).
Theorem Forall_head : forall (x : A) (l : list A), Forall P (cons x l) -> P x :=
    fun x l h => and_left (P x) (Forall P l) h.
Theorem Forall_tail : forall (x : A) (l : list A), Forall P (cons x l) -> Forall P l :=
    fun x l h => and_right (P x) (Forall P l) h.
End Universal_list.
"""
    path = work / "ListExample.lol"
    path.write_text(header + baseline)
    expected = run(work, *lol, "--explicit", path.name)
    path.write_text(header + sectioned)
    actual = run(work, *lol, "--explicit", path.name)
    assert actual == expected, (actual, expected)


def locality(work, lol, rocq):
    scoped = """Declare Scope sample_scope.
Notation "'Scoped_token'" := Prop : sample_scope.
"""
    cases = [
        ("Section S. Variable A : Set. Notation \"'local_type'\" := A. Definition copy : Set := local_type. End S. Check copy.", True),
        ("Section S. Notation \"'local_type'\" := Set. End S. Check local_type.", False),
        ("Section S. Global Notation \"'keyword'\" := Set. End S.", False),
        ("Section S. #[global] Declare Scope sample_scope. End S.", False),
        (scoped + "Section S. Global Delimit Scope sample_scope with sample. End S.", False),
        (scoped + "Section S. Open Scope sample_scope. End S. Check Scoped_token.", False),
        (scoped + "Section S. Section T. #[global] Open Scope sample_scope. End T. End S. Check Scoped_token.", True),
        (scoped + "Open Scope sample_scope. Section S. Global Close Scope sample_scope. End S. Check Scoped_token.", False),
        ("Section S. Declare Scope sample_scope. Global Open Scope sample_scope. End S. " + scoped + "Check Scoped_token.", True),
        ("#[export] Notation \"'keyword'\" := Set.", False),
    ]
    for source, valid in cases:
        (work / "LocalRules.lol").write_text(source)
        (work / "LocalRules.v").write_text(source)
        run(work, rocq, "compile", "-noinit", "LocalRules.v", accepted=valid)
        run(work, *lol, "LocalRules.lol", accepted=valid)
    library = """Definition mat : Type@{1} := Set.
Notation "'exported_mat'" := mat.
"""
    # Only declarations actually loaded in this module have qualified names.
    (work / "Opened.lol").write_text(library)
    use = "Section S. Import Opened. Check exported_mat. End S. "
    (work / "Consumer.lol").write_text(use + "Check Opened.mat. Import Opened. Check exported_mat.")
    run(work, *lol, "--emit-object=Consumer.lolo", "Consumer.lol")
    run(work, *lol, "--check-only", "Consumer.lolo")
    for short in ["mat", "exported_mat"]:
        (work / "Consumer.lol").write_text(use + "Check " + short + ".")
        run(work, *lol, "Consumer.lol", accepted=False)

with tempfile.TemporaryDirectory(prefix="lol-v1-section-") as tmp:
    work = Path(tmp)
    shutil.copytree(root / "lol/hol", work / "lol/hol")
    (work / "Facts.lol").write_text(fixture + checks + inductives)
    lol = [binary]
    output = run(work, *lol, "Facts.lol")
    assert "(* No assumptions. *)" in output, output
    explicit = run(work, *lol, "--explicit", "Facts.lol")
    assert "Discarded_section_type" not in explicit and "Axiom " not in explicit, explicit
    (work / "Expanded.lol").write_text(explicit)
    run(work, *lol, "Expanded.lol")
    reference = rocq_binary()
    require_release(run(work, reference, "--print-version"))
    (work / "Facts.v").write_text(run(work, *lol, "--rocq", "Facts.lol"))
    run(work, reference, "compile", "-noinit", "Facts.v")
    # Captured declarations need their actual dependencies, even if the
    # source imported them in the middle of the section.
    (work / "Client.lol").write_text("""Section Client.
Context (P : Prop) (p : P).
Import Facts.
Definition imported : P := @through_proof P p.
End Client.
Print Assumptions imported.
""")
    run(work, *lol, "--emit-object=Client.lolo", "Client.lol")
    (work / "Facts.lol").unlink()
    (work / "Client.lol").unlink()
    run(work, *lol, "--check-only", "Client.lolo")

    undo = """Section S.
Context (P : Prop) (p : P).
Definition get : P := p.
End S.
Undo.
Check p.
End S.
Check p.
Check get.
:quit
"""
    transcript = run(work, *lol, "--interactive", source=undo)
    assert "The previous document state was restored." in transcript, transcript
    assert transcript.count("unknown name: p") == 1, transcript
    for bad in ["End Missing.", "Section A. End B.", "Context (P : Prop).",
                "Section A. Context (P : Prop) (P : Prop). End A.",
                "Section Open.", "Section S. Variable x : Missing. End S."]:
        path = work / "Bad.lol"
        path.write_text(bad)
        run(work, *lol, str(path), accepted=False)
    library_equivalence(work, lol)
    locality(work, lol, reference)
    print("PASS Section/Context: dependencies, nested discharge, inductives, projections, proofs, undo, object and Rocq replay")
