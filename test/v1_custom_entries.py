"""Cross-entry parsing, lexical isolation, imported metadata and Rocq 9.2."""
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile

from rocq_reference import rocq_binary, version


root = Path.cwd()
exe = Path(sys.argv[1]).resolve()
rocq = rocq_binary()
version(rocq)
grammar = """Axiom Item : Set.
Axiom z : Item.
Axiom other : Item.
Axiom combine : forall _ : Item, forall _ : Item, Item.
Declare Custom Entry calc.
Declare Custom Entry bit.
Notation "'calculate' ( x )" := x (at level 0, x custom calc at level 99).
Notation "'bitvalue' ( x )" := x (at level 0, x custom bit at level 99).
Notation "'atom'" := z (in custom calc at level 0).
Notation "'atom'" := other (in custom bit at level 0).
Notation "x + y" := (combine x y) (in custom calc at level 50, left associativity).
Notation "'escape' ( x )" := x (in custom calc at level 0, x constr).
Notation "'frombit' ( x )" := x (in custom calc at level 0, x custom bit).
Definition example : Item := calculate (atom + frombit (atom) + escape (combine z other)).
Definition other_value : Item := bitvalue (atom).
Inductive EqItem (x : Item) : forall _ : Item, Prop := | same : EqItem x x.
Definition grouping : EqItem example (combine (combine z other) (combine z other)) := same example.
Definition scoped : EqItem other_value other := same other_value.
"""
fallback = """Axiom Item : Set.
Axiom z : Item.
Axiom f : forall _ : Item, Item.
Declare Custom Entry calc.
Notation "'calculate' ( x )" := x (at level 0, x custom calc).
Notation "x" := x (in custom calc at level 0, x constr at level 0).
Notation "x y" := (x y) (in custom calc at level 10, left associativity).
Definition run : Item := calculate (f z).
"""


def invoke(args, accepted=True):
    result = subprocess.run(args, cwd=work, capture_output=True, text=True, timeout=15)
    assert (result.returncode == 0) == accepted, (args, result.stdout, result.stderr)
    return result.stdout + result.stderr


def compare(stem, source, accepted=True):
    for extension in ("lol", "v"):
        (work / (stem + "." + extension)).write_text(source)
    native = invoke([exe, stem + ".lol"], accepted)
    invoke([rocq, "compile", "-noinit", stem + ".v"], accepted)
    return native


with tempfile.TemporaryDirectory(prefix="lol-entries-") as tmp:
    work = Path(tmp)
    shutil.copytree(root / "lol" / "hol", work / "lol" / "hol")
    compare("Grammar", grammar)
    compare("Fallback", fallback)
    high = """Axiom N : Set. Axiom n : N. Axiom op : forall _ : N, forall _ : N, N.
Declare Custom Entry e.
Notation "'a'" := n (in custom e at level 0).
Notation "'word' x" := x (in custom e at level 300).
Notation "x +++ y" := (op x y) (in custom e at level 500, left associativity).
Notation "<{ x }>" := x (x custom e at level 500).
Check <{ word a +++ a }>.
"""
    compare("High", high)
    compare("DelimitedTolerance", high.replace("x custom e at level 500", "x custom e at level 200"))
    compare("TrailingNarrow", high.replace("<{ x }>", "'wrap' x").replace("x custom e at level 500", "at level 0, x custom e at level 200").replace("<{ word a +++ a }>", "wrap a +++ a"), False)
    for level in (201, 500, 2**62 - 1):
        top = f"""Axiom N : Set. Axiom n : N.
Notation "'word' x" := x (at level {level}).
"""
        compare("WideLevel", top)
        compare("LConstr", top + "Check word n.", False)
    compare("Overflow", top.replace(str(level), str(level + 1)), False)
    infix = 'Axiom op : forall _ : Prop, forall _ : Prop, Prop. Infix "+++" := op (at level 500, left associativity).'
    compare("WideInfix", infix)
    compare("WideInfixTop", infix + " Check Prop +++ Prop.", False)
    invoke([exe, "--emit-object=High.lolo", "High.lol"])
    invoke([exe, "--check-only", "High.lolo"])
    compare("Angles", fallback.replace("'calculate' ( x )", "<{ x }>").replace("calculate (f z)", "<{f z}>"))
    identifiers = ('Declare Custom Entry ids. Notation "<{ x }>" := x (x custom ids). '
            'Notation "x" := x (in custom ids, x ident). Axiom item : Prop.')
    compare("Identifiers", identifiers + ' Check (fun (u : Prop) => <{u}>).')
    compare("IdentGlobal", identifiers + ' Check <{item}>.', False)
    compare("GlobalName", identifiers.replace("x ident","x global") + ' Check <{item}>.')
    compare("Keyword", """Declare Custom Entry keys. Notation "'reserved' x" := x (in custom keys at level 1, x constr).
Definition reserved : Type := Set.""", False)
    compare("Missing", """Notation "'bird'" := Set (in custom absent).""", False)
    compare("UnknownArg", """Notation "'bird' ( x )" := x (at level 0, x custom absent).""", False)
    compare("Duplicate", "Declare Custom Entry bird. Declare Custom Entry bird.", False)
    local = "Local Declare Custom Entry bird. "
    compare("Leaked", local + """Notation "'blue'" := Set (in custom bird).""", False)
    compare("Local", local + """Local Notation "'blue'" := Set (in custom bird).""")
    compare("Closed", grammar + "Check calculate (other).", False)
    compare("Narrow", fallback.replace('Notation "x y"', 'Notation "x + y"'), False)

    # Explicit text retains the declarations and the entries of their holes.
    text = invoke([exe, "--explicit", "Grammar.lol"])
    (work / "Grammar.lol").write_text(text)
    invoke([exe, "Grammar.lol"])
    (work / "Grammar.lol").write_text(grammar)
    invoke([exe, "--emit-object=Grammar.lolo", "Grammar.lol"])
    # Client parses the published grammar and serializes its dependency.
    (work / "Client.lol").write_text(
        "Import Grammar.\nDefinition obj : Item := calculate (atom + frombit (atom)).\n"
        "Definition agreement : EqItem obj (combine z other) := same obj.\n")
    invoke([exe, "--emit-object=Client.lolo", "Client.lol"])
    assert "custom-entry" in (work / "Grammar.lolo").read_text()
    (work / "Grammar.lol").unlink()
    (work / "Client.lol").unlink()
    invoke([exe, "--check-only", "Client.lolo"])

    def unit(name, imports, body):
        source = "".join("Import " + other + ".\n" for other in imports) + body
        reference = "".join("Require Import " + other + ".\n" for other in imports) + body
        (work / (name + ".lol")).write_text(source)
        (work / (name + ".v")).write_text(reference)
        # Rocq installs the exact tactic in its normal initialization.
        init = [] if "Proof." in body else ["-noinit"]
        invoke([rocq, "compile", *init, "-Q", ".", "", name + ".v"])
        invoke([exe, "--emit-object=" + name + ".lolo", name + ".lol"])

    base = """Inductive Bit : Set := | leftB : Bit | rightB : Bit.
Inductive Same (x : Bit) : forall _ : Bit, Prop := | refl : Same x x.
"""
    unit("Base", [], base)
    for owner, tag, actor in [("A", "ae", "leftB"), ("B", "be", "rightB")]:
        unit(owner, ["Base"], f"""Declare Custom Entry calc.
Notation "'atom'" := {actor} (in custom calc).
Notation "'{tag}' ( x )" := x (at level 0, x custom calc).
""")

    # Import order changes the meaning of an unresolved short name. It cannot
    # change an entry already captured by an imported production.
    for name, entries, selected in [("AB", ["A", "B"], "rightB"), ("BA", ["B", "A"], "leftB")]:
        unit(name, ["Base"] + entries, f"""Notation "'takeA' ( x )" := x (at level 0, x custom A.calc).
Notation "'takeB' ( x )" := x (at level 0, x custom B.calc).
Notation "'last' ( x )" := x (at level 0, x custom calc).
Notation "'extra'" := leftB (in custom B.calc).
Definition pinnedA : Same (ae (atom)) leftB := refl leftB.
Definition pinnedB : Same (be (atom)) rightB := refl rightB.
Definition chosenA : Same (takeA (atom)) leftB := refl leftB.
Definition chosenB : Same (takeB (atom)) rightB := refl rightB.
Definition newest : Same (last (atom)) {selected} := refl {selected}.
Definition added : Same (be (extra)) leftB := refl leftB.
Theorem fromProof : Same (ae (atom)) leftB. Proof. exact (refl leftB). Qed.
""")
        expanded = invoke([exe, "--explicit", name + ".lol"])
        assert "custom A.calc" in expanded and "custom B.calc" in expanded, expanded
        (work / "Expanded.lol").write_text(expanded)
        invoke([exe, "Expanded.lol"])

    # A subsequent local declaration shadows the imported short spelling.
    # Enabling the timeline must keep the local name portable under renaming.
    unit("Hiding", ["Base", "A"], """Declare Custom Entry calc.
Notation "'atom'" := rightB (in custom calc).
Notation "'own' ( x )" := x (at level 0, x custom calc).
Declare Scope display_scope.
Bind Scope display_scope with Sortclass.
Definition ownValue : Same (own (atom)) rightB := refl rightB.
Definition importedValue : Same (ae (atom)) leftB := refl leftB.
""")
    hiding = invoke([exe, "--explicit", "Hiding.lol"])
    assert "Hiding.calc" not in hiding, hiding
    (work / "Renamed.lol").write_text(hiding)
    invoke([exe, "Renamed.lol"])

    double = (work / "AB.lolo").read_text()
    assert '(argument-entry "A.calc"' in double
    (work / "Ambiguous.lolo").write_text(double.replace('(argument-entry "A.calc"', '(argument-entry "calc"'))
    reason = invoke([exe, "--check-only", "Ambiguous.lolo"], False)
    assert "Ambiguous legacy custom entry" in reason, reason

    # Requiring a dependency makes its qualified entry name available; its
    # productions enter the client grammar only through an explicit import.
    unit("Wrapper", ["A"], """Notation "'fresh'" := Prop (in custom A.calc).
Notation "'exported' ( x )" := x (at level 0, x custom A.calc).
""")
    unit("Indirect", ["Wrapper"], """Notation "'reach' ( x )" := x (at level 0, x custom A.calc).
Notation "'short' ( x )" := x (at level 0, x custom calc).
Check reach (fresh). Check short (fresh). Check exported (fresh).
""")
    for ext, imports in [("v", "Require Import"), ("lol", "Import")]:
        (work / ("Leaked." + ext)).write_text(imports + " Wrapper. Check exported (atom).")
    invoke([rocq, "compile", "-noinit", "-Q", ".", "", "Leaked.v"], False)
    invoke([exe, "Leaked.lol"], False)

    # Older custom-entry wires contained only the spelling local to the owner.
    # Foreign declarations and foreign references without imports are rejected.
    wire = (work / "A.lolo").read_text()
    assert '(custom-entry "A.calc")' in wire and '(argument-entry "A.calc"' in wire, wire
    (work / "Legacy.lolo").write_text(wire.replace('"A.calc"', '"calc"'))
    invoke([exe, "--check-only", "Legacy.lolo"])
    for tag in ["custom-entry", "argument-entry"]:
        (work / "WrongOwner.lolo").write_text(wire.replace(f'({tag} "A.calc"', f'({tag} "B.calc"'))
        invoke([exe, "--check-only", "WrongOwner.lolo"], False)

    for name in ["Base", "A", "B", "AB", "BA", "Wrapper", "Indirect"]:
        (work / (name + ".lol")).unlink()
    for name in ["AB", "BA", "Indirect"]:
        invoke([exe, "--check-only", name + ".lolo"])

print("V1 custom entries: Rocq comparisons, qualified ownership, old wire, explicit replay and source-free object checking passed.")
