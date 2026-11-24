"""Check what the same notation means with proofs accepted by both kernels."""
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile

from rocq_reference import rocq_binary, version


binary = Path(sys.argv[1]).resolve()
rocq = rocq_binary()
version(rocq)

base = """
Inductive N : Set := | z : N | s : forall _ : N, N.
Inductive Seq : Set := | nil : Seq | cons : forall _ : N, forall _ : Seq, Seq.
Inductive Same (A : Set) (x : A) : forall _ : A, Prop := | same : Same A x x.
Definition first (a b : N) : N := a.
Definition second (a b : N) : N := b.
"""

scopes = """
Declare Scope left_scope.
Declare Scope right_scope.
Delimit Scope left_scope with L.
Delimit Scope right_scope with R.
Reserved Notation "x ⊕ y" (at level 50, left associativity).
Notation "a ⊕ b" := (first a b) : left_scope.
Infix "⊕" := second : right_scope.
Open Scope left_scope.
Definition left_ok : Same N (z ⊕ s z) z := same N z.
Open Scope right_scope.
Definition right_ok : Same N (z ⊕ s z) (s z) := same N (s z).
Definition forced : Same N (z ⊕ s z)%L z := same N z.
Definition nested : Same N ((z ⊕ s z)%L ⊕ s (s z))%R (s (s z)) := same N (s (s z)).
Delimit Scope left_scope with NewL.
Definition old_alias : Same N (z ⊕ s z) % L z := same N z.
Undelimit Scope left_scope.
Definition retained_alias : Same N (z ⊕ s z)%L z := same N z.
Close Scope right_scope.
Definition reopened : Same N (z ⊕ s z) z := same N z.
"""

lists = """
Notation "[ ]" := nil.
Notation "[ a # ; .. # ; b ]" := (cons a .. (cons b nil) ..).
Notation "[ a # ; .. # ; b & t ]" := (cons a .. (cons b t) ..).
Definition empty_ok : Same Seq [ ] nil := same Seq nil.
Definition one_ok : Same Seq [ z ] (cons z nil) := same Seq (cons z nil).
Definition three_ok : Same Seq [ z # ; s z # ; z ] (cons z (cons (s z) (cons z nil)))
    := same Seq (cons z (cons (s z) (cons z nil))).
Definition tail_ok : Same Seq [ s z # ; z & cons z nil ] (cons (s z) (cons z (cons z nil)))
    := same Seq (cons (s z) (cons z (cons z nil))).
Inductive Pair : Set := | two : forall _ : Seq, forall _ : Seq, Pair.
Notation "[ x ; .. ; y | a # .. # b ]" :=
    (two (cons x .. (cons y nil) ..) (cons a .. (cons b nil) ..)).
Definition separate : Same Pair [z; s z | s z] (two (cons z (cons (s z) nil)) (cons (s z) nil))
    := same Pair (two (cons z (cons (s z) nil)) (cons (s z) nil)).
Notation "[! x ; .. ; y !]" := (two (cons x .. (cons y nil) ..) (cons x .. (cons y nil) ..)).
Definition repeated : Same Pair [! s z !] (two (cons (s z) nil) (cons (s z) nil))
    := same Pair (two (cons (s z) nil) (cons (s z) nil)).
"""

binders = """
Definition every (p : forall _ : N, Prop) : Prop := forall n : N, p n.
Notation "'ALL' v , b" := (every (fun v => b)) (at level 89, v name, right associativity).
Definition all_ok : forall h : (forall n : N, Same N n n), ALL n, Same N n n := fun h => h.
Notation "'FORALL' x .. y , P" := (forall x, .. (forall y, P) ..)
    (at level 200, x binder, y binder, right associativity).
Definition many_ok : FORALL (x : N) (y : N), Same N x x := fun x y => same N x.
Notation "'HIDE' b" := (fun private : N => b) (at level 0).
Notation "'ANON' x , b" := (fun x : N => b) (at level 8, x as name).
Notation "'NAMED' x , b" := (fun x : N => b) (at level 8, x at level 3 as ident).
Definition anonymous_ok : Same N ((ANON _, s z) z) (s z) := same N (s z).
Definition named_ok : Same N ((NAMED (n), n) z) z := same N z.
Definition hygiene (private : N) : Same N ((HIDE private) z) private := same N private.
"""

space_lists = """
Reserved Notation "{! x .. y !}" (at level 0, x at level 0).
Notation "{! a .. b !}" := (cons a .. (cons b nil) ..).
Definition three : Same Seq {! z (s z) z !} (cons z (cons (s z) (cons z nil)))
    := same Seq (cons z (cons (s z) (cons z nil))).
Declare Custom Entry digits.
Notation "'zero'" := z (in custom digits at level 0).
Notation "'next' k" := (s k) (in custom digits at level 50).
Notation "[[ x ; .. ; y ]]" := (cons x .. (cons y nil) ..) (y custom digits at level 50).
Definition inside : Same Seq [[zero; next zero]] (cons z (cons (s z) nil))
    := same Seq (cons z (cons (s z) nil)).
"""

interpretations = """
Notation "'PREV' n" := (match n return N with | z => z | s k => k end) (at level 9).
Definition pred_ok : Same N (PREV (s (s z))) (s z) := same N (s z).
Notation "'COUNT' x" := ((fix recur (n : N) {struct n} : N :=
    match n return N with | z => z | s v => s (recur v) end) x) (at level 9).
Definition count_ok : Same N (COUNT (s z)) (s z) := same N (s z).
"""

abbreviations = """
Abbreviation swapped x y := (first y x).
Definition swap_ok : Same N (swapped z (s z)) (s z) := same N (s z).
Definition shadow (swapped : N) : Same N swapped swapped := same N swapped.
Definition λ : N := z.
Definition λ₁ : Same N λ z := same N z.
Notation succ_alias := s.
Definition alias_ok : Same N (succ_alias z) (s z) := same N (s z).
"""


where_clauses = """
Reserved Infix "≈" (at level 70, no associativity).
Inductive Related (x : N) : forall _ : N, Prop :=
    | reflect : x ≈ x
    where "x ≈ y" := (Related x y).
Definition retroactive : z ≈ z := reflect z.
Reserved Notation "'COUNTDOWN' x" (at level 9).
Fixpoint down (n : N) {struct n} : N :=
    match n return N with | z => z | s p => COUNTDOWN p end
    where "'COUNTDOWN' x" := (down x).
Definition down_ok : Same N (COUNTDOWN (s z)) z := same N z.
"""


activation = """
Declare Scope ns.
Delimit Scope ns with Nkey.
Notation "'NODE' x" := (s x) (at level 9) : ns.
Open Scope ns.
Disable Notation "'NODE' _" (only printing) : ns.
Definition node1 : Same N (NODE z) (s z) := same N (s z).
Enable Notation "'NODE' a" (only printing) : ns.
Disable Notation "'NODE' _" : ns.
Enable Notation "'NODE' v" : ns.
Definition node2 : Same N (NODE z) (s z) := same N (s z).
Abbreviation node_alias x := (s x).
Disable Notation node_alias.
Enable Notation node_alias.
Definition alias_enabled : Same N (node_alias z) (s z) := same N (s z).
Disable Notation node_alias a := (s a).
Enable Notation := (s _) (all).
Disable Notation "'NODE' v" := (s v) (only printing) : ns.
Definition filtered : Same N (NODE z) (s z) := same N (s z).
Enable Notation "'NODE' v" := (s v) (only printing) : ns.
"""

mixed_infix = """
Infix "⊙" := first (at level 54, left associativity).
Declare Scope ns.
Infix "⊙" := second : ns.
Definition fallback : Same N (z ⊙ s z) z := same N z.
Open Scope ns.
Definition scoped : Same N (z ⊙ s z) (s z) := same N (s z).
Close Scope ns.
Definition restored : Same N (z ⊙ s z) z := same N z.
Reserved Infix "chosen" (at level 45, no associativity).
Infix "chosen" := (fun a b : N => second b a).
Definition word_op : Same N (z chosen s z) z := same N z.
"""

def invoke(args, work, succeeds=True):
    process = subprocess.run(args, cwd=work, capture_output=True, text=True, timeout=20)
    assert (process.returncode == 0) == succeeds, (args, process.stdout, process.stderr)
    return process.stdout


with tempfile.TemporaryDirectory() as directory:
    work = Path(directory)
    shutil.copytree('lol', work / 'lol')
    for name, part in [('Scopes', scopes), ('Lists', lists), ('SpaceLists', space_lists), ('Binders', binders), ('Interpretations', interpretations), ('Abbreviations', abbreviations), ('WhereClause', where_clauses), ('Activation', activation), ('MixedInfix', mixed_infix)]:
        source = work / (name + '.lol')
        reference = work / (name + '.v')
        for path in (source, reference):
            path.write_text(base + part)
        invoke([rocq, 'compile', '-noinit', reference.name], work)
        obj = name + '.lolo'
        out = invoke([binary, '--explicit', '--emit-object=' + obj, source.name], work)
        invoke([binary, '--check-only', obj], work)
        source.write_text(out)
        assert invoke([binary, '--explicit', source.name], work) == out, name

    for index, bad in enumerate([
        activation + """Disable Notation "'NODE' u" (only parsing) : ns. Check NODE z.""",
        """Notation "[ a ; .. ; b ]" := (cons a nil).""",
        """Notation "[ a .. b ]" := (cons a .. (cons b nil) ..) (a at level 0, b at level 9).""",
        """Notation "[ a .. b ]" := (cons a .. (cons b nil) ..). Check [z z].""",
        binders + """Check NAMED _, z.""",
        """Notation "'BAD' x" := (s x) (at level 1, x as name).""",
        activation + """Disable Notation "'NODE' u" := (s u) : ns. Check NODE z.""",
        """Declare Scope ns. Notation "'NEXT' x" := (s x) (at level 1, x in scope ns).""",
        """Declare Scope ns. Abbreviation repeat_scope x := (s x) (x, x in scope ns).""",
    ]):
        (work / 'Rejected.v').write_text(base + bad)
        (work / 'Rejected.lol').write_text(base + bad)
        invoke([rocq, 'compile', '-noinit', 'Rejected.v'], work, False)
        invoke([binary, 'Rejected.lol'], work, False)

    display = base + lists + """
Compute two (cons z nil) (cons z nil).
Compute two (cons z nil) (cons (s z) nil).
"""
    (work / 'Display.lol').write_text(display)
    rendered = invoke([binary, 'Display.lol'], work).splitlines()
    assert len(rendered) == 2 and rendered[0] != rendered[1], rendered
    for line, other in zip(rendered, ["two (cons z nil) (cons z nil)", "two (cons z nil) (cons (s z) nil)"]):
        witness = "Definition roundtrip : Same Pair (" + line + ") (" + other + ") := same Pair (" + other + ")."
        (work / 'Display.v').write_text(base + lists + witness)
        invoke([rocq, 'compile', '-noinit', 'Display.v'], work)
    print("Rocq re-read both printed pairs, including unequal instances of a repeated range.")

    for prelude in [space_lists.split('Declare Custom Entry')[0], space_lists]:
        term = "cons z (cons (s z) nil)"
        (work / 'Display.lol').write_text(base + prelude + "Compute " + term + ".")
        line = invoke([binary, 'Display.lol'], work).strip()
        assert line.startswith(("{!", "[[")), line
        (work / 'Display.v').write_text(base + prelude + "Definition witness : Same Seq (" + line + ") (" + term + ") := same Seq (" + term + ").")
        invoke([rocq, 'compile', '-noinit', 'Display.v'], work)

    # A Greek initial and a subscript are identifiers in both the lexer and
    # object reader. Check the owning module through the normal import path.
    (work / 'λ.lol').write_text('Inductive Α : Set := | α₁ : Α.\n')
    (work / 'λ.v').write_text((work / 'λ.lol').read_text())
    invoke([rocq, 'compile', '-noinit', 'λ.v'], work)
    (work / 'Greek.lol').write_text('Import λ. Definition answer : λ.Α := λ.α₁.\n')
    invoke([binary, '--emit-object=Greek.lolo', 'Greek.lol'], work)
    invoke([binary, '--check-only', 'Greek.lolo'], work)

    client = work / 'Client.lol'
    client.write_text('Import Scopes.\nDefinition client : Same N (z ⊕ s z)%R (s z) := same N (s z).\n')
    invoke([binary, client.name], work)
    client.write_text('Import Scopes.\nUndelimit Scope right_scope.\nCheck (z ⊕ s z)%R.\n')
    invoke([binary, client.name], work, False)
print('V1 notation: scopes, reserved precedence, recursive lists, binding and round trips passed.')
