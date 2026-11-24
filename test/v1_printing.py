"""Compare normal displays with Rocq and keep canonical outputs re-readable."""
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tempfile

from rocq_reference import require_release, rocq_binary


root = Path.cwd()
exe = Path(sys.argv[1]).resolve()
rocq = rocq_binary()


def invoke(args, directory):
    result = subprocess.run(args, cwd=directory, timeout=25, capture_output=True, text=True)
    assert result.returncode == 0, (args, result.stdout, result.stderr)
    return result.stdout


universe = """Inductive N : Set := | z : N | s : forall _ : N, N.
Axiom leftOp : forall _ : N, forall _ : N, N.
Axiom rightOp : forall _ : N, forall _ : N, N.
Declare Scope alpha_scope.
Declare Scope beta_scope.
Delimit Scope alpha_scope with AA.
Delimit Scope beta_scope with BB.
Infix "⊕" := leftOp (at level 50, left associativity) : alpha_scope.
Infix "⊕" := rightOp (at level 50, left associativity) : beta_scope.
"""

with tempfile.TemporaryDirectory() as scratch:
    wd = Path(scratch)
    shutil.copytree(root / 'lol', wd / 'lol')
    source = wd / 'Printing.lol'
    reference = wd / 'Printing.v'
    require_release(invoke([rocq, '--print-version'], wd))

    def run(value, *options):
        source.write_text(value)
        return invoke([exe, *options, source.name], wd)

    # LoL Compute displays its result, so use Rocq Check on the same opaque
    # terms to read only the expression and ignore the independently shown type.
    compare = [('Open Scope alpha_scope.', 'leftOp z z', 'z ⊕ z'),
               ('Open Scope beta_scope.', 'rightOp z z', 'z ⊕ z'),
               ('', 'leftOp z z', '(z ⊕ z)%AA'),
               ('Close Scope beta_scope.', 'leftOp z z', 'z ⊕ z')]
    lol = roc = universe
    for action, term, expected in compare:
        lol += f'{action}\nCompute {term}.\n'
        roc += f'{action}\nCheck ({term}).\n'
    shown = run(lol).splitlines()
    assert shown == [c[2] for c in compare], shown
    reference.write_text(roc)
    roc_shown = invoke([rocq, 'compile', '-noinit', reference.name], wd)
    for name in set(line for _, _, line in compare):
        assert name in roc_shown, roc_shown

    # The printed document is standalone in both machine-readable modes.
    declarations = universe + 'Open Scope alpha_scope.\nDefinition twice : N := leftOp z z.\n'
    assert 'z ⊕ z' in run(declarations + 'Print twice.\n')
    explicit = run(declarations, '--explicit')
    assert 'leftOp z z' in explicit, explicit
    run(explicit)
    canonical = run(declarations, '--rocq')
    reference.write_text(canonical)
    invoke([rocq, 'compile', '-noinit', reference.name], wd)

    aliases = '''Inductive N : Set := | z : N.
Notation "'parseZ'" := z (only parsing).
Compute parseZ.
Notation "'displayZ'" := z (only printing).
Compute z.
'''
    assert run(aliases).splitlines() == ['z', 'displayZ']

    lists = '''Inductive N : Set := | z : N.
Inductive Seq : Set := | nil : Seq | cons : forall _ : N, forall _ : Seq, Seq.
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).
'''
    for operand, spelling in [('nil', '[ ]'), ('cons z nil', '[z]'),
                              ('cons z (cons z (cons z nil))', '[z; z; z]')]:
        assert run(lists + f'Compute ({operand}).\n').strip() == spelling
        assert run(lists + f'Compute {spelling}.\n').strip() == spelling
        reference.write_text(lists + f'Check ({operand}).\n')
        external = invoke([rocq, 'compile', '-noinit', reference.name], wd)
        assert spelling in external, external

    binders = '''Inductive N : Set := | z : N.
Axiom allN : forall _ : (forall _ : N, Prop), Prop.
Axiom pred : forall _ : N, Prop.
Notation "'ALL' v , b" := (allN (fun v => b)) (at level 89, v name, right associativity).
'''
    body = 'allN (fun x : N => pred x)'
    written = run(binders + f'Compute ({body}).\n').strip()
    assert re.fullmatch(r'ALL (\w+), \(?pred \1\)?', written), written
    assert run(binders + f'Compute ({written}).\n').strip() == written
    reference.write_text(binders + f'Check ({body}).\n')
    assert 'ALL x, pred x' in invoke([rocq, 'compile', '-noinit', reference.name], wd)

    orientations = lists.split('Notation')[0] + '''Axiom snoc : forall _ : Seq, forall _ : N, Seq.
Axiom wrap : forall _ : Seq, Seq.
'''
    for rhs, expression in [('snoc .. (snoc nil x) .. y', 'snoc (snoc (snoc nil z) z) z'),
                            ('wrap (cons x .. (cons y nil) ..)', 'wrap (cons z (cons z (cons z nil)))')]:
        prefix = orientations + f'Notation "<< x ; .. ; y >>" := ({rhs}).\n'
        native = run(prefix + f'Compute ({expression}).\n').strip()
        assert native == '<< z; z; z >>', native
        assert run(prefix + f'Compute {native}.\n').strip() == native
        reference.write_text(prefix + f'Check ({expression}).\n')
        assert native in invoke([rocq, 'compile', '-noinit', reference.name], wd)

    typed = '''Inductive N : Set := | z : N.
Axiom allN : forall _ : (forall _ : N, Prop), Prop.
Axiom rel : forall _ : N, forall _ : N, Prop.
Notation "'Q' x .. y , p" := (allN (fun x => .. (allN (fun y => p)) ..)) (at level 200, x binder, y binder, right associativity).
'''
    nested = 'allN (fun a : N => allN (fun b : N => rel a b))'
    written = run(typed + f'Compute ({nested}).\n').strip()
    assert re.fullmatch(r'Q \((\w+) : N\) \((\w+) : N\), rel \1 \2', written), written
    assert run(typed + f'Compute {written}.\n').strip() == written
    reference.write_text(typed + f'Check ({nested}).\n')
    assert 'Q a b : N, rel a b' in invoke([rocq, 'compile', '-noinit', reference.name], wd)

    custom = '''Inductive N : Set := | z : N.
Declare Custom Entry small.
Notation "<{ e }>" := e (e custom small at level 99).
Notation "'smallz'" := z (in custom small at level 0).
'''
    written = run(custom + 'Compute z.\n').strip()
    assert written == '<{ smallz }>', written
    assert run(custom + f'Compute {written}.\n').strip() == written
    reference.write_text(custom + 'Check z.\n')
    assert written in invoke([rocq, 'compile', '-noinit', reference.name], wd)
    groups = custom + '''Axiom op : forall _ : N, forall _ : N, N.
Notation "x + y" := (op x y) (in custom small at level 50, left associativity).
Notation "( x )" := x (in custom small at level 0, x at level 99).
'''
    shaped = run(groups + 'Compute (op z (op z z)).\n').strip()
    assert shaped == '<{ smallz + (smallz + smallz) }>', shaped
    assert run(groups + f'Compute {shaped}.\n').strip() == shaped
    reference.write_text(groups + 'Check (op z (op z z)).\n')
    assert shaped in invoke([rocq, 'compile', '-noinit', reference.name], wd)

    patterns = '''Inductive N : Set := | z : N | s : forall _ : N, N.
Notation "'ZZ'" := z.
Notation "'SUCC' x" := (s x) (at level 10).
Definition previous (v : N) : N := match v return N with | ZZ => z | SUCC x => x end.
'''
    assert run(patterns + 'Compute (previous (s (s z))).\n').strip() == 'SUCC ZZ'
    reference.write_text(patterns + 'Check (previous (s (s z))).\n')
    invoke([rocq, 'compile', '-noinit', reference.name], wd)
    pending = run(patterns + 'Compute (fun v : N => previous v).\n').strip()
    assert '| ZZ =>' in pending and '| SUCC ' in pending, pending
    assert run(patterns + f'Compute ({pending}).\n').strip() == pending

    # The exported syntax fixes its constructor in the defining module.
    # Neither indirect imports nor a caller's local named z retarget it.
    (wd / 'PrivateN.lol').write_text(patterns.split('Notation')[0])
    (wd / 'PublicPattern.lol').write_text('''Import PrivateN.
Definition Item : Set := PrivateN.N.
Definition base : Item := PrivateN.z.
Notation "'ZeroPat'" := PrivateN.z.
Notation "'StepPat' x" := (PrivateN.s x) (at level 10, x ident, only parsing).
''')
    imported = '''Import PublicPattern.
Definition pred (z : PublicPattern.Item) : PublicPattern.Item :=
    match z return PublicPattern.Item with | ZeroPat => PublicPattern.base | StepPat t => t end.
Compute (pred PublicPattern.base).
'''
    assert run(imported).strip() == 'ZeroPat'

    scoped = universe + '''Axiom takeN : forall x : N, N.
Open Scope beta_scope.
Arguments takeN x%AA.
'''
    for expr, display in [('takeN (leftOp z z)', 'takeN (z ⊕ z)'),
                          ('takeN (rightOp z z)', 'takeN ((z ⊕ z)%BB)')]:
        native = run(scoped + f'Compute ({expr}).\n').strip()
        # A delimiter binds to a parenthesized expression and may itself
        # stand as an atomic Gallina argument.
        assert native in (display, display.replace('((z ⊕ z)%BB)', '(z ⊕ z)%BB')), native
        assert run(scoped + f'Compute ({native}).\n').strip() == native
        reference.write_text(scoped + f'Check ({expr}).\n')
        external = invoke([rocq, 'compile', '-noinit', reference.name], wd)
        assert ('%BB' in native) == ('%BB' in external), external

    case_syntax = '''Inductive N : Set := | z : N | s : forall _ : N, N.
Notation "'observe' x 'zeroes' a 'later' v 'gives' b" :=
  (match x with | z => a | s v => b end)
  (at level 50, v name).
'''
    case_term = 'fun n : N => match n return N with | z => z | s k => k end'
    shown = run(case_syntax + f'Compute ({case_term}).\n').strip()
    assert 'observe ' in shown and ' later ' in shown and ' gives ' in shown, shown
    assert run(case_syntax + f'Compute ({shown}).\n').strip() == shown
    reference.write_text(case_syntax + f'Check ({case_term}).\n')
    assert 'observe ' in invoke([rocq, 'compile', '-noinit', reference.name], wd)

    fix = 'fix h (n : N) {struct n} : N := n'
    definitions = patterns.split('Notation')[0] + f'Notation FixId := ({fix}).\n'
    shown = run(definitions + f'Compute ({fix}).\n').strip()
    assert shown == 'FixId', shown
    assert run(definitions + f'Compute {shown}.\n').strip() == shown
    reference.write_text(definitions + f'Check ({fix}).\n')
    assert 'FixId' in invoke([rocq, 'compile', '-noinit', reference.name], wd)

print('V1 notation printing: scopes, exports, recursive terms and binders, custom entries and constructor patterns passed.')
