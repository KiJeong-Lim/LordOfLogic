"""Compare notation format directives and object replay with Rocq's printer."""
import re
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

from rocq_reference import rocq_binary, version


exe = Path(sys.argv[1]).resolve()
rocq = rocq_binary()
version(rocq)
root = Path.cwd()
base = """Axiom A : Set.
Axiom p : forall _ : A, forall _ : A, A.
Axiom a : A.
"""


def invoke(args, accepted=True):
    cmd = subprocess.run(args, cwd=work, text=True, capture_output=True, timeout=12)
    assert (cmd.returncode == 0) == accepted, (args, cmd.stdout, cmd.stderr)
    return cmd.stdout


def check(declarations, term, expected=None):
    (work / 'Formats.v').write_text(declarations + '\nCheck (' + term + ').\n')
    (work / 'Formats.lol').write_text(declarations + '\nCompute (' + term + ').\n')
    reference = invoke([rocq, 'compile', '-noinit', 'Formats.v'])
    native = invoke([exe, 'Formats.lol']).rstrip('\n')
    result = re.sub(r'\n\s*: A\s*$', '', reference)
    assert native == result, (native, result)
    if expected is not None:
        assert native == expected, native
    return native


def notation(fmt):
    return base + f"""Notation "'op' ( x , y )" := (p x y) (at level 0, format "{fmt}")."""


with tempfile.TemporaryDirectory(prefix='lol-v1-format-') as folder:
    work = Path(folder)
    shutil.copytree(root / 'lol/hol', work / 'lol/hol')
    for fmt, expected in [
        ("'op' ( x , y )", "op(a,a)"),
        ("'op' (  x ,  y  )", "op( a, a )"),
        ("'[' 'op' ( x ,  '/' y ) ']'", "op(a, a)"),
        ("'[hv ' 'op' ( x ,  '/' y ) ']'", "op(a, a)"),
        ("'[v  ' 'op' ( x , '/' y ) ']'", "op(a,\n  a)"),
        ("'[' 'op' ( x , '//' y ) ']'", "op(a,\na)"),
    ]:
        check(notation(fmt), "p a a", expected)
    for pattern, expected in [
        ("'op' (  x , y  )", "op ( a, a )"),
        ("'op'   ( x , y )", "op  (a, a)"),
        ("[  x ;  y  ]", "[ a; a ]"),
        ("'K'  x  'with'  y", "K a with a"),
    ]:
        check(base + f'Notation "{pattern}" := (p x y) (at level 10).', "p a a", expected)
    check(base + """Notation "'key'" := a (only parsing, format "bad").""", "key", "a")
    name = 'a' * 39
    checked = notation("'[hv  ' 'op' ( x ,  '/' y ) ']'") + '\nAxiom ' + name + ' : A.'
    check(checked, 'p ' + name + ' ' + name)
    check(checked, 'p ' + name + ' (p ' + name + ' ' + name + ')')
    # A prefix which already occupies columns can move the entire argument to
    # a fresh line. The inner hv box then makes its decision in that column.
    for prefix_length, arg_length in [(12, 29), (5, 33), (3, 35), (20, 27)]:
        prefix = "g" * prefix_length
        atom = "k" * arg_length
        context = notation("'[hv  ' 'op' ( x ,  '/' y ) ']'")
        context += "\nAxiom " + prefix + " : forall _ : A, A. Axiom " + atom + " : A."
        check(context, prefix + " (p " + atom + " " + atom + ")")
    both = notation("'[hv  ' 'op' ( x ,  '/' y ) ']'")
    both += """
Axiom q : forall _ : A, forall _ : A, A.
Notation "'inner' ( x , y )" := (q x y) (at level 0, format "'[v  ' 'inner' ( x ,  '/' y ) ']'")."""
    check(both, 'p a (q a a)')
    check(both, 'q a (p a a)')
    recursive = base + '''Notation "[ x ; .. ; y ]" := (p x .. (p y a) ..)
    (format "'[' [ x ;  '/' .. ;  '/' y ] ']'").'''
    check(recursive, "p a (p a (p a a))", "[a; a; a]")
    multiple = """Axiom A : Set.
Axiom k : A.
Axiom nil : A.
Axiom cons : forall _ : A, forall _ : A, A.
Axiom two : forall _ : A, forall _ : A, A.
Notation "[ x ; .. ; y | u # .. # v ]" :=
    (two (cons x .. (cons y nil) ..) (cons u .. (cons v nil) ..))
    (format "'[v  ' [ x ;  '/' .. ;  '/' y  |  u #  '/' .. #  '/' v ] ']'").
"""
    check(multiple, "two (cons k nil) (cons k (cons k (cons k nil)))")
    check(multiple, "two (cons k (cons k (cons k nil))) (cons k (cons k nil))")
    (work / 'Formats.lol').write_text(notation("'[v  ' 'op' ( x , '/' y ) ']'"))
    explicit = invoke([exe, '--explicit', 'Formats.lol'])
    assert "format " in explicit
    (work / 'Formats.lol').write_text(explicit)
    invoke([exe, '--emit-object=Formats.lolo', 'Formats.lol'])
    (work / 'Client.lol').write_text('Import Formats. Compute (p a a).\n')
    assert invoke([exe, 'Client.lol']).strip() == 'op(a,\n  a)'
    assert "format" in (work / "Formats.lolo").read_text()
    (work / "Formats.lol").unlink()
    invoke([exe, '--check-only', 'Formats.lolo'])
    bad = [notation(fmt) for fmt in ["'op' x y", "'[v ' 'op' ( x , y )", "'op' ( x , y ) ']'"]]
    bad.append(multiple.replace(".. #  '/' v", ".. # v"))
    bad.append(multiple.replace("x ; .. ; y", "x ;  .. ; y", 1))
    for src in bad:
        (work / 'Bad.lol').write_text(src)
        (work / 'Bad.v').write_text(src)
        invoke([exe, 'Bad.lol'], False)
        invoke([rocq, 'compile', '-noinit', 'Bad.v'], False)

print("V1 format: spacing, flowing/vertical/hv boxes, forced break, width, recursive range, malformed formats, explicit and object replay passed.")
