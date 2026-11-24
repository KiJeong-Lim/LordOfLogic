"""Flat constructor destructuring inside a notation binder, on LoL and Rocq."""
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile

from rocq_reference import require_release, rocq_binary


exe = str(Path(sys.argv[1]).resolve())
root = Path.cwd()
rocq = rocq_binary()
header = """Inductive Bit : Set := | bit0 : Bit | bit1 : Bit.
Inductive Pair : Set := | pair : forall _ : Bit, forall _ : Bit, Pair.
Definition applyPair (f : forall _ : Pair, Bit) : Bit := f (pair bit0 bit1).
Axiom hold : forall _ : (forall _ : Pair, Bit), Bit.
"""
modes = ["pattern", "strict pattern", "as pattern", "as strict pattern",
         "constr as pattern", "pattern at level 10", "at level 0 as pattern"]


with tempfile.TemporaryDirectory() as scratch:
    work = Path(scratch)
    shutil.copytree(root / 'lol/hol', work / 'lol/hol')

    def invoke(args, success=True):
        proc = subprocess.run(args, cwd=work, timeout=18, capture_output=True, text=True)
        assert (proc.returncode == 0) == success, (args, proc.stdout, proc.stderr)
        return proc.stdout

    def both(text, success=True):
        (work / 'Pattern.lol').write_text(text)
        (work / 'Pattern.v').write_text(text)
        native = invoke([exe, 'Pattern.lol'], success)
        external = invoke([rocq, 'compile', '-noinit', 'Pattern.v'], success)
        return native, external

    require_release(invoke([rocq, '--print-version']))
    for mode in modes:
        notation = header + f'''Notation "'READ' p , t" := (applyPair (fun p => t)) (at level 50, p {mode}).
Notation "'KEEP' p , t" := (hold (fun p => t)) (at level 50, p {mode}).
'''
        text = notation + '''Compute READ (pair a b), b.
Compute READ _, bit0.
Compute READ v, bit1.
Compute (hold (fun v : Pair => match v return Bit with | pair a b => b end)).
Compute (hold (fun v : Pair => bit0)).
'''
        native, external = both(text)
        answers = native.strip().splitlines()
        assert answers[:3] == ['bit1', 'bit0', 'bit1'], (mode, answers)
        assert answers[3].startswith('KEEP ' if mode != 'strict pattern' else 'hold ') and 'pair' in answers[3], (mode, answers)
        assert ('KEEP ' in answers[4]) == (mode != 'strict pattern'), (mode, answers)
        assert ('KEEP ' in external) == (mode != 'strict pattern') and '= bit1' in external, (mode, external)
        _, direct = both(notation + 'Check KEEP (pair a b), b.\n')
        assert 'KEEP ' in direct and 'pair' in direct, (mode, direct)
        # A shown constructor pattern must read under the notation's binder.
        repeated, _ = both(notation + f'Compute {answers[3]}.\n')
        assert repeated.strip() == answers[3], (answers[3], repeated)

    entry = header + """Declare Custom Entry pat.
Notation "'PAIR' a b" := (pair a b) (in custom pat at level 0, a ident, b ident).
Notation "'VAR' a" := a (in custom pat at level 0, a ident).
Notation "'ANY'" := _ (in custom pat at level 0).
Notation "'go' ( e )" := e (at level 0, e custom pat at level 99).
"""
    # The concrete operand entry is independent of the production's entry.
    for destination in ["custom pat", "custom pat at level 20"]:
        for modifier in ["pattern", "strict pattern"]:
            syntax = entry + f"""Notation "'READ' p , t" := (applyPair (fun p => t)) (at level 50, p {destination} as {modifier}).
Notation "'KEEP' p , t" := (hold (fun p => t)) (at level 50, p {destination} as {modifier}).
"""
            native, external = both(syntax + "Compute READ PAIR a b, b. Compute hold (fun unused : Pair => bit1).")
            assert native.splitlines() == ["bit1", "KEEP ANY, bit1"], (destination, modifier, native)
            assert "= KEEP ANY, bit1" in external, external
            assert both(syntax + "Compute KEEP ANY, bit1.")[0].strip() == "KEEP ANY, bit1"
            both(syntax + "Check READ (pair a b), b.", False)

    for modifier in ["custom pat at next level", "at next level"]:
        syntax = entry + f"""Notation "'READ' p , t" := (applyPair (fun p => t)) (in custom pat at level 50, p {modifier} as pattern, t constr).
"""
        assert both(syntax + "Compute go (READ PAIR a b, b).")[0].strip() == "bit1"
    native_mode = entry + """Notation "'READ' p , t" := (applyPair (fun p => t)) (at level 50, p at next level as strict pattern).
"""
    assert both(native_mode + "Compute READ (pair a b), b.")[0].strip() == "bit1"
    for wrong in ["custom pat at next level as pattern", "pattern at next level", "strict pattern at next level"]:
        both(entry + f"""Notation "'BAD' p , t" := (applyPair (fun p => t)) (at level 50, p {wrong}).""", False)

    shared = entry + """Notation "'READ' p , t" := (applyPair (fun p => t)) (at level 50, p custom pat as pattern).
"""
    (work / "Shared.lol").write_text(shared)
    (work / "ExpandedShared.lol").write_text(invoke([exe, "--explicit", "Shared.lol"]) + "Compute READ PAIR a b, b.")
    assert invoke([exe, "ExpandedShared.lol"]).strip() == "bit1"
    invoke([exe, "--emit-object=Shared.lolo", "Shared.lol"])
    (work / "Crossed.lol").write_text("Import Shared. Compute READ PAIR a b, b.")
    assert invoke([exe, "Crossed.lol"]).strip() == "bit1"
    invoke([exe, "--emit-object=Crossed.lolo", "Crossed.lol"])
    (work / "Shared.lol").unlink()
    (work / "Crossed.lol").unlink()
    invoke([exe, "--check-only", "Crossed.lolo"])

    term_only = header + '''Notation "'VIEW' p" := p (at level 10, p pattern).
Compute VIEW (pair bit0 bit1).
'''
    # An operand used solely as a term may name constructors recursively.
    native, _ = both(term_only)
    assert 'pair bit0 bit1' in native, native
    both(header + '''Notation "'INVALID' p" := p (at level 10, p as pattern).
''', False)

    case = header + '''Notation "'LOOK' p 'at' v 'yield' f" :=
  (match v with | p => f end) (at level 50, p as pattern).
Definition first (obj : Pair) : Bit := LOOK (pair a b) at obj yield a.
Definition unchanged (obj : Pair) : Pair := LOOK whole at obj yield whole.
'''
    native, _ = both(case + 'Compute (first (unchanged (pair bit1 bit0))).\n')
    assert native.strip() == 'bit1'
    recovered, _ = both(case + 'Compute (fun v : Pair => match v return Bit with | pair a b => a end).\n')
    assert 'LOOK ' in recovered and 'pair' in recovered, recovered
    assert both(case + f'Compute ({recovered.strip()}).\n')[0].strip() == recovered.strip()
    # Check the published grammar in both replay formats.
    (work / 'Pattern.lol').write_text(case)
    explicit = invoke([exe, '--explicit', 'Pattern.lol'])
    (work / 'Explicit.lol').write_text(explicit + 'Compute (first (pair bit1 bit0)).\n')
    assert invoke([exe, 'Explicit.lol']).strip() == 'bit1'
    invoke([exe, '--emit-object=Pattern.lolo', 'Pattern.lol'])
    (work / 'Use.lol').write_text('Import Pattern. Definition take (x : Pair) : Bit := LOOK (pair a b) at x yield b. Compute (take (pair bit0 bit1)).\n')
    assert invoke([exe, 'Use.lol']).strip() == 'bit1'
    invoke([exe, '--emit-object=Use.lolo', 'Use.lol'])
    (work / 'Pattern.lol').unlink()
    (work / 'Use.lol').unlink()
    invoke([exe, '--check-only', 'Use.lolo'])

    # Bit has two constructors. A single-clause flat binder cannot cover both.
    both(header + '''Axiom useBit : forall _ : (forall _ : Bit, Bit), Bit.
Notation "'SINGLE' p , t" := (useBit (fun p => t)) (at level 50, p pattern).
Check SINGLE bit1, bit0.
''', False)

print('V1 pattern slots: native and custom grammar entries, entry levels, strict and ordinary patterns, inverse display and object replay passed.')
