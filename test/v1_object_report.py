"""Check what a recipient learns when only the checked object graph is available."""
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
exe = str(Path(sys.argv[1]).resolve())


def invoke(work, arguments, status=0):
    result = subprocess.run([exe, *arguments], cwd=work, text=True,
                            capture_output=True, timeout=18)
    assert result.returncode == status, (arguments, result)
    return result.stdout, result.stderr


with tempfile.TemporaryDirectory(prefix='lol-object-report-') as temporary:
    work = Path(temporary)
    shutil.copytree(ROOT / 'lol/hol', work / 'lol/hol')
    sources = {
        'Left': 'Axiom Claim : Prop. Axiom witness : Claim.',
        'Right': 'Axiom Claim : Prop. Axiom witness : Claim.',
        'Middle': 'Import Left. Theorem hidden : Claim := witness.',
        'Data': ('Inductive N : Set := | z : N. '
                 'Theorem ident : forall a : N, N. Proof. intro a. exact a. Qed.'),
        'Unused': ('Import Right. '
                   'Theorem identity : forall P : Prop, P -> P := fun P p => p.'),
        'Client': ('Import Middle. Import Left. Import Right. '
                   'Theorem local : Right.Claim := Right.witness. '
                   'Definition through : Left.Claim := Middle.hidden. '
                   'Theorem transported : Left.Claim := through.'),
    }
    for name, source in sources.items():
        (work / (name + '.lol')).write_text(source + '\n')
    for name in ['Client', 'Data', 'Unused']:
        output, _ = invoke(work, ['--emit-object=' + name + '.lolo', name + '.lol'])
        if name == 'Data':
            assert output == 'The theorem was accepted.\n', output
    for source in work.glob('*.lol'):
        source.unlink()
    for hol in (work / 'lol/hol').glob('*.hol'):
        if hol.name != 'kernel.hol':
            hol.unlink()
    report, error = invoke(work, ['--check-only', 'Client.lolo'])
    assert not error and report.startswith('Checked object Client.\n'), (report, error)
    assert 'Module Left.\nAxiom Claim : Prop.\nAxiom witness : Left.Claim.' in report, report
    assert 'Definition through : Left.Claim.' in report, report
    assert 'Theorem transported : Left.Claim.\n  Assumptions: Left.Claim, Left.witness' in report, report
    assert 'Theorem local : Right.Claim.\n  Assumptions: Right.Claim, Right.witness' in report, report
    assert 'Theorem hidden : Left.Claim.\n  Assumptions: Left.Claim, Left.witness' in report, report
    denied, error = invoke(work, ['--check-only', '--no-axioms', 'Client.lolo'], 1)
    assert denied == report and '--no-axioms' in error, (denied, error)
    safe, _ = invoke(work, ['--no-axioms', '--check-only', 'Data.lolo'])
    assert '  Assumptions: none' in safe and safe.endswith('Axioms in checked modules: none\n'), safe
    assert 'Inductive N' in safe and 'Theorem ident' in safe, safe
    unused, _ = invoke(work, ['--check-only', '--no-axioms', 'Unused.lolo'], 1)
    assert '  Assumptions: none' in unused and 'Axioms in checked modules: Right.Claim, Right.witness' in unused, unused
    (work / 'Wrong.lolo').write_bytes((work / 'Client.lolo').read_bytes()[:74])
    failed, _ = invoke(work, ['--check-only', 'Wrong.lolo'], 1)
    assert 'Checked object' not in failed and '[I-Object]' in failed, failed
    refused, _ = invoke(work, ['--no-axioms', 'Data.lol'], 1)
    assert '--no-axioms requires --check-only' in refused, refused

print('PASS source-free declaration reports, qualified transitive assumptions, and axiom policy')
