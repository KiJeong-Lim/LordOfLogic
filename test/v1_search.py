"""Exercise Search against the live document cursor, direct imports and Rocq."""
from pathlib import Path
import json
import re
import shutil
import subprocess
import sys
import tempfile

from rocq_reference import require_release, rocq_binary


root = Path.cwd()
exe = Path(sys.argv[1]).resolve()


def invoke(args, directory, succeeds=True):
    p = subprocess.run(args, cwd=directory, capture_output=True, text=True, timeout=28)
    assert (p.returncode == 0) == succeeds, (args, p.stdout, p.stderr)
    return p.stdout + p.stderr


with tempfile.TemporaryDirectory() as scratch:
    work = Path(scratch)
    shutil.copytree(root / "lol", work / "lol")
    source = work / "Queries.lol"

    def run(text, succeeds=True):
        source.write_text(text)
        return invoke([exe, source.name], work, succeeds)

    # This occurrence has implicit arguments at both the outer and inner head.
    output = run('Import lol.theories.List.\nImport lol.theories.ListProperties.\n'
                 'Search (rev (app _ _)) "rev_app" in lol.theories.ListProperties.\n')
    assert output.startswith('lol.theories.ListProperties.rev_app : forall '), output
    assert output.count(' : forall ') == 1, output

    (work / 'Deep.lol').write_text('Axiom search_hidden : Prop.\n')
    (work / 'Near.lol').write_text('Import Deep.\nAxiom search_visible : Prop.\n')
    imports = 'Import Near.\n'
    # The first Undo must reverse the import. If Search consumed that step,
    # the second search would still print Near.search_visible.
    found = run(imports + 'Search _ "search_".\nUndo.\nSearch _ "search_".\n')
    assert found.count('Near.search_visible : Prop') == 1 and 'search_hidden' not in found, found
    assert not run(imports + 'Search _ "search_" outside Near.\n').strip()
    out = run(imports + 'Search Deep.search_hidden.\n', succeeds=False)
    assert 'unknown name' in out and 'Deep.search_hidden' in out, out

    # A proof local must not match the coincident de Bruijn index of a
    # binder inside a closed global signature. Search leaves the goals alone.
    out = run('Axiom Candidate : forall P : Prop, P -> P.\n'
              'Theorem keep : forall A : Prop, A -> A.\nProof.\nintros A h.\n'
              'Search A.\nUndo.\nintros A h.\nexact h.\nQed.\n')
    assert 'h : A' in out and 'Queries.Candidate :' not in out and 'The theorem was accepted.' in out, out

    # The live server returns a document cursor for every consumed command.
    # Search must preserve the entire debugger view, including available goals.
    commands = ('Axiom rel : forall _ : Prop, forall _ : Prop, Prop.\n'
                'Notation "x ≈ y" := (rel x y) (at level 70).\n'
                'Theorem prove : forall A : Prop, (rel A A) -> rel A A.\n'
                'Proof.\nintros A h.\nSearch A.\nexact h.\nQed.\n')
    with subprocess.Popen([exe, '--server'], cwd=work, stdin=subprocess.PIPE,
                          stdout=subprocess.PIPE, text=True) as server:
        assert json.loads(server.stdout.readline())['event'] == 'ready'
        def ask(number, method, **fields):
            request = dict(protocol=2, id=number, method=method, **fields)
            server.stdin.write(json.dumps(request) + '\n')
            server.stdin.flush()
            answer = json.loads(server.stdout.readline())
            assert answer['status'] == 'ok', answer
            return answer
        cursor = ask(1, 'open', document='query', revision=0, path=source.name, source=commands)
        states = []
        for index in range(8):
            cursor = ask(index + 2, 'next', **{key: cursor[key] for key in ('document', 'revision', 'incarnation', 'state')})
            states.append(cursor)
        before, after = states[4], states[5]
        # viewBudget charges the complete response, including the extra search text.
        proof_state = lambda reply: {k: v for k, v in reply['proof'].items() if k != 'viewBudget'}
        assert proof_state(before) == proof_state(after) and before['state'] != after['state']
        assert 'A ≈ A' in before['proof']['display'], before['proof']
        ask(10, 'shutdown')

    # Compare identical wildcard, explicit application, alpha-renamed binder
    # and name filters in the Gallina fragment, without a prelude.
    declarations = ('Axiom Item : Set.\nAxiom f : forall x : Item, Item.\n'
                    'Axiom Hit : forall t : Item, forall g : (forall z : Item, Item), Item.\n'
                    'Axiom Miss : Prop.\nAxiom P : forall x : Item, Prop.\n'
                    'Axiom Shape : forall x : Item, P (f x).\n')
    reference = work / 'Queries.v'
    rocq = rocq_binary()
    require_release(invoke([rocq, '--print-version'], work))
    for statement, expected in [
        ('Search (P (f _)).', {'Shape'}),
        ('Search (@P (@f _)).', {'Shape'}),
        ('Search (forall y : Item, P (f y)).', {'Shape'}),
        ('Search _ "Hit".', {'Hit'}),
        ('Search P -"Shape".', set()),
    ]:
        text = declarations + statement + '\n'
        reference.write_text(text)
        native = run(text)
        external = invoke([rocq, 'compile', '-noinit', reference.name], work)
        names = r'(?m)^\s*(?:Queries\.)?(Item|f|Hit|Miss|P|Shape)\s*:'
        assert set(re.findall(names, native)) == expected, (statement, native)
        assert set(re.findall(names, external)) == expected, (statement, external)

    # Dependent field types come from the kernel and Search does not admit
    # a new constant in order to inspect them.
    out = run('#[projections(primitive)] Record Pack : Type@{1} := mkPack { carrier : Set ; field : carrier }.\n'
              'Search Pack "field".\n')
    assert 'Queries.field :' in out and 'carrier' in out, out

print('V1 Search: term/name/module filters, scopes and Undo, proof locals, projection types and five Rocq 9.2.0 comparisons passed.')
