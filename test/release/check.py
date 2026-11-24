"""Release examples, diagnostic goldens and a compiled independent proof corpus."""

import argparse
from difflib import unified_diff
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import tempfile

HERE = Path(__file__).resolve().parent
ROOT = Path.cwd().resolve()
PUBLIC = (ROOT / 'lol.cabal').is_file()
EXAMPLES = Path('example' if PUBLIC else 'example/LoL')
GUARD = HERE.parent / 'resources.py'
sys.path.insert(0, str(HERE.parent))
from rocq_reference import rocq_binary, require_release


def run(command):
    env = {**os.environ, 'NO_COLOR': '1', 'CLICOLOR_FORCE': '0', 'LOL_IMPORT_CACHE': 'off'}
    return subprocess.run(
        [sys.executable, str(GUARD), '--quiet', '--seconds', '210', '--rss-mib', '2200',
         '--', *map(str, command)], capture_output=True, text=True, env=env, timeout=220)


def checked(command):
    result = run(command)
    if result.returncode:
        raise RuntimeError(f'{command!r} returned {result.returncode}\n{result.stdout}{result.stderr}')
    return result.stdout


def examples():
    files = sorted(EXAMPLES.glob('*.lol'))
    rejected = sorted((EXAMPLES / 'rejected').glob('*.lol'))
    if not files or not rejected:
        raise SystemExit('Run in the project root: expected both examples and rejection examples.')
    return files, rejected


def transcript(binary, source):
    result = run([*binary, source])
    def normalise(text):
        return text.replace(str(ROOT) + '/', '').replace(str(EXAMPLES) + '/', '<examples>/')
    return {'exit': result.returncode, 'stdout': normalise(result.stdout), 'stderr': normalise(result.stderr)}


def golden(binary, positives, rejected, only_positive):
    name = 'public' if PUBLIC else 'development'
    expected = json.loads((HERE / (name + '.json')).read_text())
    all_examples = positives + rejected
    universe = {str(p.relative_to(EXAMPLES)) for p in all_examples}
    if set(expected) != universe:
        raise RuntimeError(f'Example files and golden manifest differ: {set(expected) ^ universe}')
    for source in positives if only_positive else all_examples:
        key = str(source.relative_to(EXAMPLES))
        actual = transcript(binary, source)
        want = expected[key]
        if want.get('exit') != (1 if source in rejected else 0):
            raise RuntimeError(f'{key}: golden file has the wrong acceptance verdict')
        if actual['exit'] != want['exit']:
            raise RuntimeError(f"{key}: expected exit {want['exit']}, got {actual['exit']}\n{actual['stdout']}{actual['stderr']}")
        for stream in ('stdout', 'stderr'):
            if actual[stream] != want[stream]:
                delta = unified_diff(want[stream].splitlines(True), actual[stream].splitlines(True),
                                     key + ' expected ' + stream, key + ' actual ' + stream)
                raise RuntimeError(''.join(delta))
    print(f'Checked {len(positives)} accepted and {0 if only_positive else len(rejected)} rejected example transcripts.')


def rocq_corpus(binary, positives):
    rocq = rocq_binary()
    version = require_release(checked([rocq, '--print-version']))
    sources = sorted(Path('lol/theories').glob('*.lol')) + positives + [HERE.relative_to(ROOT) / 'Invariants.lol']
    if not Path('lol/theories/Logic.lol').is_file():
        raise RuntimeError('Missing standard library')
    with tempfile.TemporaryDirectory(prefix='lol-rocq-release-') as directory:
        tree = Path(directory)
        modules = {}
        # Ask LoL to choose Rocq identifiers itself, including escaped module paths.
        for source in sources:
            checked([*binary, '--rocq-dir=' + directory, source])
            target = tree / source.with_suffix('.v')
            if not target.is_file():
                raise RuntimeError(f'LoL did not emit the main Rocq module for {source}: {target}')
        for path in sorted(tree.rglob('*.v')):
            name = '.'.join(path.relative_to(tree).with_suffix('').parts)
            modules[name] = (path, re.findall(r'^Require Import ([\w.]+)\.$', path.read_text(), re.M))
        done, busy = set(), set()
        def compile_one(name):
            if name in done:
                return
            if name in busy or name not in modules:
                raise RuntimeError(f'Unresolved or cyclic export dependency: {name}')
            busy.add(name)
            target, dependencies = modules[name]
            for dependency in dependencies:
                compile_one(dependency)
            checked([rocq, 'compile', '-noinit', '-Q', tree, '', target])
            busy.remove(name)
            done.add(name)
        for name in modules:
            compile_one(name)
    print(f'Rocq {version} compiled {len(done)} exported modules with -noinit, including every standard-library module and positive example.')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('check', choices=['golden', 'sanitizers', 'rocq'])
    parser.add_argument('binary', type=Path)
    args = parser.parse_args()
    binary = [str(args.binary.resolve())] + ([] if PUBLIC else ['LoL'])
    positives, rejected = examples()
    if args.check == 'rocq':
        rocq_corpus(binary, positives)
    else:
        golden(binary, positives, rejected, only_positive=args.check == 'sanitizers')
        output = checked([*binary, HERE.relative_to(ROOT) / 'Invariants.lol'])
        if output.splitlines() != ['Tree'] + ['(* No assumptions. *)'] * 6:
            raise RuntimeError('Unexpected closed computation or proof assumptions: ' + output)


if __name__ == '__main__':
    main()
