"""Run local release checks from the repository root on Linux."""

import argparse
import os
from pathlib import Path
import subprocess
import sys

public = Path('lol.cabal').is_file()
name = 'lol' if public else 'ppap'
test = Path('test' if public else 'test/lol')
guard = test / 'resources.py'


def bounded(command, memory, seconds, env=None):
    subprocess.run(
        [sys.executable, str(guard), '--rss-mib', str(memory), '--seconds', str(seconds), '--', *map(str, command)],
        check=True, timeout=seconds + 10, env=env)


def main():
    cli = argparse.ArgumentParser(description=__doc__)
    cli.add_argument('mode', choices=('proofs', 'sanitizers'))
    args = cli.parse_args()
    instrumented = args.mode == 'sanitizers'
    build = ['--builddir=dist-newstyle/asan', '-fsanitizers', '--constraint=filepath < 1.5'] if instrumented else []
    bounded(['cabal', 'build', '-j2', *build, 'exe:' + name], 3200, 1200)
    binary = subprocess.check_output(['cabal', 'list-bin', *build, 'exe:' + name], text=True).strip()
    driver = [sys.executable, test / 'release/check.py']
    if instrumented:
        env = {**os.environ, 'ASAN_OPTIONS': 'detect_leaks=0:halt_on_error=1:abort_on_error=1',
               'UBSAN_OPTIONS': 'halt_on_error=1:print_stacktrace=1', name.upper() + '_HOL_CACHE': 'off'}
        deps = subprocess.check_output(['ldd', binary], text=True)
        if 'libasan.' not in deps or 'libubsan.' not in deps:
            raise SystemExit('The sanitizer binary must load both libasan and libubsan.')
        references = subprocess.check_output(['nm', '-u', binary], text=True)
        if '__asan_report_load' not in references or '__ubsan_handle_' not in references:
            raise SystemExit('The sanitizer libraries are linked but the executable lacks instrumentation calls.')
        bounded([*driver, 'sanitizers', binary], 2600, 1500, env)
    else:
        if public:
            bounded(['cabal', 'test', 'release-examples', '--test-show-details=direct'], 2600, 1200)
            bounded(['bash', 'test/v1.sh'], 2400, 900)
        else:
            bounded([*driver, 'golden', binary], 2400, 900)
            for suite in sorted(test.glob('v1_*.sh')):
                bounded(['bash', suite], 2400, 140, {**os.environ, 'PPAP_BIN': binary})
        bounded([*driver, 'rocq', binary], 2600, 1800)


if __name__ == '__main__':
    main()
