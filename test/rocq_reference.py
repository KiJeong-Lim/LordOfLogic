"""The release used for differential checks and its OCaml 5 memory envelope."""
from functools import lru_cache
import os
import shutil
from pathlib import Path
import subprocess
import sys


def require_release(output):
    # rocq-core.9.2.0 prints "9.2 <OCaml version>". Compare the entire release
    # token so development versions and later patches cannot silently enter CI.
    words = output.split()
    if not words or words[0] not in ('9.2', '9.2.0'):
        raise RuntimeError('Rocq 9.2.0 is required; --print-version gave ' + repr(output.strip()))
    return words[0]


def rocq_binary(binary=None):
    selected = binary if binary is not None else os.environ.get('ROCQ', 'rocq')
    path = shutil.which(selected)
    if path is None:
        raise RuntimeError(f'Rocq 9.2.0 is required; executable not found: {selected!r}')
    return os.path.abspath(path)


def version(binary=None):
    output = subprocess.check_output([rocq_binary(binary), '--print-version'], text=True, timeout=5)
    require_release(output)
    return output.strip()


@lru_cache(maxsize=1)
def enclosing_rss_limit():
    # A whole-corpus guard already accounts for all of its children. Verify
    # its ancestry, actual script and limit before avoiding redundant sampling
    # for each small Rocq compilation. An ordinary invocation has no marker.
    try:
        guard = int(os.environ.get('LOL_TEST_RSS_GUARD_PID', '0'))
        if guard <= 1:
            return None
        parent = os.getppid()
        while parent > 1 and parent != guard:
            parent = int(Path(f'/proc/{parent}/stat').read_text().rsplit(')', 1)[1].split()[1])
        if parent != guard:
            return None
        proc = Path(f'/proc/{guard}')
        arguments = (proc / 'cmdline').read_bytes().decode().rstrip('\0').split('\0')
        script, options = arguments[1], arguments[2:arguments.index('--')]
        if (proc / 'cwd' / script).resolve() != Path(__file__).with_name('resources.py').resolve():
            return None
        return int(options[options.index('--rss-mib') + 1]) * 1024 ** 2
    except (OSError, ValueError, IndexError, UnicodeError):
        return None


def rss_command(command, seconds, memory):
    # OCaml 5 reserves a large virtual address space at startup. Bound the
    # complete process tree by resident bytes and keep the timeout transitive.
    ceiling = enclosing_rss_limit()
    if ceiling is not None and ceiling <= memory:
        return command
    return [sys.executable, str(Path(__file__).with_name('resources.py')), '--quiet',
            '--rss-mib', str(memory // (1024 ** 2)), '--seconds', str(seconds), '--', *command]


if __name__ == '__main__':
    print(version(*sys.argv[1:]))
