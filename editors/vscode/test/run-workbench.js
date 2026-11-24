'use strict';

const { spawn } = require('node:child_process');
const fs = require('node:fs/promises');
const os = require('node:os');
const path = require('node:path');

async function main() {
    const [desktop, binary, ...serverArgs] = process.argv.slice(2);
    if (!desktop || !binary) throw new Error('Usage: node test/run-workbench.js CODE-EXECUTABLE LOL-EXECUTABLE [SERVER ARGS]');
    const dir = await fs.mkdtemp(path.join(os.tmpdir(), 'lol-vscode-test-'));
    const root = path.join(dir, 'project');
    try {
        await fs.mkdir(path.join(root, 'lol'), { recursive: true });
        await fs.cp('lol/hol', path.join(root, 'lol', 'hol'), { recursive: true });
        await fs.writeFile(path.join(root, 'Editor.lol'), [
            'Theorem swap : forall P Q : Prop, (P -> Q) -> P -> Q.', 'Proof.', 'intros P Q f p.', 'apply f.', 'exact p.', 'Qed.', ''
        ].join('\n'));
        const user = path.join(dir, 'profile', 'User');
        await fs.mkdir(user, { recursive: true });
        await fs.writeFile(path.join(user, 'settings.json'), JSON.stringify({
            'lordOfLogic.executable': path.resolve(binary),
            'lordOfLogic.arguments': serverArgs.length ? serverArgs : ['--server'],
            'update.mode': 'none',
            'telemetry.telemetryLevel': 'off',
            'window.restoreWindows': 'none',
            'workbench.startupEditor': 'none'
        }));
        const extension = path.resolve(__dirname, '..');
        const env = { ...process.env };
        delete env.ELECTRON_RUN_AS_NODE;
        delete env.VSCODE_IPC_HOOK_CLI;
        const child = spawn(desktop, [
            '--no-sandbox', '--disable-gpu', '--disable-dev-shm-usage', '--disable-workspace-trust',
            '--disable-extensions', '--skip-release-notes', '--skip-welcome', '--disable-updates',
            '--user-data-dir=' + path.join(dir, 'profile'), '--extensions-dir=' + path.join(dir, 'extensions'),
            '--extensionDevelopmentPath=' + extension, '--extensionTestsPath=' + path.join(__dirname, 'workbench.js'), root
        ], { stdio: 'inherit', env });
        const code = await new Promise((resolve, reject) => {
            child.once('error', reject);
            child.once('exit', resolve);
        });
        if (code !== 0) throw new Error('VS Code tests exited with ' + code + '.');
    } finally {
        await fs.rm(dir, { recursive: true, force: true });
    }
}

main().catch(error => { console.error(error.message); process.exitCode = 1; });
