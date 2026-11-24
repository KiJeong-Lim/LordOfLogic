'use strict';

const vscode = require('vscode');
const path = require('node:path');
const { Server, Session } = require('./client');

let stopOnExit;

function activate(context) {
    const diagnostics = vscode.languages.createDiagnosticCollection('LoL');
    const log = vscode.window.createOutputChannel('LoL Server');
    const changes = new vscode.EventEmitter();
    let rows = [];
    const tree = vscode.window.createTreeView('lordOfLogic.proof', {
        treeDataProvider: {
            onDidChangeTreeData: changes.event,
            getChildren: () => rows,
            getParent: () => undefined,
            getTreeItem: item => {
                const row = new vscode.TreeItem(item.text);
                row.tooltip = item.text;
                return row;
            }
        }
    });
    context.subscriptions.push(diagnostics, log, tree, changes);

    let session, server, owner, project, timer;
    let generation = 0;
    let queue = Promise.resolve();
    let dependencyChanged = false;
    let cursorMove, requestedTarget;
    const targetOf = editor => JSON.stringify([editor.document.uri.toString(), editor.document.version,
        editor.document.offsetAt(editor.selection.active)]);
    const owns = doc => owner && doc && owner.uri.toString() === doc.uri.toString();
    const contextActive = value => vscode.commands.executeCommand('setContext', 'lordOfLogic.active', value);

    function display(message, reply, output = []) {
        const lines = [];
        if (reply?.proof) {
            const proof = reply.proof;
            lines.push(...[...(proof.locals || [])].reverse().map(local => {
                const body = local.bodyDisplay ? ' := ' + local.bodyDisplay : '';
                return (local.name ?? '…') + body + ' : ' + (local.typeDisplay ?? '…');
            }));
            lines.push(proof.complete ? 'No goals remain.' : '⊢ ' + (proof.display ?? '…'));
            if (proof.truncated) lines.push('The server omitted part of this proof state.');
        }
        lines.push(...output.map(line => line ?? '…'));
        rows = lines.flatMap(line => line.split('\n')).map(text => ({ text }));
        tree.description = [owner && path.basename(owner.fileName), reply?.proofName].filter(Boolean).join(' · ');
        tree.message = message || (rows.length ? undefined : 'No open proof.');
        changes.fire();
    }

    function interrupt() {
        clearTimeout(timer);
        generation++;
        if (server) server.cancel().catch(error => log.appendLine(error.message));
        return generation;
    }

    async function release() {
        const old = server;
        server = undefined;
        session = undefined;
        project = undefined;
        if (old) await old.stop();
    }

    async function ensure(editor, current) {
        const doc = editor.document;
        const folder = vscode.workspace.getWorkspaceFolder(doc.uri);
        if (!folder || doc.uri.scheme !== 'file') throw new Error('Open the project folder containing lol/hol and a .lol file.');
        if (!vscode.workspace.isTrusted) throw new Error('Trust the workspace to run its proof server.');
        if (session && owns(doc) && !server.closed && !dependencyChanged) return;
        await release();
        if (!current()) return;
        owner = doc;
        project = folder;
        dependencyChanged = false;
        const config = vscode.workspace.getConfiguration('lordOfLogic', doc.uri);
        server = new Server(config.get('executable'), config.get('arguments'), folder.uri.fsPath, chunk => log.append(chunk));
        session = new Session(server, doc.uri.fsPath);
        await server.ready;
    }

    function report(error, editor) {
        const detail = error.reply?.error;
        const message = detail ? ('[' + detail.code + '] ' + detail.message) : error.message;
        if (detail?.range && session && editor.document.getText() === session.source.text) {
            const from = editor.document.positionAt(session.source.offset(detail.range.from));
            const to = editor.document.positionAt(session.source.offset(detail.range.to, true));
            const item = new vscode.Diagnostic(new vscode.Range(from, to), [message, ...(detail.details || [])].filter(Boolean).join('\n'));
            item.source = 'LoL';
            item.code = detail.code;
            diagnostics.set(editor.document.uri, [item]);
        }
        display(message, session?.reply);
        log.appendLine(message);
        if (!detail) vscode.window.showErrorMessage(message);
    }

    function moveCursor(editor, offset) {
        const pos = editor.document.positionAt(offset);
        if (editor.selection.isEmpty && editor.selection.active.isEqual(pos)) return;
        cursorMove = [editor.document.uri.toString(), editor.document.version, offset];
        editor.selection = new vscode.Selection(pos, pos);
        editor.revealRange(new vscode.Range(pos, pos), vscode.TextEditorRevealType.InCenterIfOutsideViewport);
    }

    function run(editor, action, id) {
        const current = () => id === generation && !editor.document.isClosed;
        const work = async () => {
            if (!current()) return;
            try {
                const first = !owns(editor.document) || !session;
                if (first) {
                    diagnostics.clear();
                    await contextActive(true);
                }
                await ensure(editor, current);
                if (!current()) return;
                const doc = editor.document;
                const offset = doc.offsetAt(editor.selection.active);
                await session.sync(doc.getText());
                if (!current()) return;
                if (action === 'next') await session.next();
                else if (action === 'undo') await session.previous(current);
                else await session.toCursor(offset, current);
                if (!current()) return;
                diagnostics.delete(doc.uri);
                display(undefined, session.reply, session.output);
                if (action !== 'check') moveCursor(editor, session.offset);
                if (first && rows.length) await tree.reveal(rows[0], { focus: false, select: false });
                return session.reply;
            } catch (error) {
                if (current()) report(error, editor);
                return current() ? error.reply : undefined;
            }
        };
        queue = queue.then(work, work);
        return queue;
    }

    function command(action) {
        const editor = vscode.window.activeTextEditor;
        if (!editor || editor.document.languageId !== 'lord-of-logic') return;
        const id = interrupt();
        requestedTarget = targetOf(editor);
        display('Checking…');
        return run(editor, action, id);
    }

    function follow(editor, force = false) {
        if (!editor || !owns(editor.document)) return;
        const target = targetOf(editor);
        if (!force && requestedTarget === target) return;
        requestedTarget = target;
        const id = interrupt();
        diagnostics.delete(editor.document.uri);
        display('Checking…');
        timer = setTimeout(() => run(editor, 'check', id), 120);
    }

    function stop() {
        interrupt();
        owner = undefined;
        requestedTarget = undefined;
        diagnostics.clear();
        display();
        contextActive(false);
        // Shutdown also stops an outstanding non-interruptible command. Pending
        // callbacks see their superseded generation before touching the new view.
        const stopped = release();
        queue = queue.then(() => stopped, () => stopped);
        return queue;
    }
    stopOnExit = stop;
    for (const action of ['check', 'next', 'undo']) {
        context.subscriptions.push(vscode.commands.registerCommand('lordOfLogic.' + action, () => command(action)));
    }
    context.subscriptions.push(
        vscode.commands.registerCommand('lordOfLogic.stop', stop),
        vscode.commands.registerCommand('lordOfLogic.cancel', async () => {
            const id = interrupt();
            await queue;
            if (id === generation && owner) display('Checking stopped.', session?.reply);
        }),
        vscode.workspace.onDidChangeTextDocument(change => {
            if (change.contentChanges.length && owns(change.document)) {
                cursorMove = undefined;
                follow(vscode.window.visibleTextEditors.find(editor => owns(editor.document)));
            }
        }),
        vscode.window.onDidChangeTextEditorSelection(event => {
            if (!owns(event.textEditor.document) || event.textEditor !== vscode.window.activeTextEditor) return;
            const doc = event.textEditor.document;
            const offset = doc.offsetAt(event.selections[0].active);
            if (cursorMove && cursorMove[0] === doc.uri.toString() && cursorMove[1] === doc.version && cursorMove[2] === offset) {
                cursorMove = undefined;
                requestedTarget = targetOf(event.textEditor);
                return;
            }
            cursorMove = undefined;
            follow(event.textEditor);
        }),
        vscode.workspace.onDidCloseTextDocument(doc => { if (owns(doc)) stop(); }),
        vscode.workspace.onDidSaveTextDocument(doc => {
            if (!project || owns(doc) || !/\.(lol|hol)$/.test(doc.fileName)) return;
            if (vscode.workspace.getWorkspaceFolder(doc.uri)?.uri.toString() === project.uri.toString()) {
                dependencyChanged = true;
                follow(vscode.window.visibleTextEditors.find(editor => owns(editor.document)), true);
            }
        }),
        vscode.workspace.onDidChangeConfiguration(event => {
            if (server && event.affectsConfiguration('lordOfLogic')) {
                dependencyChanged = true;
                follow(vscode.window.activeTextEditor, true);
            }
        })
    );
}

function deactivate() {
    return stopOnExit?.();
}

module.exports = { activate, deactivate };
