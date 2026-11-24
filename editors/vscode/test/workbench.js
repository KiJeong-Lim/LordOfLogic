'use strict';

const vscode = require('vscode');
const assert = require('node:assert/strict');

async function waitFor(check, message) {
    const start = Date.now();
    while (!check()) {
        if (Date.now() - start > 12000) throw new Error(message);
        await new Promise(resolve => setTimeout(resolve, 30));
    }
}

async function run() {
    const root = vscode.workspace.workspaceFolders[0];
    const uri = vscode.Uri.joinPath(root.uri, 'Editor.lol');
    const doc = await vscode.workspace.openTextDocument(uri);
    const first = new vscode.Position(3, 3);
    const editor = await vscode.window.showTextDocument(doc, { selection: new vscode.Range(first, first) });
    const extension = vscode.extensions.getExtension('lord-of-logic.lord-of-logic');
    assert(extension, 'The development extension was not discovered.');
    assert.equal(doc.languageId, 'lord-of-logic');
    // Checking a proof activates the extension. Installing the language alone starts no worker.
    const run = verb => vscode.commands.executeCommand('lordOfLogic.' + verb);
    const place = (line, column) => {
        const pos = new vscode.Position(line, column);
        if (editor.selection.active.isEqual(pos)) return Promise.resolve();
        // The renderer may still deliver the previous selection (including the
        // initial position restored when the document was opened). Wait for its
        // acknowledgement before sending a proof command for the new position.
        return new Promise((resolve, reject) => {
            const listener = vscode.window.onDidChangeTextEditorSelection(event => {
                if (event.textEditor !== editor || !event.selections[0].active.isEqual(pos)) return;
                clearTimeout(timeout);
                listener.dispose();
                resolve();
            });
            const timeout = setTimeout(() => {
                listener.dispose();
                reject(new Error('The workbench did not confirm the requested cursor position.'));
            }, 12000);
            editor.selection = new vscode.Selection(pos, pos);
        });
    };
    await place(3, 3);
    assert.equal((await run('check')).proof.display, 'P');
    assert.equal((await run('undo')).proof.display, 'Q');
    assert.equal((await run('next')).proof.display, 'P');
    const edit = async (line, text) => {
        const ok = await editor.edit(builder => builder.replace(doc.lineAt(line).range, text));
        assert(ok);
    };
    // Leave the cursor on the edited tactic. Diagnostics appear without another command.
    await edit(3, '(* 😀 *) exact p.');
    await place(3, 11);
    const failures = () => vscode.languages.getDiagnostics(uri).filter(x => x.source === 'LoL');
    await waitFor(() => failures().length > 0, 'No diagnostic after a buffer edit.');
    assert.equal(failures()[0].code, 'P-StepFailed');
    assert.match(doc.getText(failures()[0].range), /exact p/);
    await edit(3, 'apply f.');
    await place(3, 3);
    await waitFor(() => !failures().length, 'The previous error survived a successful edit.');
    assert.equal((await run('check')).proof.display, 'P');
    await place(5, 4);
    assert.deepEqual((await run('check')).proof, null);
    await run('stop');
    assert.deepEqual(failures(), []);
    console.log('Workbench proof commands, edit tracking and Unicode diagnostics passed.');
}

module.exports = { run };
