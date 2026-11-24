'use strict';

const test = require('node:test');
const assert = require('node:assert/strict');
const { Server, Source, Session, ReplyError, splitSource } = require('../client');
const { join } = require('node:path');

const binary = process.env.LOL_EDITOR_TEST_BIN || 'lol';
const args = ['--server'];

function newSession(t, cwd = process.cwd()) {
    const server = new Server(binary, args, cwd);
    t.after(() => server.stop());
    const methods = [];
    const request = server.request.bind(server);
    server.request = (...parameters) => {
        methods.push(parameters[0]);
        return request(...parameters);
    };
    return { session: new Session(server, join(cwd, 'EditorDemo.lol')), server, methods };
}

const script = [
    '(* 😀 *) Theorem swap : forall P Q : Prop, (P -> Q) -> P -> Q.',
    'Proof.', 'intros P Q f p.', 'apply f.', 'exact p.', 'Qed.', ''
].join('\r\n');

function goal(view) {
    return { goal: view.proof?.display, locals: view.proof?.locals?.map(x => [x.name, x.typeDisplay]),
        complete: view.proof?.complete, position: view.position };
}

test('Unicode positions include an inclusive diagnostic end and preserve CRLF', () => {
    const source = new Source('😀α\r\nβ𐀀Z\n');
    assert.equal(source.offset({ line: 1, column: 2 }), 2);
    assert.equal(source.offset({ line: 2, column: 2 }, true), 8);
    assert.equal(source.offset({ line: 3, column: 1 }), 10);
    assert.equal(source.cursorTarget(4), 3);
    assert.equal(new Source('Check Prop.\nCheck Set.').cursorTarget(11), 11);
});

test('source frames preserve astral characters, escapes and exact wire budget', () => {
    const text = ('𐀀' + String.fromCharCode(1) + '\n').repeat(2500);
    const parts = splitSource(text, 4096, { document: 'editor' });
    assert(parts.length > 3);
    assert.equal(parts.join(''), text);
    for (const part of parts) {
        assert(!/^[\uDC00-\uDFFF]|[\uD800-\uDBFF]$/.test(part));
        assert(Buffer.byteLength(JSON.stringify({ source: part })) < 4096);
    }
});

test('check, undo, edit and replay agree with a new engine; suffix edits reuse the prefix', async t => {
    const { session, methods } = newSession(t);
    await session.sync(script);
    await session.toCursor(script.indexOf('apply f.') + 3);
    assert.equal(session.reply.proof.display, 'P');
    const oldIncarnation = session.ref.incarnation;
    await session.previous();
    assert.equal(session.reply.proof.display, 'Q');
    await session.next();
    assert.equal(session.reply.proof.display, 'P');
    const amended = script.replace('apply f.\r\nexact p.', 'exact (f p).');
    const start = methods.length;
    await session.sync(amended);
    assert.deepEqual(methods.slice(start), ['undo', 'replace']);
    const cursor = amended.indexOf('exact (f p).') + 2;
    await session.toCursor(cursor);
    const before = goal(session.reply);
    assert.equal(session.ref.incarnation, oldIncarnation);
    assert.equal(session.reply.proof.complete, true);
    await session.next();
    assert.deepEqual(session.output, ['The theorem was accepted.']);
    await session.sync(amended + 'Check Prop.\n');
    assert.equal(session.ref.incarnation, oldIncarnation);
    await session.toCursor(session.source.text.length);
    assert.deepEqual(session.output, ['Type@{1}']);
    await session.server.stop();
    const clean = newSession(t).session;
    await clean.sync(amended);
    await clean.toCursor(cursor);
    assert.deepEqual(before, goal(clean.reply));
});

test('expired document history reopens from the beginning and replays to the same position', async t => {
    const { session, methods } = newSession(t);
    const source = Array.from({ length: 42 }, (_, i) => 'Definition t' + i + ' : Prop := Prop.').join('\n')
        .replaceAll(' : Prop := Prop.', ' : Type@{1} := Prop.');
    await session.sync(source);
    await session.toCursor(source.length);
    const old = session.ref.incarnation;
    // The first executed declaration and state zero have expired.
    assert(![...session.history.values()].some(pos => pos < source.indexOf('t2 ')));
    const amended = source.replace('t0 ', 'renamed ');
    await session.sync(amended);
    await session.toCursor(amended.indexOf('t1 ') + 1);
    assert.notEqual(session.ref.incarnation, old);
    assert.equal(methods.filter(m => m === 'open').length, 2);
    assert.equal(session.offset, amended.indexOf('\nDefinition t2'));
});

test('a diagnostic range from the kernel survives an astral scalar; replace fixes the failed tactic', async t => {
    const { session } = newSession(t);
    const bad = script.replace('apply f.', '(* 😀 *) exact p.');
    await session.sync(bad);
    await assert.rejects(session.toCursor(bad.indexOf('exact p.') + 1), error => {
        assert(error instanceof ReplyError);
        const problem = error.reply.error;
        assert.equal(problem.code, 'P-StepFailed');
        const range = bad.slice(session.source.offset(problem.range.from), session.source.offset(problem.range.to, true));
        assert.match(range, /exact p/);
        return true;
    });
    await session.sync(script);
    await session.toCursor(script.length);
    assert.deepEqual(session.output, ['The theorem was accepted.']);
});

test('editing the separator after a checked dot reparses the preceding command', async t => {
    const { session } = newSession(t);
    const original = 'Check Prop.\nCheck Set.\n';
    await session.sync(original);
    await session.next();
    await session.sync('Check Prop.Check Set.\n');
    assert.equal(session.offset, 0);
    await assert.rejects(session.next(), ReplyError);
    await session.sync(original);
    await session.toCursor(original.length);
    assert.deepEqual(session.output, ['Type@{1}']);
});

test('cancel an executing tactic, use its final reference, and finish the edited proof', async t => {
    const fs = require('node:fs/promises');
    const os = require('node:os');
    const dir = await fs.mkdtemp(join(os.tmpdir(), 'lol-editor-'));
    t.after(() => fs.rm(dir, { recursive: true, force: true }));
    const tactic = join(dir, 'Loop.hol');
    await fs.writeFile(tactic, 'import lol.hol.tactics.\ntype spin o.\nspin :- spin.\np_user_tactic "loop" [] A R :- spin.\n');
    await fs.mkdir(join(dir, 'lol'));
    await fs.cp('lol/hol', join(dir, 'lol', 'hol'), { recursive: true });
    const { session, server } = newSession(t, dir);
    const source = 'Load Tactics "' + tactic + '".\nTheorem id : forall P : Prop, P -> P.\nintros P p.\ntactic loop.\nQed.\n';
    await session.sync(source);
    await session.toCursor(source.indexOf('intros P p.') + 1);
    assert.equal(session.reply.proof.display, 'P');
    const stopped = assert.rejects(session.next(), error => /cancel/i.test(error.message));
    await new Promise(resolve => setTimeout(resolve, 60));
    assert.equal((await server.cancel()).status, 'ok');
    await stopped;
    assert.equal(session.reply.proof.display, 'P');
    const fixed = source.replace('tactic loop.', 'exact p.');
    await session.sync(fixed);
    await session.toCursor(fixed.length);
    assert.deepEqual(session.output, ['The theorem was accepted.']);
});

test('large UTF-8 buffer uses append frames and still executes the first command', async t => {
    const { session, methods } = newSession(t);
    const text = '(* ' + '😀'.repeat(270000) + ' *)\nCheck Prop.';
    await session.sync(text);
    assert(methods.includes('append'));
    await session.toCursor(text.length);
    assert.deepEqual(session.output, ['Type@{1}']);
});
