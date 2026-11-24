'use strict';

const { spawn } = require('node:child_process');
const { createInterface } = require('node:readline');

class Server {
    constructor(executable, args, cwd, log = () => {}) {
        this.process = spawn(executable, args, { cwd, stdio: ['pipe', 'pipe', 'pipe'], windowsHide: true });
        this.pending = new Map();
        this.nextId = 1;
        this.activeNext = null;
        this.closed = false;
        this.ready = new Promise((resolve, reject) => {
            this.receiveReady = resolve;
            this.rejectReady = reject;
        });
        // An executable can fail before the first request awaits the greeting.
        this.ready.catch(() => {});
        this.exit = new Promise(resolve => this.process.once('close', resolve));
        const reader = createInterface({ input: this.process.stdout, crlfDelay: Infinity });
        reader.on('line', line => {
            try {
                const reply = JSON.parse(line);
                if (reply.protocol !== 2) throw new Error('This editor requires LoL protocol 2.');
                if (this.receiveReady && reply.event === 'ready') {
                    if (!Number.isSafeInteger(reply.requestByteLimit) || reply.requestByteLimit < 4096) {
                        throw new Error('Invalid request byte limit in the LoL greeting.');
                    }
                    this.limit = reply.requestByteLimit;
                    this.receiveReady(reply);
                    this.receiveReady = null;
                    return;
                }
                const waiter = this.pending.get(reply.id);
                if (!waiter) throw new Error(reply.error?.message || 'Unexpected reply from the LoL server.');
                this.pending.delete(reply.id);
                waiter.resolve(reply);
            } catch (error) {
                this.fail(error);
                this.process.kill();
            }
        });
        this.process.stderr.setEncoding('utf8').on('data', log);
        this.process.stdin.on('error', error => this.fail(error));
        this.process.once('error', error => this.fail(error));
        this.process.once('close', (code, signal) =>
            this.fail(new Error('LoL server exited (' + (signal || code) + ').')));
    }

    fail(error) {
        this.closed = true;
        this.rejectReady(error);
        for (const waiter of this.pending.values()) waiter.reject(error);
        this.pending.clear();
    }

    async request(method, fields = {}) {
        await this.ready;
        if (this.closed) throw new Error('The LoL server is closed.');
        const id = this.nextId++;
        const line = JSON.stringify({ protocol: 2, id, method, ...fields });
        if (Buffer.byteLength(line, 'utf8') > this.limit) throw new Error('Request exceeds the LoL server byte limit.');
        const reply = new Promise((resolve, reject) => this.pending.set(id, { resolve, reject }));
        if (method === 'next') this.activeNext = id;
        try {
            this.process.stdin.write(line + '\n');
            return await reply;
        } finally {
            if (method === 'next') this.activeNext = null;
        }
    }

    async cancel() {
        if (this.activeNext !== null) return this.request('cancel', { target: this.activeNext });
    }

    async stop() {
        // Stop also works while the executable is still starting or a tactic cannot be interrupted.
        const timer = setTimeout(() => this.process.kill(), 1500);
        try {
            if (!this.closed) await this.request('shutdown');
            await this.exit;
        } catch {
            this.process.kill();
        } finally {
            clearTimeout(timer);
        }
    }
}

class Source {
    constructor(text) {
        this.text = text;
        this.lines = [0];
        for (let i = text.indexOf('\n'); i >= 0; i = text.indexOf('\n', i + 1)) this.lines.push(i + 1);
    }

    // Server columns count Unicode scalars. VS Code offsets count UTF-16 code units.
    offset(position, includeCharacter = false) {
        const line = Math.max(0, position.line - 1);
        let i = this.lines[line] ?? this.text.length;
        const end = line + 1 < this.lines.length ? this.lines[line + 1] - 1 : this.text.length;
        const count = position.column - 1 + Number(includeCharacter);
        for (let column = 0; column < count && i < end; column++) {
            i += this.text.codePointAt(i) > 0xffff ? 2 : 1;
        }
        return i;
    }

    cursorTarget(cursor) {
        let offset = Math.min(Math.max(0, cursor), this.text.length);
        if (offset < this.text.length && !' \t\r\n'.includes(this.text[offset])) return offset + 1;
        while (offset > 0 && ' \t\r\n'.includes(this.text[offset - 1])) offset--;
        return offset;
    }
}

function firstDifference(a, b) {
    const size = Math.min(a.length, b.length);
    let offset = 0;
    while (offset < size && a.charCodeAt(offset) === b.charCodeAt(offset)) offset++;
    return offset;
}

function splitSource(text, limit, fields) {
    const overhead = Buffer.byteLength(JSON.stringify(fields)) + 256;
    if (Buffer.byteLength(JSON.stringify(text)) + overhead <= limit) return [text];
    // Even a control character takes at most six JSON bytes per UTF-16 code unit.
    const width = Math.floor((limit - overhead) / 6);
    if (width < 2) throw new Error('The document path exceeds the request size limit.');
    const chunks = [];
    for (let i = 0; i < text.length;) {
        let end = Math.min(i + width, text.length);
        const tail = text.charCodeAt(end - 1);
        if (tail >= 0xd800 && tail <= 0xdbff && end < text.length) end--;
        chunks.push(text.slice(i, end));
        i = end;
    }
    return chunks;
}

class ReplyError extends Error {
    constructor(reply) {
        super(reply.error.message);
        this.reply = reply;
    }
}

class Session {
    constructor(server, path) {
        this.server = server;
        this.path = path;
        this.source = new Source('');
        this.ref = null;
        this.history = new Map();
        this.ends = [0];
        this.reply = null;
        this.output = [];
    }

    accept(reply) {
        if (reply.document !== undefined) {
            this.ref = { document: reply.document, incarnation: reply.incarnation, revision: reply.revision, state: reply.state };
            this.reply = reply;
            this.offset = this.source.offset(reply.position.from);
            const retained = new Set(reply.retainedStates);
            for (const state of this.history.keys()) if (!retained.has(state)) this.history.delete(state);
            this.history.set(reply.state, this.offset);
        }
        if (reply.status === 'error') throw new ReplyError(reply);
        return reply;
    }

    async send(method, fields) {
        return this.accept(await this.server.request(method, { ...this.ref, ...fields }));
    }

    async open(source) {
        await this.server.ready;
        this.history.clear();
        this.output = [];
        this.ends = [0];
        const body = { document: 'editor', revision: 1, path: this.path };
        const parts = splitSource(source.text, this.server.limit, body);
        this.source = source;
        this.accept(await this.server.request('open', { ...body, source: parts[0] }));
        await this.appendParts(parts);
    }

    async appendParts(parts) {
        for (const part of parts.slice(1)) {
            await this.send('append', { nextRevision: this.ref.revision + 1, source: part });
        }
    }

    async reopen(source) {
        if (this.ref) await this.send('close');
        this.ref = null;
        await this.open(source);
    }

    async rewind(limit) {
        if (this.offset <= limit) return;
        const candidates = [...this.history.entries()].filter(([, offset]) => offset <= limit);
        candidates.sort((a, b) => b[1] - a[1] || b[0] - a[0]);
        for (const [state] of candidates) {
            try {
                await this.send('undo', { target: state });
                this.output = [];
                return;
            } catch (e) {
                if (!['P-ExpiredState', 'P-Restore', 'P-ProofClosed'].includes(e.reply?.error.code)) throw e;
            }
        }
        await this.reopen(this.source);
    }

    async sync(text) {
        if (text.length > 524288) {
            let count = 0;
            for (const _ of text) if (++count > 524288) throw new Error('LoL documents are limited to 524,288 Unicode scalars.');
        }
        if (!this.ref) return this.open(new Source(text));
        if (text === this.source.text) return;
        const old = this.source;
        const source = new Source(text);
        let boundary = firstDifference(old.text, text);
        // Editing whitespace just after a final dot can merge a formerly executed token.
        if (text[boundary - 1] === '.' && text[boundary] && !' \t\r\n'.includes(text[boundary])) boundary--;
        await this.rewind(boundary);
        this.ends = this.ends.filter(end => end <= boundary);
        const suffix = text.slice(this.offset);
        const fields = { ...this.ref, nextRevision: this.ref.revision + 1 };
        const parts = splitSource(suffix, this.server.limit, fields);
        await this.send('replace', { nextRevision: fields.nextRevision, source: parts[0] });
        this.source = source;
        try {
            await this.appendParts(parts);
        } catch (e) {
            // A partial multi-frame edit must never be mistaken for the whole buffer.
            await this.reopen(source);
        }
        this.output = [];
    }

    async next() {
        const result = await this.send('next');
        this.output = result.output || [];
        if (this.offset > this.ends[this.ends.length - 1]) this.ends.push(this.offset);
        return result;
    }

    async toCursor(cursor, current = () => true) {
        const target = this.source.cursorTarget(cursor);
        // Repeated views of a command use its ending checkpoint when we know it.
        if (target < this.offset) {
            // Only offsets are kept for old commands, never the term graphs. The server
            // supplies every boundary, including those introduced by dynamic notation.
            let low = 0;
            let high = this.ends.length - 1;
            while (low < high) {
                const middle = Math.floor((low + high) / 2);
                if (this.ends[middle] < target) low = middle + 1;
                else high = middle;
            }
            await this.rewind(this.ends[low]);
        }
        while (this.offset < target && current()) {
            const before = this.offset;
            const reply = await this.next();
            if (reply.atEnd || this.offset <= before) break;
        }
        if (current()) await this.send('show');
        return this.reply;
    }

    async previous(current = () => true) {
        const index = this.ends.indexOf(this.offset);
        if (index <= 0) return this.reply;
        const previous = this.ends[index - 1];
        await this.rewind(previous);
        while (this.offset < previous && current()) {
            const reply = await this.next();
            if (reply.atEnd) break;
        }
        return this.reply;
    }
}

module.exports = { Server, Source, Session, ReplyError, splitSource };
