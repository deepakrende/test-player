// IPTV Player: production server (Node 18+). Serves the player and a hardened stream proxy.
// Env: PORT, ADMIN_PASSWORD (turns on /admin to manage member access codes), DATA_DIR (Render Disk mount path where members are saved), SESSION_SECRET, ACCESS_CODES (optional first import), ACCESS_PASSWORD (old single password, only used when there is no admin and no members), TRUST_PROXY=1 (Caddy/nginx) or render, RATE_LIMIT, MAX_STREAMS_PER_IP, ALLOW_INSECURE_TLS=1
const http = require('http'), https = require('https'), fs = require('fs'), path = require('path');
const dns = require('dns'), net = require('net'), crypto = require('crypto'), zlib = require('zlib');

const PORT = +process.env.PORT || 8787;
const PASS = process.env.ACCESS_PASSWORD || '';
const TRUST_MODE = process.env.TRUST_PROXY || '';   // '1' = Caddy/nginx, 'render' = Render
const TRUST = TRUST_MODE === '1';
const RATE = +process.env.RATE_LIMIT || 900;            // proxy requests per minute per IP
const MAX_CONC = +process.env.MAX_STREAMS_PER_IP || 8;  // simultaneous open streams per IP
const INSECURE = process.env.ALLOW_INSECURE_TLS === '1';
const MAX_PLAYLIST = 80 * 1024 * 1024;
const UA = 'VLC/3.0.18 LibVLC/3.0.18';
const agents = { 'http:': new http.Agent({ keepAlive: true, maxSockets: 200 }), 'https:': new https.Agent({ keepAlive: true, maxSockets: 200 }) };
const px = u => '/proxy?u=' + encodeURIComponent(u);
/* ---- diagnostics: everything below only writes to the log, never changes what is streamed ---- */
const maskUrl = t => { try { const x = new URL(t); return x.host + x.pathname.replace(/\/(live|movie|series|timeshift)\/[^\/]+\/[^\/]+\//i, '/$1/***/***/'); } catch { return '?'; } };
const STYPE = { 0x01: 'mpeg1-video', 0x02: 'mpeg2-video', 0x03: 'mp2-audio', 0x04: 'mp2-audio', 0x0f: 'aac', 0x11: 'aac-latm', 0x1b: 'h264', 0x24: 'HEVC(h265)', 0x42: 'avs', 0x81: 'ac3', 0x82: 'dts', 0x87: 'eac3', 0x86: 'dts-hd', 0x15: 'metadata' };
function sniffTS(b) {   // reads the PAT/PMT tables to list the streams (video/audio codecs) inside an MPEG-TS chunk
  if (!b.length) return 'empty';
  let o = b.indexOf(0x47); if (o < 0) return 'not MPEG-TS (first bytes: ' + b.slice(0, 16).toString('latin1').replace(/[^\x20-\x7e]/g, '.') + ')';
  let pmt = -1; const out = [];
  for (; o + 188 <= b.length; o += 188) {
    if (b[o] !== 0x47) return 'TS sync lost';
    const pid = ((b[o + 1] & 0x1f) << 8) | b[o + 2], pusi = b[o + 1] & 0x40, afc = (b[o + 3] >> 4) & 3;
    if (!pusi || !(afc & 1)) continue;
    let q = o + 4; if (afc & 2) q += 1 + b[o + 4];
    const sec = q + 1 + b[q];
    if (pid === 0 && pmt < 0) { const len = ((b[sec + 1] & 0x0f) << 8) | b[sec + 2]; for (let i = sec + 8; i + 4 <= sec + 3 + len - 4 && i + 4 <= o + 188; i += 4) { const prog = (b[i] << 8) | b[i + 1]; if (prog) { pmt = ((b[i + 2] & 0x1f) << 8) | b[i + 3]; break; } } }
    else if (pid === pmt && b[sec] === 2) {
      const len = ((b[sec + 1] & 0x0f) << 8) | b[sec + 2], pil = ((b[sec + 10] & 0x0f) << 8) | b[sec + 11], end = Math.min(sec + 3 + len - 4, o + 188);
      for (let i = sec + 12 + pil; i + 5 <= end;) {
        const t = b[i], esl = ((b[i + 3] & 0x0f) << 8) | b[i + 4]; let name = STYPE[t] || ('type 0x' + t.toString(16));
        if (t === 0x06) { name = 'private'; for (let d = i + 5; d + 2 <= i + 5 + esl; d += 2 + b[d + 1]) { const tag = b[d]; if (tag === 0x6a) name = 'ac3'; else if (tag === 0x7a) name = 'eac3'; else if (tag === 0x7b) name = 'dts'; else if (tag === 0x56) name = 'teletext'; else if (tag === 0x59) name = 'subtitles'; } }
        out.push(name); i += 5 + esl;
      }
      return out.join(' + ') || 'no streams in PMT';
    }
  }
  return pmt < 0 ? 'PAT not found in first chunk' : 'PMT not found in first chunk';
}
function sniffStream(r, tag) {   // peeks at the first ~48 KB of a stream and logs the codecs; does not consume or alter the data
  const ch = []; let n = 0;
  const f = c => { ch.push(c); n += c.length; if (n >= 49152) { r.removeListener('data', f); console.log('[' + tag + '] codecs: ' + sniffTS(Buffer.concat(ch))); } };
  r.on('data', f);
  r.once('close', () => { if (n < 49152) { r.removeListener('data', f); if (n) console.log('[' + tag + '] codecs (short stream, ' + n + ' bytes): ' + sniffTS(Buffer.concat(ch))); } });
}

const CSP = "default-src 'self'; script-src 'self' 'unsafe-inline' https://cdnjs.cloudflare.com https://cdn.jsdelivr.net; " +
  "style-src 'self' 'unsafe-inline' https://fonts.googleapis.com; font-src https://fonts.gstatic.com; img-src * data:; media-src 'self' blob:; connect-src 'self'; worker-src 'self' blob:; " +
  "frame-ancestors 'none'; base-uri 'none'";
const SEC = { 'Content-Security-Policy': CSP, 'X-Content-Type-Options': 'nosniff', 'Referrer-Policy': 'no-referrer', 'X-Frame-Options': 'DENY' };

/* ---- block requests to private / internal addresses (SSRF protection) ---- */
function isPrivate(ip) {
  if (net.isIPv4(ip)) {
    const [a, b] = ip.split('.').map(Number);
    return a === 0 || a === 10 || a === 127 || (a === 169 && b === 254) || (a === 172 && b >= 16 && b <= 31) ||
      (a === 192 && b === 168) || (a === 100 && b >= 64 && b <= 127) || a >= 224;
  }
  const x = ip.toLowerCase();
  if (x === '::1' || x === '::') return true;
  if (x.startsWith('::ffff:')) { const v4 = x.slice(7); return net.isIPv4(v4) ? isPrivate(v4) : true; }
  return /^f[cd]/.test(x) || /^fe[89ab]/.test(x);
}
// Checked at connection time, so DNS rebinding cannot swap in an internal address.
function safeLookup(host, opts, cb) {
  dns.lookup(host, { ...opts, all: true }, (err, addrs) => {
    if (err) return cb(err);
    const ok = addrs.filter(a => !isPrivate(a.address));
    if (!ok.length) return cb(new Error('Blocked address'));
    if (opts.all) return cb(null, ok);
    cb(null, ok[0].address, ok[0].family);
  });
}
function upstream(target, headers, signal, hops = 0) {
  return new Promise((resolve, reject) => {
    let u; try { u = new URL(target); } catch { return reject(new Error('Bad url')); }
    if (!/^https?:$/.test(u.protocol)) return reject(new Error('Bad url'));
    const host = u.hostname.replace(/^\[|\]$/g, '');
    if (net.isIP(host) && isPrivate(host)) return reject(new Error('Blocked address'));
    const lib = u.protocol === 'https:' ? https : http;
    const req = lib.request(u, { method: 'GET', headers, lookup: safeLookup, timeout: 30000, agent: agents[u.protocol], rejectUnauthorized: !INSECURE }, res => {
      if ([301, 302, 303, 307, 308].includes(res.statusCode) && res.headers.location) {
        res.resume();
        if (hops >= 5) return reject(new Error('Too many redirects'));
        return resolve(upstream(new URL(res.headers.location, u).href, headers, signal, hops + 1));
      }
      res.finalUrl = u.href; resolve(res);
    });
    req.on('timeout', () => req.destroy(new Error('Upstream timeout')));
    req.on('error', reject);
    if (signal.aborted) req.destroy();
    else { const onAbort = () => req.destroy(); signal.addEventListener('abort', onAbort, { once: true }); req.on('close', () => signal.removeEventListener('abort', onAbort)); }
    req.end();
  });
}

/* ---- live MPEG-TS keep-alive ----
   Some Xtream panels close a live .ts connection every ~30s. Instead of letting the browser see the
   break (and freeze while it reconnects), reconnect to the provider here and keep feeding the SAME
   response to the browser, cutting only on whole 188-byte TS packets so the stream stays valid. */

/* ---- start-on-keyframe gate ----
   A live .ts joined in the middle of a GOP (first connect, and every reconnect) starts with P/B frames whose reference
   frames are missing. VLC hides that, Chrome's decoder aborts with PIPELINE_ERROR_DECODE. This drops everything until the
   first H.264 IDR picture, then re-sends PAT+PMT in front of it so the stream is valid from byte 0.
   If no IDR shows up within GATE_MAX_SKIP bytes (intra-refresh streams), it opens on the next video PES anyway. */
const IDR_GATE = process.env.IDR_GATE !== '0';
const GATE_MAX_SKIP = 12 * 1024 * 1024;
class TsGate {
  constructor() { this.reset(); }
  reset() { this.open = false; this.vpid = -1; this.pmtPid = -1; this.pat = null; this.pmt = null; this.held = []; this.parts = []; this.skipped = 0; this.reason = ''; }
  /* what this video PES contains: IDR slice, SPS, and a recovery-point SEI (payload type 6) */
  static scan(buf) {
    const r = { idr: false, sps: false, rp: false };
    for (let i = 0; i + 4 < buf.length; i++) {
      if (buf[i] === 0 && buf[i + 1] === 0 && buf[i + 2] === 1) {
        const t = buf[i + 3] & 0x1f;
        if (t === 5) r.idr = true;
        else if (t === 7) r.sps = true;
        else if (t === 6) {                       // SEI: walk its messages looking for payloadType 6
          let j = i + 4;
          for (let m = 0; m < 8 && j + 2 < buf.length; m++) {
            let pt = 0; while (buf[j] === 0xff && j < buf.length) { pt += 255; j++; } pt += buf[j++];
            let sz = 0; while (buf[j] === 0xff && j < buf.length) { sz += 255; j++; } sz += buf[j++];
            if (pt === 6) { r.rp = true; break; }
            j += sz; if (buf[j] === 0x80 || (buf[j] === 0 && buf[j + 1] === 0)) break;
          }
        }
        i += 2;
      }
    }
    return r;
  }
  feed(chunk) {
    if (this.open) return chunk;
    const out = []; let next = -1;
    for (let o = 0; o + 188 <= chunk.length && !this.open; o += 188) {
      const p = chunk.subarray(o, o + 188);
      if (p[0] !== 0x47) continue;
      const pid = ((p[1] & 0x1f) << 8) | p[2], pusi = !!(p[1] & 0x40), afc = (p[3] >> 4) & 3;
      let off = 4; if (afc & 2) off += 1 + p[4];
      const pl = (afc & 1) && off < 188 ? p.subarray(off) : Buffer.alloc(0);
      if (pid === 0 && pusi && pl.length > 12) {
        this.pat = Buffer.from(p);
        const sec = pl.subarray(1 + pl[0]), end = 3 + (((sec[1] & 0xf) << 8) | sec[2]) - 4;
        for (let i = 8; i + 4 <= end && i + 4 <= sec.length; i += 4) { if ((sec[i] << 8 | sec[i + 1]) !== 0) { this.pmtPid = ((sec[i + 2] & 0x1f) << 8) | sec[i + 3]; break; } }
      } else if (pid === this.pmtPid && pusi) this.pmt = Buffer.from(p);
      if (this.vpid < 0 && pusi && pl.length > 3 && pl[0] === 0 && pl[1] === 0 && pl[2] === 1 && (pl[3] & 0xf0) === 0xe0) this.vpid = pid;
      if (pid === this.vpid && pusi) {
        let ok = false;
        if (this.held.length) {
          const f = TsGate.scan(Buffer.concat(this.parts));
          if (f.idr) { ok = true; this.reason = 'IDR'; }
          else if (f.sps && f.rp) { ok = true; this.reason = 'recovery point'; }
          else if (f.sps && this.skipped > GATE_MAX_SKIP) { ok = true; this.reason = 'no IDR/recovery, SPS only'; }
          else if (this.skipped > GATE_MAX_SKIP * 4) { ok = true; this.reason = 'forced'; }
        }
        if (ok) {
          this.open = true;
          if (this.pat) out.push(this.pat); if (this.pmt) out.push(this.pmt);
          for (const h of this.held) out.push(h); out.push(Buffer.from(p));
          this.held = []; this.parts = []; next = o + 188;
        } else { this.skipped += this.held.length * 188; this.held = [Buffer.from(p)]; this.parts = [pl]; }
      } else if (this.held.length) { this.held.push(Buffer.from(p)); if (pid === this.vpid) this.parts.push(pl); }
      else this.skipped += 188;
    }
    if (next >= 0 && next < chunk.length) out.push(chunk.subarray(next));
    return out.length ? Buffer.concat(out) : null;
  }
}

const LIVE_TS = /\/live\/[^/]+\/[^/]+\/\d+\.ts$/i;
const sleep = ms => new Promise(r => setTimeout(r, ms));
async function pumpLive(res, first, target, hd, signal, tx) {
  /* tx=true: pass the stream through ffmpeg, copying video and converting audio (AC-3/E-AC-3/MP2...) to AAC,
     because browsers cannot decode Dolby audio. Used only when the player asks for it. */
  let out = res, ff = null;
  if (tx) {
    const { spawn } = require('child_process');
    const common = ['-hide_banner', '-loglevel', 'warning', '-fflags', '+genpts+discardcorrupt', '-probesize', '1000000', '-analyzeduration', '1500000', '-i', 'pipe:0', '-map', '0:v:0?', '-map', '0:a:0?'];
    const tail = ['-c:a', 'aac', '-b:a', '128k', '-ac', '2', '-f', 'mpegts', '-muxdelay', '0', '-flush_packets', '1', 'pipe:1'];
    // tx=1: copy video, convert audio.  tx=2 (repair): decode with error concealment, deinterlace, re-encode to <=720p H.264 so a damaged/interlaced source plays in Chrome. Needs real CPU (~0.5 core).
    const vargs = tx === 2
      ? ['-vf', "yadif=0:-1:1,scale=-2:'min(720,ih)'", '-c:v', 'libx264', '-preset', 'ultrafast', '-tune', 'zerolatency', '-profile:v', 'main', '-pix_fmt', 'yuv420p', '-crf', '27', '-maxrate', '3500k', '-bufsize', '3500k', '-g', '50', '-sc_threshold', '0', '-af', 'aresample=async=1:first_pts=0']
      : ['-c:v', 'copy'];
    ff = spawn('ffmpeg', [...common, ...vargs, ...tail], { stdio: ['pipe', 'pipe', 'pipe'] });
    out = ff.stdin;
    ff.stdin.on('error', () => {});
    let errLines = 0, errSupp = 0; ff.stderr.on('data', d => { if (errLines < 6) { errLines++; console.log('[ffmpeg] ' + String(d).trim().slice(0, 300)); } else errSupp++; });
    console.log('[ffmpeg] started ' + (tx === 2 ? 'REPAIR re-encode (deinterlace + 720p)' : 'audio conversion') + ' for ' + maskUrl(target));
    let ffOut = 0; const ffT0 = Date.now();
    ff.stdout.on('data', c => { if (!ffOut) console.log('[ffmpeg] first output after ' + (Date.now() - ffT0) + 'ms'); ffOut += c.length; if (!res.write(c)) { ff.stdout.pause(); res.once('drain', () => ff.stdout.resume()); } });
    ff.on('error', e => { console.log('[ffmpeg] cannot start: ' + e.message); res.end(); });
    ff.on('close', (code, sig) => { console.log('[ffmpeg] exited code=' + code + ' signal=' + sig + ' output=' + Math.round(ffOut / 1024) + ' KB' + (errSupp ? ' (' + errSupp + ' more warning chunks hidden: source stream is damaged)' : '')); if (!res.writableEnded) res.end(); });
    res.on('close', () => { try { ff.kill('SIGKILL'); } catch {} });
  }
  const host = (() => { try { return new URL(target).host; } catch { return '?'; } })();
  const headers = { ...hd }; delete headers.Range;
  let r = first, quick = 0, reconnects = 0, lastUrl = first.finalUrl, cachedOk = true, usedCached = false, lastMs = 0;
  const gate = new TsGate(); let wasOpen = false;
  const st = { inB: 0, outB: 0, pausedMs: 0, ps: 0, t: Date.now() };
  const tick = setInterval(() => { const dt = (Date.now() - st.t) / 1000; if (st.ps) { st.pausedMs += Date.now() - st.ps; st.ps = Date.now(); }
    console.log('[live] ' + dt.toFixed(0) + 's: provider->server ' + Math.round(st.inB / 1024 / dt) + ' KB/s, server->browser ' + Math.round(st.outB / 1024 / dt) + ' KB/s, waiting on browser ' + Math.round(st.pausedMs / 10 / dt) + '%');
    st.inB = st.outB = st.pausedMs = 0; st.t = Date.now(); }, 10000);
  res.once('close', () => clearInterval(tick));
  for (;;) {
    gate.reset(); wasOpen = false;
    const t0 = Date.now(); let got = 0, carry = Buffer.alloc(0), why = 'end';
    await new Promise(resolve => {
      r.on('data', c => {
        got += c.length; st.inB += c.length;
        const buf = carry.length ? Buffer.concat([carry, c]) : c;
        const n = buf.length - (buf.length % 188);
        carry = buf.subarray(n);
        const piece = n ? (IDR_GATE ? gate.feed(buf.subarray(0, n)) : buf.subarray(0, n)) : null;
        if (IDR_GATE && !wasOpen && gate.open) { wasOpen = true; console.log('[live] started on keyframe (' + gate.reason + '), skipped ' + Math.round(gate.skipped / 1024) + ' KB'); }
        if (piece && piece.length) { st.outB += piece.length; if (!out.write(piece)) { r.pause(); if (!st.ps) st.ps = Date.now(); out.once('drain', () => { if (st.ps) { st.pausedMs += Date.now() - st.ps; st.ps = 0; } r.resume(); }); } }
      });
      r.on('end', resolve);
      r.on('error', e => { why = 'error: ' + e.message; resolve(); });
      r.on('close', () => { if (why === 'end') why = 'close'; resolve(); });
    });
    if (signal.aborted || res.destroyed) return;
    const secs = Math.round((Date.now() - t0) / 100) / 10;
    console.log('[live] provider ended stream host=' + host + ' after ' + secs + 's, ' + got + ' bytes (' + why + '); last reconnect took ' + lastMs + 'ms; reconnect #' + (reconnects + 1));
    if (got < 188 * 20 || secs < 3) { quick++; if (usedCached) cachedOk = false; } else quick = 0;
    if (quick >= 4 || ++reconnects > 2000) break;
    if (quick) await sleep(400 * quick);
    if (signal.aborted || res.destroyed) return;
    const tc = Date.now();
    try {
      usedCached = false;
      if (cachedOk && lastUrl) {
        try { r = await upstream(lastUrl, headers, signal); usedCached = true; if (r.statusCode !== 200) { r.resume(); usedCached = false; cachedOk = false; r = null; } }
        catch { cachedOk = false; r = null; }
      } else r = null;
      if (!r) r = await upstream(target, headers, signal);
      if (r.statusCode !== 200) { r.resume(); quick++; if (quick >= 4) break; r = emptyStream(); }
      else lastUrl = r.finalUrl;
    } catch (e) { quick++; if (quick >= 4) break; r = emptyStream(); }
    lastMs = Date.now() - tc;
  }
  if (ff) ff.stdin.end(); else res.end();
}
function emptyStream() { const { Readable } = require('stream'); const s = new Readable({ read() {} }); s.push(null); return s; }

function rewrite(text, base, sfx = '') {
  return text.split(/\r?\n/).map(l => {
    const t = l.trim();
    if (!t) return l;
    if (t[0] === '#') return l.replace(/URI="([^"]+)"/g, (m, u) => { try { return 'URI="' + px(new URL(u, base).href) + sfx + '"'; } catch { return m; } });
    try { return px(new URL(t, base).href) + sfx; } catch { return l; }
  }).join('\n');
}

/* ---- limits and auth ---- */
const hits = new Map(), conc = new Map();
setInterval(() => { const n = Date.now(); for (const [k, v] of hits) if (v.reset < n) hits.delete(k); }, 60000).unref();
const clientIp = req => {
  if (TRUST_MODE === 'render') {
    const h = req.headers['true-client-ip'] || req.headers['cf-connecting-ip'];
    if (h) return String(h).trim();
    const f = (req.headers['x-forwarded-for'] || '').split(',')[0].trim();
    if (f) return f;
  }
  if (TRUST) { const x = (req.headers['x-forwarded-for'] || '').split(',').map(s => s.trim()).filter(Boolean); if (x.length) return x[x.length - 1]; }
  return req.socket.remoteAddress || '';
};
function authed(req) {
  if (!PASS) return true;
  const m = /^Basic (.+)$/.exec(req.headers.authorization || '');
  if (!m) return false;
  const given = Buffer.from(m[1], 'base64').toString().split(':').slice(1).join(':');
  const a = crypto.createHash('sha256').update(given).digest(), b = crypto.createHash('sha256').update(PASS).digest();
  return crypto.timingSafeEqual(a, b);
}
const fail = (res, code, msg) => { if (!res.headersSent) res.writeHead(code, { ...SEC, 'Content-Type': 'text/plain' }); res.end(msg); };


/* ================= Member access codes, managed from /admin =================
   Members are saved in DATA_DIR/members.json. Attach a Render Disk and set DATA_DIR to its mount path so they survive deploys.
   ADMIN_PASSWORD turns the admin page on (/admin). ACCESS_CODES is optional and only used to import a first list. */
const DATA_DIR = process.env.DATA_DIR || '';
const ADMIN_PASSWORD = process.env.ADMIN_PASSWORD || '';
const DEFAULT_DEVICES = +process.env.DEFAULT_DEVICES || 3;
const SECRET = process.env.SESSION_SECRET || crypto.randomBytes(32).toString('hex');
const ALPHA = 'ABCDEFGHJKLMNPQRSTUVWXYZ23456789';
const normCode = s => String(s || '').toUpperCase().replace(/[^A-Z0-9]/g, '');
const hashCode = code => crypto.createHash('sha256').update(normCode(code)).digest();
const fpOf = code => hashCode(code).toString('hex').slice(0, 16);
const expOf = m => m.expires == null ? Infinity : m.expires;
const newId = () => crypto.randomBytes(4).toString('hex');
function genCode() { const b = crypto.randomBytes(12); let c = ''; for (const x of b) c += ALPHA[x % ALPHA.length]; return c.slice(0, 4) + '-' + c.slice(4, 8) + '-' + c.slice(8, 12); }
function parseExpiry(x) {                       // 'YYYY-MM-DD' = through the end of that day, India time. Empty = never.
  if (!x) return null;
  if (/^\d{4}-\d{2}-\d{2}$/.test(x)) return Date.parse(x + 'T23:59:59+05:30');
  return Date.parse(x);
}
const clean = m => ({
  id: m.id || newId(), name: String(m.name || '').replace(/[\u0000-\u001f]/g, ' ').trim().slice(0, 60), code: String(m.code || '').toUpperCase().replace(/[^A-Z0-9-]/g, ''),
  expires: m.expires == null || Number.isNaN(+m.expires) ? null : +m.expires, paused: !!m.paused,
  devices: +m.devices > 0 ? Math.floor(+m.devices) : DEFAULT_DEVICES, screens: +m.screens > 0 ? Math.floor(+m.screens) : 1,
  note: String(m.note || '').slice(0, 200), epoch: +m.epoch || 0, createdAt: +m.createdAt || Date.now(), lastSeenAt: +m.lastSeenAt || 0
});
function parseCodes(raw) {                      // optional first import from ACCESS_CODES: name:code:expiry[:devices[:screens]] (use | to give a time)
  const list = [];
  for (const part of String(raw || '').split(/[\n;,]+/)) {
    const t = part.trim(); if (!t) continue;
    const [name, code, exp, dev, scr] = t.split(t.includes('|') ? '|' : ':').map(x => x.trim());
    const expires = parseExpiry(exp);
    if (!name || normCode(code).length < 8 || Number.isNaN(expires)) { console.log('[access] skipped an ACCESS_CODES entry that could not be read'); continue; }
    list.push(clean({ name, code, expires, devices: dev, screens: scr }));
  }
  return list;
}

let STORE = { members: [], usage: {}, daily: {}, hourly: {}, titles: {}, peak: {} };
const storeInfo = { persistent: false, mounted: false, dir: DATA_DIR, error: '' };
const STORE_FILE = DATA_DIR ? path.join(DATA_DIR, 'members.json') : '';
let BYFP = new Map(), HASHES = [], usageDirty = false;
const DEVICES = new Map();   // fp -> Map(deviceId -> lastSeen)
const STREAMS = new Map();   // fp -> Map(deviceId -> open stream count)
const OPEN = new Map();      // fp -> Set(open response objects), so a stream can be cut when access ends
const tries = new Map(), atries = new Map();   // wrong-password attempts per IP
function rebuild() {
  BYFP = new Map(); HASHES = [];
  for (const m of STORE.members) { m.fp = fpOf(m.code); BYFP.set(m.fp, m); HASHES.push({ hash: hashCode(m.code), m }); }
}
function saveStore() {
  if (!storeInfo.persistent) return false;
  try {
    const cut = istDay(Date.now() - 120 * 86400000);
    for (const id of Object.keys(STORE.usage)) { for (const d of Object.keys(STORE.usage[id])) if (d < cut) delete STORE.usage[id][d]; }
    const cutD = istDay(Date.now() - 120 * 86400000), cutT = istDay(Date.now() - 45 * 86400000);
    for (const k of ['daily', 'hourly', 'peak']) for (const d of Object.keys(STORE[k])) if (d < cutD) delete STORE[k][d];
    for (const d of Object.keys(STORE.titles)) {
      if (d < cutT) { delete STORE.titles[d]; continue; }
      const ks = Object.keys(STORE.titles[d]);
      if (ks.length > 400) { ks.sort((a, b) => STORE.titles[d][b][1] - STORE.titles[d][a][1]); for (const k of ks.slice(300)) delete STORE.titles[d][k]; }
    }
    const data = { version: 1, members: STORE.members.map(m => clean(m)), usage: STORE.usage, daily: STORE.daily, hourly: STORE.hourly, titles: STORE.titles, peak: STORE.peak };
    fs.writeFileSync(STORE_FILE + '.tmp', JSON.stringify(data)); fs.renameSync(STORE_FILE + '.tmp', STORE_FILE);
    usageDirty = false; storeInfo.error = ''; return true;
  } catch (e) { storeInfo.error = e.message; console.log('[admin] could not save members: ' + e.message); return false; }
}
function loadStore() {
  if (DATA_DIR) {
    try {
      fs.mkdirSync(DATA_DIR, { recursive: true }); fs.accessSync(DATA_DIR, fs.constants.W_OK);
      storeInfo.persistent = true;
      try { storeInfo.mounted = fs.statSync(DATA_DIR).dev !== fs.statSync('/').dev; } catch {}
      if (fs.existsSync(STORE_FILE)) {
        const j = JSON.parse(fs.readFileSync(STORE_FILE, 'utf8'));
        STORE = { members: (j.members || []).map(clean).filter(m => m.name && normCode(m.code).length >= 8), usage: j.usage || {}, daily: j.daily || null, hourly: j.hourly || {}, titles: j.titles || {}, peak: j.peak || {} };
        if (!STORE.daily) { STORE.daily = {}; for (const u of Object.values(STORE.usage)) for (const [d, v] of Object.entries(u)) STORE.daily[d] = (STORE.daily[d] || 0) + v; }   // history from before Insights existed
        rebuild(); return;
      }
    } catch (e) { storeInfo.persistent = false; storeInfo.error = e.message; console.log('[admin] cannot use DATA_DIR (' + DATA_DIR + '): ' + e.message); }
  }
  STORE = { members: parseCodes(process.env.ACCESS_CODES), usage: {}, daily: {}, hourly: {}, titles: {}, peak: {} };
  rebuild(); if (storeInfo.persistent && STORE.members.length) saveStore();
}
const istDay = (t = Date.now()) => new Date(t).toLocaleDateString('en-CA', { timeZone: 'Asia/Kolkata' });
const r2 = x => Math.round(x * 100) / 100;
const istHour = (t = Date.now()) => new Date(t + 19800000).getUTCHours();
const METERS = new Set(), VIEWS = new Map();
function account(m, mb, meta) {
  if (!(mb > 0)) return;
  const now = Date.now(), d = istDay(now), h = istHour(now);
  const u = STORE.usage[m.id] || (STORE.usage[m.id] = {}); u[d] = r2((u[d] || 0) + mb);
  STORE.daily[d] = r2((STORE.daily[d] || 0) + mb);
  const H = STORE.hourly[d] || (STORE.hourly[d] = new Array(24).fill(0)); H[h] = r2(H[h] + mb);
  if (meta && meta.n) { const T = STORE.titles[d] || (STORE.titles[d] = {}), key = meta.k + '|' + meta.n, e = T[key] || (T[key] = [0, 0]); e[1] = r2(e[1] + mb); }
  usageDirty = true;
}
function trackView(w, meta) {          // one "view" = one device starting a title; the same title again within 30 minutes is the same view
  const key = w.entry.fp + '|' + w.device + '|' + meta.k + '|' + meta.n, now = Date.now(), last = VIEWS.get(key);
  VIEWS.set(key, now); if (last && now - last < 30 * 60000) return;
  const T = STORE.titles[istDay(now)] || (STORE.titles[istDay(now)] = {}), k2 = meta.k + '|' + meta.n, e = T[k2] || (T[k2] = [0, 0]); e[0]++; usageDirty = true;
}
setInterval(() => { for (const f of METERS) f(); }, (+process.env.METER_SECONDS || 15) * 1000).unref();
setInterval(() => { const cut = Date.now() - 3600000; for (const [k, t] of VIEWS) if (t < cut) VIEWS.delete(k); }, 600000).unref();
function usageOf(m) {
  const u = STORE.usage[m.id] || {}, today = istDay(), mon = today.slice(0, 7); let t = 0, mo = 0, tot = 0;
  for (const [d, v] of Object.entries(u)) { tot += v; if (d === today) t += v; if (d.startsWith(mon)) mo += v; }
  return { today: Math.round(t), month: Math.round(mo), total: Math.round(tot) };
}
const gateOn = () => !!ADMIN_PASSWORD || STORE.members.length > 0;
const dateStr = ms => ms === Infinity || ms == null ? 'never' : new Date(ms).toLocaleDateString('en-GB', { day: 'numeric', month: 'short', year: 'numeric', timeZone: 'Asia/Kolkata' });
function killMember(fp) { const set = OPEN.get(fp); if (set) for (const r of [...set]) { try { r.destroy(); } catch {} } }
setInterval(() => {            // cut running streams when access ends (expiry, pause, removal)
  for (const fp of OPEN.keys()) { const m = BYFP.get(fp); if (!m || m.paused || Date.now() > expOf(m)) killMember(fp); }
  if (usageDirty) saveStore();
}, 20000).unref();
process.on('SIGTERM', () => { try { for (const f of METERS) f(); saveStore(); } catch {} process.exit(0); });

const sign = obj => { const body = Buffer.from(JSON.stringify(obj)).toString('base64url'); return body + '.' + crypto.createHmac('sha256', SECRET).update(body).digest('base64url'); };
function verify(tok) {
  const i = (tok || '').lastIndexOf('.'); if (i < 1) return null;
  const body = tok.slice(0, i), mac = tok.slice(i + 1), exp = crypto.createHmac('sha256', SECRET).update(body).digest('base64url');
  if (mac.length !== exp.length || !crypto.timingSafeEqual(Buffer.from(mac), Buffer.from(exp))) return null;
  try { return JSON.parse(Buffer.from(body, 'base64url').toString()); } catch { return null; }
}
const cookieOf = (req, name) => { for (const p of (req.headers.cookie || '').split(';')) { const i = p.indexOf('='); if (i > 0 && p.slice(0, i).trim() === name) return decodeURIComponent(p.slice(i + 1).trim()); } return ''; };
const isHttps = req => req.headers['x-forwarded-proto'] === 'https' || !!req.socket.encrypted;
const setCookie = (req, name, val, maxAgeSec, p = '/', strict = false) => name + '=' + encodeURIComponent(val) + '; Path=' + p + '; HttpOnly; SameSite=' + (strict ? 'Strict' : 'Lax') + '; Max-Age=' + maxAgeSec + (isHttps(req) ? '; Secure' : '');
function pruneDevices(devs) { const cut = Date.now() - 14 * 86400000; for (const [d, t] of devs) if (t < cut) devs.delete(d); }

/* returns { entry, device } for a signed-in member, or { error } */
function memberOf(req) {
  const p = verify(cookieOf(req, 'mmn_session'));
  if (!p) return { error: 'login' };
  const e = BYFP.get(p.f);
  if (!e) return { error: 'revoked' };
  if (e.paused) return { error: 'paused', entry: e };
  if (Date.now() > expOf(e)) return { error: 'expired', entry: e };
  if ((p.e | 0) !== (e.epoch | 0)) return { error: 'signedout', entry: e };
  let devs = DEVICES.get(e.fp); if (!devs) DEVICES.set(e.fp, devs = new Map());
  if (!devs.has(p.d)) { pruneDevices(devs); if (devs.size >= e.devices) return { error: 'devices', entry: e }; }
  devs.set(p.d, Date.now());
  { const t = Date.now(); if (!e.lastSeenAt || t - e.lastSeenAt > 300000) { e.lastSeenAt = t; usageDirty = true; } }
  return { entry: e, device: p.d };
}
function streamInc(w, res) { let m = STREAMS.get(w.entry.fp); if (!m) STREAMS.set(w.entry.fp, m = new Map()); m.set(w.device, (m.get(w.device) || 0) + 1); let o = OPEN.get(w.entry.fp); if (!o) OPEN.set(w.entry.fp, o = new Set()); o.add(res);
  let n = 0; for (const mm of STREAMS.values()) for (const c of mm.values()) if (c > 0) n++;
  const d = istDay(); if (n > (STORE.peak[d] || 0)) { STORE.peak[d] = n; usageDirty = true; } }
function streamDec(w, res) { const m = STREAMS.get(w.entry.fp); if (m) { const n = (m.get(w.device) || 1) - 1; n ? m.set(w.device, n) : m.delete(w.device); } const o = OPEN.get(w.entry.fp); if (o) { o.delete(res); if (!o.size) OPEN.delete(w.entry.fp); } }
function otherScreens(w) { const m = STREAMS.get(w.entry.fp); let n = 0; if (m) for (const [d, c] of m) if (d !== w.device && c > 0) n++; return n; }

const WHY = {
  expired: 'Your access code has expired. Enter a new code to continue.',
  revoked: 'Your access was removed. Enter a new code to continue.',
  paused: 'Your access is paused. Please contact the owner.',
  signedout: 'You were signed out. Enter your code to continue.',
  devices: 'This code is already signed in on the maximum number of devices.'
};
function gatePage(why) {
  const note = WHY[why] || '';
  return `<!doctype html><html lang="en"><head><meta charset="utf-8"><meta name="viewport" content="width=device-width, initial-scale=1"><title>MMN · Access</title>
<style>:root{--bg:#0d0f1f;--panel:#161938;--line:#2a2e5c;--text:#eef0ff;--mute:#9aa0d0;--accent:#8b7bff;--err:#ff7a8a}*{box-sizing:border-box}html,body{height:100%;margin:0}
body{background:var(--bg);color:var(--text);font:16px/1.5 system-ui,-apple-system,"Segoe UI",Roboto,sans-serif;display:grid;place-items:center;padding:24px}
main{width:100%;max-width:420px}.logo{display:flex;align-items:center;gap:12px;margin-bottom:26px}.logo i{width:40px;height:40px;border-radius:12px;background:var(--accent);display:grid;place-items:center}
.logo i:after{content:"";border-left:13px solid #fff;border-top:8px solid transparent;border-bottom:8px solid transparent;margin-left:3px}.logo b{font-size:28px}
h1{font-size:22px;margin:0 0 6px}p{color:var(--mute);margin:0 0 18px}input{width:100%;padding:14px 16px;border-radius:12px;border:1px solid var(--line);background:var(--panel);color:var(--text);font:600 18px ui-monospace,Consolas,monospace;letter-spacing:2px;text-transform:uppercase}
input:focus{outline:2px solid var(--accent);outline-offset:2px}button{margin-top:12px;width:100%;padding:14px;border:0;border-radius:12px;background:var(--accent);color:#fff;font:600 16px inherit;cursor:pointer}button:disabled{opacity:.6;cursor:default}
#msg{min-height:1.5em;margin-top:14px;color:var(--err);font-size:14px}small{display:block;margin-top:22px;color:var(--mute)}</style></head><body><main>
<div class="logo"><i></i><b>MMN</b></div><h1>Enter your access code</h1><p>Access is by invitation. Ask the person who invited you for a code.</p>
<form id="f"><input id="c" autocomplete="off" autocapitalize="characters" spellcheck="false" maxlength="40" placeholder="XXXX-XXXX-XXXX" aria-label="Access code" autofocus><button id="b" type="submit">Continue</button></form>
<div id="msg" role="alert">${note}</div><small>Your code is private. Do not share it.</small></main>
<script>const f=document.getElementById('f'),c=document.getElementById('c'),b=document.getElementById('b'),m=document.getElementById('msg');
f.onsubmit=async e=>{e.preventDefault();if(!c.value.trim())return;b.disabled=true;m.textContent='';
try{const r=await fetch('/gate',{method:'POST',headers:{'Content-Type':'application/json'},body:JSON.stringify({code:c.value})});const j=await r.json().catch(()=>({}));
if(r.ok){location.href='/app';return}m.textContent=j.error||'Could not check the code. Try again.'}catch(x){m.textContent='Could not reach the server. Try again.'}b.disabled=false};</script></body></html>`;
}
function readBody(req, max = 8192) {
  return new Promise((resolve, reject) => {
    let n = 0; const ch = [];
    req.on('data', c => { n += c.length; if (n > max) { reject(new Error('too big')); req.destroy(); return; } ch.push(c); });
    req.on('end', () => resolve(Buffer.concat(ch).toString())); req.on('error', reject);
  });
}
function acceptsEnc(req, enc) { return new RegExp('\\b' + enc + '\\b').test(String((req && req.headers['accept-encoding']) || '')); }
function sendJson(res, code, o, extra) {
  const h = { ...SEC, 'Content-Type': 'application/json', 'Cache-Control': 'no-store', ...(extra || {}) };
  let body = Buffer.from(JSON.stringify(o));
  if (body.length > 1024 && acceptsEnc(res.req, 'gzip')) { body = zlib.gzipSync(body, { level: 5 }); h['Content-Encoding'] = 'gzip'; h.Vary = 'Accept-Encoding'; }
  h['Content-Length'] = body.length; res.writeHead(code, h); res.end(body);
}
const STATIC = new Map();   // file -> prepared copy (raw, gzip, brotli, etag); rebuilt only when the file changes
function staticPage(file, transform) {
  const fp = path.join(__dirname, file), st = fs.statSync(fp); let c = STATIC.get(file);
  if (!c || c.mtime !== st.mtimeMs) {
    let raw = fs.readFileSync(fp, 'utf8'); if (transform) raw = transform(raw);
    const buf = Buffer.from(raw);
    c = { mtime: st.mtimeMs, raw: buf, gz: zlib.gzipSync(buf, { level: 9 }), br: zlib.brotliCompressSync(buf, { params: { [zlib.constants.BROTLI_PARAM_QUALITY]: 9 } }), etag: 'W/"' + crypto.createHash('sha1').update(buf).digest('hex').slice(0, 16) + '"' };
    STATIC.set(file, c);
  }
  return c;
}
function sendStatic(req, res, c, type) {
  const h = { ...SEC, 'Content-Type': type, 'Cache-Control': 'no-cache', ETag: c.etag, Vary: 'Accept-Encoding' };
  const inm = String(req.headers['if-none-match'] || '');
  if (inm && inm.split(',').some(x => x.trim() === c.etag)) { res.writeHead(304, h); return res.end(); }
  let body = c.raw;
  if (acceptsEnc(req, 'br')) { body = c.br; h['Content-Encoding'] = 'br'; } else if (acceptsEnc(req, 'gzip')) { body = c.gz; h['Content-Encoding'] = 'gzip'; }
  h['Content-Length'] = body.length; res.writeHead(200, h); res.end(req.method === 'HEAD' ? undefined : body);
}
/* channel lists (get_live_streams ...) are big, rarely change and are asked for again at every visit: keep a compressed copy for a few minutes */
const LIST_TTL = (+process.env.LIST_CACHE_SECONDS || 300) * 1000, LIST_MAX = (+process.env.LIST_CACHE_MB || 80) * 1048576, LIST_RAW_MAX = 64 * 1048576;
const LIST_ACTIONS = new Set(['get_live_categories', 'get_live_streams', 'get_vod_categories', 'get_vod_streams', 'get_series_categories', 'get_series']);
const LISTC = new Map(); let listBytes = 0;
const LIST_HDR = 'private, max-age=' + Math.round(LIST_TTL / 1000) + ', stale-while-revalidate=86400';
function listActionOf(t) { try { const x = new URL(t); return /\/player_api\.php$/i.test(x.pathname) && LIST_ACTIONS.has(x.searchParams.get('action')) ? x.searchParams.get('action') : ''; } catch { return ''; } }
function listGet(key) { const e = LISTC.get(key); if (!e) return null; if (Date.now() - e.t > LIST_TTL) { listBytes -= e.gz.length; LISTC.delete(key); return null; } return e; }
function listSet(key, e) {
  if (e.gz.length > LIST_MAX / 3) return;
  const old = LISTC.get(key); if (old) { listBytes -= old.gz.length; LISTC.delete(key); }
  LISTC.set(key, e); listBytes += e.gz.length;
  for (const [k, v] of LISTC) { if (listBytes <= LIST_MAX) break; listBytes -= v.gz.length; LISTC.delete(k); }
}
setInterval(() => { for (const k of [...LISTC.keys()]) listGet(k); }, 60000).unref();
function sendList(req, res, e) {
  const h = { ...SEC, 'Content-Type': e.ct, 'Cache-Control': LIST_HDR, Vary: 'Accept-Encoding' };
  if (acceptsEnc(req, 'gzip')) { h['Content-Encoding'] = 'gzip'; h['Content-Length'] = e.gz.length; res.writeHead(200, h); return res.end(e.gz); }
  const raw = zlib.gunzipSync(e.gz); h['Content-Length'] = raw.length; res.writeHead(200, h); res.end(raw);
}

async function handleGate(req, res, u) {
  if (!gateOn()) { res.writeHead(302, { Location: '/app' }); return res.end(); }
  if (req.method === 'GET') {
    if (!memberOf(req).error && !u.searchParams.get('why')) { res.writeHead(302, { Location: '/app' }); return res.end(); }
    res.writeHead(200, { ...SEC, 'Content-Type': 'text/html; charset=utf-8', 'Cache-Control': 'no-store' });
    return res.end(gatePage(u.searchParams.get('why') || ''));
  }
  if (req.method !== 'POST') return fail(res, 405, 'GET or POST only');
  const site = req.headers['sec-fetch-site']; if (site && site !== 'same-origin') return fail(res, 403, 'Same-origin requests only');
  const ip = clientIp(req), now = Date.now();
  let t = tries.get(ip); if (!t || t.reset < now) { t = { n: 0, reset: now + 15 * 60000 }; tries.set(ip, t); }
  if (t.n >= 10) return sendJson(res, 429, { error: 'Too many wrong attempts. Please try again in a few minutes.' });
  let code = '';
  try { const raw = await readBody(req); try { code = JSON.parse(raw).code; } catch { code = new URLSearchParams(raw).get('code'); } } catch { return sendJson(res, 400, { error: 'Bad request' }); }
  const h = hashCode(code);
  let found = null; for (const x of HASHES) if (crypto.timingSafeEqual(h, x.hash)) found = x.m;   // checks every code, so timing reveals nothing
  if (!found || !normCode(code)) { t.n++; console.log('[access] wrong code from ' + ip); return sendJson(res, 401, { error: 'That code is not valid.' }); }
  if (found.paused) return sendJson(res, 401, { error: WHY.paused });
  if (Date.now() > expOf(found)) return sendJson(res, 401, { error: 'This code expired on ' + dateStr(found.expires) + '.' });
  let devs = DEVICES.get(found.fp); if (!devs) DEVICES.set(found.fp, devs = new Map());
  pruneDevices(devs);
  const old = verify(cookieOf(req, 'mmn_session'));
  let device = old && old.f === found.fp && (old.e | 0) === (found.epoch | 0) && devs.has(old.d) ? old.d : null;   // same browser signing in again keeps its slot
  if (!device) {
    if (devs.size >= found.devices) { console.log('[access] ' + found.name + ' refused: device limit (' + found.devices + ')'); return sendJson(res, 401, { error: 'This code is already signed in on ' + found.devices + ' device' + (found.devices > 1 ? 's' : '') + '. Ask the owner to reset it.' }); }
    device = crypto.randomBytes(8).toString('hex');
  }
  devs.set(device, Date.now());
  const ttl = Math.max(60, Math.min(30 * 86400, Math.floor((expOf(found) - Date.now()) / 1000)));
  console.log('[access] sign-in ok member=' + found.name + ' device=' + device.slice(0, 4) + ' (' + devs.size + '/' + found.devices + ' devices)');
  return sendJson(res, 200, { ok: true }, { 'Set-Cookie': setCookie(req, 'mmn_session', sign({ f: found.fp, d: device, e: found.epoch | 0 }), ttl) });
}

/* ---------- admin ---------- */
const adminHash = ADMIN_PASSWORD ? crypto.createHash('sha256').update(ADMIN_PASSWORD).digest() : null;
const adminOk = req => { const p = verify(cookieOf(req, 'mmn_admin')); return !!(p && p.a === 1 && p.x > Date.now()); };
function insights(days) {
  days = [7, 30, 60].includes(days) ? days : 30;
  const now = Date.now(), keys = []; for (let i = days - 1; i >= 0; i--) keys.push(istDay(now - i * 86400000));
  const today = istDay(now), mon = today.slice(0, 7);
  const daily = keys.map(d => ({ d, mb: Math.round(STORE.daily[d] || 0), peak: STORE.peak[d] || 0 }));
  const hourly = new Array(24).fill(0); let hourDays = 0;
  for (const d of keys) { const H = STORE.hourly[d]; if (H) { hourDays++; for (let h = 0; h < 24; h++) hourly[h] += H[h] || 0; } }
  const T = new Map();
  for (const d of keys) { const D = STORE.titles[d]; if (!D) continue; for (const [key, v] of Object.entries(D)) { const i = key.indexOf('|'), e = T.get(key) || { k: key.slice(0, i), name: key.slice(i + 1), views: 0, mb: 0 }; e.views += v[0] || 0; e.mb += v[1] || 0; T.set(key, e); } }
  const titles = [...T.values()].map(e => ({ ...e, mb: Math.round(e.mb) }));
  const topMb = titles.slice().sort((a, b) => b.mb - a.mb).slice(0, 15), topViews = titles.slice().sort((a, b) => b.views - a.views || b.mb - a.mb).slice(0, 15);
  const members = STORE.members.map(m => { const u = STORE.usage[m.id] || {}; let mb = 0; for (const d of keys) mb += u[d] || 0; return { name: m.name, mb: Math.round(mb) }; }).filter(x => x.mb > 0).sort((a, b) => b.mb - a.mb).slice(0, 8);
  const cut = now - 14 * 86400000;
  const inactive = STORE.members.filter(m => !m.paused && expOf(m) > now && (!m.lastSeenAt || m.lastSeenAt < cut))
    .map(m => ({ name: m.name, days: m.lastSeenAt ? Math.floor((now - m.lastSeenAt) / 86400000) : null, expires: m.expires }))
    .sort((a, b) => (b.days == null ? 9999 : b.days) - (a.days == null ? 9999 : a.days)).slice(0, 20);
  let month = 0; for (const [d, v] of Object.entries(STORE.daily)) if (d.startsWith(mon)) month += v;
  const ist = new Date(now + 19800000), elapsed = (+today.slice(8) - 1) + (ist.getUTCHours() * 60 + ist.getUTCMinutes()) / 1440, dim = new Date(+today.slice(0, 4), +today.slice(5, 7), 0).getDate();
  return { days, now, daily, hourly: hourly.map(Math.round), hourDays, topMb, topViews, members, inactive, titlesTracked: titles.length,
    totals: { today: Math.round(STORE.daily[today] || 0), month: Math.round(month), projected: elapsed >= 0.5 ? Math.round(month / elapsed * dim) : null, daysInMonth: dim } };
}
function memberView(m) {
  const devs = DEVICES.get(m.fp); if (devs) pruneDevices(devs);
  const st = STREAMS.get(m.fp); let watching = 0; if (st) for (const c of st.values()) if (c > 0) watching++;
  let last = m.lastSeenAt || 0; if (devs) for (const t of devs.values()) last = Math.max(last, t);
  return { id: m.id, name: m.name, code: m.code, expires: m.expires, expiresDate: m.expires == null ? '' : istDay(m.expires), paused: m.paused, devices: m.devices, screens: m.screens, note: m.note,
    createdAt: m.createdAt, devicesUsed: devs ? devs.size : 0, watching, lastSeen: last || null, usage: usageOf(m) };
}
function applyFields(m, b) {
  if ('name' in b) { const n = String(b.name || '').replace(/[\u0000-\u001f]/g, ' ').trim().slice(0, 60); if (!n) throw new Error('Please enter a name'); m.name = n; }
  if ('expires' in b) { if (b.expires === '' || b.expires == null) m.expires = null; else { const t = parseExpiry(String(b.expires)); if (Number.isNaN(t)) throw new Error('Cannot read that date'); m.expires = t; } }
  if ('devices' in b) { const d = +b.devices; if (!(d >= 1 && d <= 20)) throw new Error('Devices must be between 1 and 20'); m.devices = Math.floor(d); }
  if ('screens' in b) { const d = +b.screens; if (!(d >= 1 && d <= 10)) throw new Error('"At once" must be between 1 and 10'); m.screens = Math.floor(d); }
  if ('paused' in b) m.paused = !!b.paused;
  if ('note' in b) m.note = String(b.note || '').slice(0, 200);
  if ('code' in b && String(b.code || '').trim()) {
    const c = String(b.code).toUpperCase().replace(/[^A-Z0-9-]/g, ''), n = normCode(c);
    if (n.length < 8 || n.length > 32) throw new Error('A code needs 8 to 32 letters or numbers');
    if (STORE.members.some(x => x !== m && normCode(x.code) === n)) throw new Error('Another member already has that code');
    m.code = c;
  }
}
function dropSessions(fp) { DEVICES.delete(fp); killMember(fp); }
async function handleAdmin(req, res, u) {
  if (!adminHash) return fail(res, 404, 'Admin is off. Set ADMIN_PASSWORD to turn it on.');
  const p = u.pathname;
  if (p === '/admin' || p === '/admin/') {
    if (req.method !== 'GET') return fail(res, 405, 'GET only');
    try { return sendStatic(req, res, staticPage('admin.html'), 'text/html; charset=utf-8'); } catch { return fail(res, 500, 'admin.html is missing from the server files'); }
  }
  const site = req.headers['sec-fetch-site'];
  if (req.method !== 'GET' && ((site && site !== 'same-origin') || req.headers['x-admin'] !== '1')) return fail(res, 403, 'Not allowed');
  if (p === '/admin/login' && req.method === 'POST') {
    const ip = clientIp(req), now = Date.now();
    let t = atries.get(ip); if (!t || t.reset < now) { t = { n: 0, reset: now + 15 * 60000 }; atries.set(ip, t); }
    if (t.n >= 5) return sendJson(res, 429, { error: 'Too many wrong attempts. Try again in a few minutes.' });
    let pw = ''; try { pw = JSON.parse(await readBody(req)).password || ''; } catch { return sendJson(res, 400, { error: 'Bad request' }); }
    if (!crypto.timingSafeEqual(crypto.createHash('sha256').update(String(pw)).digest(), adminHash)) { t.n++; console.log('[admin] wrong password from ' + ip); return sendJson(res, 401, { error: 'Wrong password.' }); }
    console.log('[admin] login from ' + ip);
    return sendJson(res, 200, { ok: true }, { 'Set-Cookie': setCookie(req, 'mmn_admin', sign({ a: 1, x: Date.now() + 12 * 3600000 }), 12 * 3600, '/admin', true) });
  }
  if (p === '/admin/logout') return sendJson(res, 200, { ok: true }, { 'Set-Cookie': setCookie(req, 'mmn_admin', '', 0, '/admin', true) });
  if (!adminOk(req)) return sendJson(res, 401, { error: 'login' });
  try {
    if (p === '/admin/api/state' && req.method === 'GET') {
      return sendJson(res, 200, { now: Date.now(), storage: { persistent: storeInfo.persistent, mounted: storeInfo.mounted, error: storeInfo.error, dir: storeInfo.dir, wantsDisk: !DATA_DIR }, members: STORE.members.map(memberView) });
    }
    if (p === '/admin/api/insights' && req.method === 'GET') return sendJson(res, 200, insights(+u.searchParams.get('days') || 30));
    if (p === '/admin/api/members' && req.method === 'POST') {
      const b = JSON.parse(await readBody(req) || '{}');
      if (STORE.members.length >= 500) throw new Error('Member limit reached (500)');
      const m = clean({ name: 'x', code: genCode(), devices: DEFAULT_DEVICES, screens: 1 }); m.name = '';
      applyFields(m, { devices: DEFAULT_DEVICES, screens: 1, ...b });
      if (!m.name) throw new Error('Please enter a name');
      STORE.members.push(m); rebuild(); const saved = saveStore();
      console.log('[admin] added member ' + m.name);
      return sendJson(res, 200, { ok: true, saved, member: memberView(m) });
    }
    const mm = /^\/admin\/api\/members\/([a-f0-9]{8})(?:\/(newcode|signout))?$/.exec(p);
    if (mm) {
      const m = STORE.members.find(x => x.id === mm[1]); if (!m) return sendJson(res, 404, { error: 'Member not found' });
      const act = mm[2], oldFp = m.fp;
      if (req.method === 'DELETE' && !act) {
        dropSessions(m.fp); STORE.members = STORE.members.filter(x => x !== m); delete STORE.usage[m.id]; rebuild(); const saved = saveStore();
        console.log('[admin] removed member ' + m.name); return sendJson(res, 200, { ok: true, saved });
      }
      if (req.method === 'POST' && act === 'newcode') {
        m.code = genCode(); dropSessions(oldFp); m.epoch++; rebuild(); const saved = saveStore();
        console.log('[admin] new code for ' + m.name); return sendJson(res, 200, { ok: true, saved, member: memberView(m) });
      }
      if (req.method === 'POST' && act === 'signout') {
        m.epoch++; dropSessions(m.fp); const saved = saveStore();
        console.log('[admin] signed out all devices of ' + m.name); return sendJson(res, 200, { ok: true, saved, member: memberView(m) });
      }
      if (req.method === 'PUT' && !act) {
        const b = JSON.parse(await readBody(req) || '{}'), before = { code: m.code, paused: m.paused, expires: m.expires };
        applyFields(m, b);
        if (m.code !== before.code) { dropSessions(oldFp); m.epoch++; }
        rebuild(); if ((m.paused && !before.paused) || (expOf(m) < Date.now())) killMember(m.fp);
        const saved = saveStore(); console.log('[admin] updated member ' + m.name);
        return sendJson(res, 200, { ok: true, saved, member: memberView(m) });
      }
    }
    return sendJson(res, 404, { error: 'Not found' });
  } catch (e) { return sendJson(res, 400, { error: e.message || 'Bad request' }); }
}
loadStore();
console.log('[access] ' + (gateOn() ? 'access codes are ON: ' + STORE.members.length + ' member(s)' : 'access codes are OFF (no ADMIN_PASSWORD and no members)'));
if (ADMIN_PASSWORD) console.log('[admin] admin page is ON at /admin · saved on disk: ' + (storeInfo.persistent ? 'yes' + (storeInfo.mounted ? '' : ' (WARNING: ' + DATA_DIR + ' does not look like a separate disk, so it may be wiped on deploy)') : 'NO, members will be lost on restart. Attach a Render Disk and set DATA_DIR'));
if (gateOn() && !process.env.SESSION_SECRET) console.log('[access] WARNING: SESSION_SECRET is not set, so everyone is signed out whenever the server restarts.');

/* Any unexpected error is logged and answered with a 500 instead of crashing the whole server (a crash shows up as 502 for everyone). */
process.on('unhandledRejection', e => console.log('[error] unhandled: ' + (e && e.stack || e)));
process.on('uncaughtException', e => console.log('[error] uncaught: ' + (e && e.stack || e)));
const server = http.createServer((req, res) => {
  handle(req, res).catch(e => {
    console.log('[error] ' + req.method + ' ' + String(req.url).split('?')[0] + ': ' + (e && e.stack || e));
    try { if (!res.headersSent) res.writeHead(500, { 'Content-Type': 'text/plain' }); res.end('Server error'); } catch {}
  });
});
async function handle(req, res) {
  const u = new URL(req.url, 'http://localhost');
  if (u.pathname === '/healthz') return fail(res, 200, 'ok');
  if (u.pathname === '/' || u.pathname === '/index.html') {
    try { return sendStatic(req, res, staticPage('landing.html'), 'text/html; charset=utf-8'); } catch { return fail(res, 500, 'landing.html not found'); }
  }
  if (u.pathname === '/admin' || u.pathname.startsWith('/admin/')) return handleAdmin(req, res, u);
  if (u.pathname === '/gate') return handleGate(req, res, u);
  if (u.pathname === '/logout') { res.writeHead(302, { Location: '/gate', 'Set-Cookie': setCookie(req, 'mmn_session', '', 0), 'Cache-Control': 'no-store' }); return res.end(); }
  let who = null;
  if (gateOn()) {
    if (u.pathname === '/app' || u.pathname === '/proxy' || u.pathname === '/diag' || u.pathname === '/session' || u.pathname === '/clog') {
      const m = memberOf(req);
      if (m.error) {
        if (u.pathname === '/app') { res.writeHead(302, { Location: m.error === 'login' ? '/gate' : '/gate?why=' + m.error, 'Cache-Control': 'no-store' }); return res.end(); }
        res.writeHead(401, { ...SEC, 'Content-Type': 'application/json', 'Cache-Control': 'no-store' });
        return res.end(JSON.stringify({ error: m.error }));
      }
      who = m;
    }
  } else if (!authed(req)) { res.writeHead(401, { ...SEC, 'WWW-Authenticate': 'Basic realm="IPTV Player"' }); return res.end('Password required'); }
  if (u.pathname === '/clog') {      // player -> server log lines (playback events from the browser), shown in the same log as the server's own
    if (req.method !== 'POST') return fail(res, 405, 'POST only');
    const site = req.headers['sec-fetch-site']; if (site && site !== 'same-origin') return fail(res, 403, 'Same-origin requests only');
    const ip = clientIp(req), now = Date.now(); let h = hits.get('log|' + ip); if (!h || h.reset < now) { h = { n: 0, reset: now + 60000 }; hits.set('log|' + ip, h); }
    if (++h.n > 240) return fail(res, 429, 'Too many log lines');
    let o = {}; try { o = JSON.parse(await readBody(req, 6144)); } catch { return fail(res, 400, 'Bad request'); }
    const line = {}; for (const [k, v] of Object.entries(o).slice(0, 30)) line[String(k).slice(0, 20)] = typeof v === 'string' ? v.replace(/(live|movie|series)\/[^\/\s"]+\/[^\/\s"]+\//g, '$1/***/***/').replace(/(username|password)=[^&\s"]+/g, '$1=***').slice(0, 300) : v;
    console.log('[client] member=' + (who ? who.entry.name : '-') + ' dev=' + (who && who.device ? who.device.slice(0, 4) : '-') + ' ' + JSON.stringify(line));
    res.writeHead(204, { ...SEC, 'Cache-Control': 'no-store' }); return res.end();
  }
  if (u.pathname === '/session') {
    res.writeHead(200, { ...SEC, 'Content-Type': 'application/json', 'Cache-Control': 'no-store' });
    return res.end(JSON.stringify(who ? { name: who.entry.name, expires: expOf(who.entry) === Infinity ? null : expOf(who.entry) } : { name: '', expires: null }));
  }

  if (u.pathname === '/proxy' || u.pathname === '/diag') {
    if (req.method !== 'GET') return fail(res, 405, 'GET only');
    req.socket.setNoDelay(true);
    const site = req.headers['sec-fetch-site'];
    if (site && site !== 'same-origin') return fail(res, 403, 'Same-origin requests only');
    const ip = clientIp(req), now = Date.now();
    let h = hits.get(ip); if (!h || h.reset < now) { h = { n: 0, reset: now + 60000 }; hits.set(ip, h); }
    if (++h.n > RATE) return fail(res, 429, 'Too many requests');
    if ((conc.get(ip) || 0) >= MAX_CONC) return fail(res, 429, 'Too many open streams');
    if (who && otherScreens(who) >= who.entry.screens) return fail(res, 429, 'This access code is already in use on another device');
    const target = u.searchParams.get('u') || '';
    const meta = { n: String(u.searchParams.get('n') || '').replace(/[\u0000-\u001f]/g, ' ').slice(0, 80), k: ['live', 'movie', 'episode'].includes(u.searchParams.get('k')) ? u.searchParams.get('k') : '' };
    if (u.pathname !== '/proxy' || /player_api\.php/i.test(target) || !meta.k) meta.n = meta.k = '';
    const ac = new AbortController();
    const rid = crypto.randomBytes(2).toString('hex'), tReq = Date.now(), isList = /player_api\.php/i.test(target), quiet = (() => { try { const q = new URL(target).pathname; return /\.(m3u8?|ts|aac|m4s|mp4)$/i.test(q) && !LIVE_TS.test(q) && u.searchParams.get('tx') !== '1' && /\.(m3u8?|ts|aac|m4s)$/i.test(q); } catch { return false; } })(), logIt = u.pathname === '/proxy' && !isList && !quiet;
    const who_ = who ? who.entry.name : '-', tag = 'req ' + rid;
    let upStatus = ''; const b0 = req.socket.bytesWritten;
    if (logIt) console.log('[' + tag + '] member=' + who_ + ' ch="' + meta.n + '" kind=' + (meta.k || '-') + ' -> ' + maskUrl(target) + (u.searchParams.get('tx') === '2' ? ' (REPAIR re-encode ON)' : u.searchParams.get('tx') === '1' ? ' (audio conversion ON)' : '') + (req.headers.range ? ' range=' + req.headers.range : ''));
    conc.set(ip, (conc.get(ip) || 0) + 1);
    if (who) { streamInc(who, res); if (meta.n) trackView(who, meta); }
    let lastB = req.socket.bytesWritten, total = 0;
    const sample = () => { const cur = req.socket.bytesWritten, d = cur - lastB; lastB = cur; if (d > 0) { total += d; if (who) account(who.entry, d / 1e6, meta); } };
    if (who) METERS.add(sample);
    let done = false;
    const release = () => { if (!done) { done = true; const c = (conc.get(ip) || 1) - 1; c ? conc.set(ip, c) : conc.delete(ip); if (who) { streamDec(who, res); sample(); METERS.delete(sample); if (total >= 1e6) console.log('[usage] member=' + who.entry.name + ' MB=' + (total / 1e6).toFixed(1)); } } };
    res.on('close', () => {
      if (logIt && upStatus) { const s = (Date.now() - tReq) / 1000, mb = Math.max(0, req.socket.bytesWritten - b0) / 1e6; console.log('[' + tag + '] closed after ' + s.toFixed(1) + 's, sent ~' + mb.toFixed(1) + ' MB' + (s > 3 && mb ? ' (avg ' + Math.round(mb * 8 / s * 1000) + ' kbps)' : '') + ', ' + (res.writableEnded ? 'server finished the response' : 'browser disconnected/aborted')); }
      ac.abort(); release(); });
    try {
      const hd = { 'User-Agent': UA, Accept: '*/*' };
      if (req.headers.range) hd.Range = req.headers.range;
      const listAct = u.pathname === '/proxy' ? listActionOf(target) : '';
      if (listAct) { const hit = listGet(target); if (hit) return sendList(req, res, hit); }
      let r = await upstream(target, hd, ac.signal);
      upStatus = String(r.statusCode);
      if (logIt || (u.pathname === '/proxy' && !isList && r.statusCode >= 400)) console.log('[' + tag + '] member=' + who_ + ' ' + maskUrl(target) + ' provider answered HTTP ' + r.statusCode + ' type=' + (r.headers['content-type'] || '-') + ' length=' + (r.headers['content-length'] || 'none(live)') + ' first-byte=' + (Date.now() - tReq) + 'ms' + (r.finalUrl !== target ? ' redirected to ' + maskUrl(r.finalUrl) : ''));
      if ((logIt || (u.pathname === '/proxy' && !isList)) && r.statusCode >= 400) { const ch = []; r.on('data', c => { if (ch.length < 2) ch.push(c); }); r.once('close', () => console.log('[' + tag + '] provider error body: ' + Buffer.concat(ch).toString('utf8', 0, 160).replace(/\s+/g, ' ').replace(/(live|movie|series)\/[^\/\s]+\/[^\/\s]+\//g, '$1/***/***/'))); }
      if (u.pathname === '/diag') {
        const chunks = []; let n = 0;
        await new Promise(done => {
          r.on('data', c => { chunks.push(c); n += c.length; if (n >= 512) { r.destroy(); done(); } });
          r.on('end', done); r.on('close', done); r.on('error', done);
          setTimeout(done, 8000);
        });
        const b = Buffer.concat(chunks), head = b.slice(0, 20).toString('latin1');
        const kind = b[0] === 0x47 ? 'MPEG-TS video' : head.startsWith('#EXTM3U') ? 'HLS/M3U playlist' : head.startsWith('FLV') ? 'FLV video'
          : b.slice(4, 8).toString() === 'ftyp' ? 'MP4 video' : /^\s*</.test(head) ? 'HTML/XML page' : b.length ? 'unknown data' : 'empty';
        const mask = x => x.replace(/(live|movie|series)\/[^\/\s]+\/[^\/\s]+\//g, '$1/***/***/');
        const snippet = /HTML|M3U|unknown/.test(kind) ? mask(b.toString('utf8', 0, 200)) : '';
        res.writeHead(200, { ...SEC, 'Content-Type': 'application/json', 'Cache-Control': 'no-store' });
        return res.end(JSON.stringify({ status: r.statusCode, type: r.headers['content-type'] || '', kind, bytes: b.length, host: new URL(r.finalUrl).host, redirected: r.finalUrl !== target, snippet }));
      }
      { // live .ts that answers with an HTML page = provider busy / channel offline. The previous connection is often
        // still being released after a channel switch, so retry a few times before giving up.
        let tp0 = ''; try { tp0 = new URL(target).pathname; } catch {}
        for (let tries = 0; tries < 3 && LIVE_TS.test(tp0) && r.statusCode === 200 && /^text\/html/i.test(r.headers['content-type'] || ''); tries++) {
          r.destroy(); if (logIt) console.log('[' + tag + '] provider sent a web page instead of video (busy/offline?), retry ' + (tries + 1) + '/3');
          await sleep(1500); if (ac.signal.aborted) return;
          r = await upstream(target, hd, ac.signal); upStatus = String(r.statusCode);
        }
        if (LIVE_TS.test(tp0) && r.statusCode === 200 && /^text\/html/i.test(r.headers['content-type'] || '')) { r.destroy(); return fail(res, 503, 'Provider returned a web page instead of video: the channel is offline or your provider connection limit is reached'); }
      }
      const ct = r.headers['content-type'] || '';
      if (listAct && r.statusCode === 200 && !r.headers['content-encoding'] && /json|text/i.test(ct)) {
        const it = r[Symbol.asyncIterator](), chunks = []; let size = 0, streamed = null;
        for (;;) {
          const nx = await it.next(); if (nx.done) break;
          size += nx.value.length;
          if (!streamed && size > LIST_RAW_MAX) {            // too big to keep in memory: compress on the fly instead
            const o = { ...SEC, 'Content-Type': ct, 'Cache-Control': 'no-store', Vary: 'Accept-Encoding' };
            if (acceptsEnc(req, 'gzip')) { o['Content-Encoding'] = 'gzip'; streamed = zlib.createGzip({ level: 4 }); streamed.pipe(res); } else streamed = res;
            res.writeHead(200, o); for (const c of chunks) streamed.write(c); chunks.length = 0;
          }
          if (streamed) { if (!streamed.write(nx.value)) await new Promise(rs => streamed.once('drain', rs)); } else chunks.push(nx.value);
        }
        if (streamed) { streamed.end(); return; }
        const raw = Buffer.concat(chunks);
        const gz = await new Promise(rs => zlib.gzip(raw, { level: 6 }, (e, b) => rs(e ? null : b)));
        if (gz && raw.length > 2 && raw[0] === 0x5b) { const e = { ct: ct || 'application/json', gz, t: Date.now() }; listSet(target, e); return sendList(req, res, e); }
        const o = { ...SEC, 'Content-Type': ct, 'Cache-Control': 'no-store', Vary: 'Accept-Encoding' };
        if (gz && acceptsEnc(req, 'gzip')) { o['Content-Encoding'] = 'gzip'; o['Content-Length'] = gz.length; res.writeHead(200, o); return res.end(gz); }
        o['Content-Length'] = raw.length; res.writeHead(200, o); return res.end(raw);
      }
      const looksPlaylist = /mpegurl/i.test(ct) || /\.m3u8?$/i.test(new URL(r.finalUrl).pathname);
      if (looksPlaylist) {
        // Peek at the first bytes: a real playlist starts with #EXTM3U. Some Xtream panels answer
        // ".m3u8" with an endless MPEG-TS stream; buffering that would hang forever ("Connecting...").
        const it = r[Symbol.asyncIterator]();
        const first = await it.next();
        const head = first.done ? Buffer.alloc(0) : first.value;
        if (/^\uFEFF?\s*#EXTM3U/.test(head.toString('utf8', 0, 32))) {
          const chunks = [head]; let size = head.length;
          for (let n = await it.next(); !n.done; n = await it.next()) { size += n.value.length; if (size > MAX_PLAYLIST) { r.destroy(); return fail(res, 502, 'Playlist too large'); } chunks.push(n.value); }
          const text = Buffer.concat(chunks).toString('utf8');
          const body = text.includes('#EXT-X-') ? rewrite(text, r.finalUrl, meta.n ? '&n=' + encodeURIComponent(meta.n) + '&k=' + meta.k : '') : text;
          let buf = Buffer.from(body); const hh = { ...SEC, 'Content-Type': ct || 'application/vnd.apple.mpegurl', 'Cache-Control': 'no-store', Vary: 'Accept-Encoding' };
          if (buf.length > 1024 && acceptsEnc(req, 'gzip')) { const gz = await new Promise(rs => zlib.gzip(buf, { level: 5 }, (e, b) => rs(e ? null : b))); if (gz) { buf = gz; hh['Content-Encoding'] = 'gzip'; } }
          hh['Content-Length'] = buf.length; res.writeHead(r.statusCode, hh);
          return res.end(buf);
        }
        const o = { ...SEC, 'X-Accel-Buffering': 'no', 'Cache-Control': 'no-store' };
        for (const k of ['content-type', 'content-length', 'content-range', 'accept-ranges']) if (r.headers[k]) o[k] = r.headers[k];
        res.writeHead(r.statusCode, o);
        res.write(head);
        r.on('error', () => res.end()); r.pipe(res);
        return;
      }
      if (r.statusCode === 200 && !r.headers['content-range'] && !r.headers['content-encoding'] && /^(application\/json|text\/|application\/(xml|x-mpegurl)|audio\/x-mpegurl)/i.test(ct) && acceptsEnc(req, 'gzip')) {
        res.writeHead(200, { ...SEC, 'Content-Type': ct, 'Content-Encoding': 'gzip', Vary: 'Accept-Encoding', 'Cache-Control': 'no-store', 'X-Accel-Buffering': 'no' });
        const gz = zlib.createGzip({ level: 4 }); r.on('error', () => gz.end()); r.pipe(gz).pipe(res); return;
      }
      const out = { ...SEC, 'X-Accel-Buffering': 'no', 'Cache-Control': 'no-store' };
      for (const k of ['content-type', 'content-length', 'content-range', 'accept-ranges']) if (r.headers[k]) out[k] = r.headers[k];
      res.writeHead(r.statusCode, out);
      let tp = ''; try { tp = new URL(target).pathname; } catch {}
      const wantTx = u.searchParams.get('tx') === '2' ? 2 : u.searchParams.get('tx') === '1' ? 1 : 0;
      if (logIt && r.statusCode === 200 && /\.(ts|m2ts)$|mp2t|octet|^$/i.test(tp + ' ' + (r.headers['content-type'] || ''))) sniffStream(r, tag);
      if (r.statusCode === 200 && !r.headers['content-length'] && (LIVE_TS.test(tp) || wantTx)) { pumpLive(res, r, target, hd, ac.signal, wantTx); return; }
      r.on('error', e => { if (logIt) console.log('[' + tag + '] provider stream error: ' + e.message); res.end(); }); r.pipe(res);
    } catch (e) { if (u.pathname === '/proxy' && !isList) console.log('[' + tag + '] member=' + who_ + ' ' + maskUrl(target) + ' FAILED to reach provider after ' + (Date.now() - tReq) + 'ms: ' + e.message + (e.code ? ' (' + e.code + ')' : '')); fail(res, 502, 'Proxy error: ' + e.message); }
    return;
  }

  if (u.pathname === '/app') {
    try { return sendStatic(req, res, staticPage('iptv-player.html', h => h.replace('<head>', '<head>\n<script>window.IPTV_PROXY=true</script>')), 'text/html; charset=utf-8'); } catch { return fail(res, 500, 'iptv-player.html not found'); }
  }
  fail(res, 404, 'Not found');
}
server.keepAliveTimeout = 65000; server.headersTimeout = 66000;
server.listen(PORT, '0.0.0.0', () => console.log('IPTV Player listening on :' + PORT + (gateOn() ? ' (access codes: ' + STORE.members.length + ')' : PASS ? ' (password protected)' : ' (NO PASSWORD OR ACCESS CODES SET)')));
