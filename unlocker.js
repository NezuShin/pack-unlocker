/*
 * Pack Unlocker core: repairs "protected" Minecraft resource packs.
 *
 * Pure JavaScript, no dependencies. Works in browsers and in Node 18+.
 *
 *   const { parts, size, report } = await PackUnlocker.unlock(bytes, { onProgress });
 *   const blob = new Blob(parts, { type: 'application/zip' });
 *
 * Approach: read the archive the same way Minecraft (java.util.zip.ZipFile) does,
 * decompress every file to learn its real CRC and size, fix PNG checksums that the
 * game's image decoder (stb_image) ignores, then write a brand-new, clean ZIP.
 * Unmodified files keep their original compressed bytes.
 */
(function (root, factory) {
  'use strict';
  const api = factory();
  if (typeof module === 'object' && module.exports) module.exports = api;
  else root.PackUnlocker = api;
})(typeof globalThis !== 'undefined' ? globalThis : this, function () {
  'use strict';

  // ---------------------------------------------------------------------------
  // Byte helpers
  // ---------------------------------------------------------------------------
  const u16 = (d, p) => d[p] | (d[p + 1] << 8);
  const u32 = (d, p) => (d[p] | (d[p + 1] << 8) | (d[p + 2] << 16) | (d[p + 3] << 24)) >>> 0;
  const u64 = (d, p) => u32(d, p) + u32(d, p + 4) * 4294967296;
  const be32 = (d, p) => ((d[p] << 24) | (d[p + 1] << 16) | (d[p + 2] << 8) | d[p + 3]) >>> 0;
  function putBe32(d, p, v) {
    d[p] = v >>> 24; d[p + 1] = (v >>> 16) & 255; d[p + 2] = (v >>> 8) & 255; d[p + 3] = v & 255;
  }
  const hex32 = (n) => (n >>> 0).toString(16).toUpperCase().padStart(8, '0');

  const SIG_LOCAL = 0x04034b50;
  const SIG_CENTRAL = 0x02014b50;
  const SIG_EOCD = 0x06054b50;
  const SIG_EOCD64 = 0x06064b50;
  const SIG_EOCD64_LOC = 0x07064b50;
  const SIG_DESCRIPTOR = 0x08074b50;

  // Anything bigger than this after decompression is treated as a zip bomb.
  const MAX_ENTRY_SIZE = 512 * 1024 * 1024;

  const now = () => (typeof performance !== 'undefined' ? performance.now() : Date.now());
  // Lets the page repaint during long runs. MessageChannel isn't throttled in
  // background tabs the way setTimeout is; Node has setImmediate.
  const yieldToUi = (() => {
    if (typeof setImmediate === 'function') return () => new Promise((r) => setImmediate(r));
    if (typeof MessageChannel === 'function') {
      const ch = new MessageChannel(), waiting = [];
      ch.port1.onmessage = () => waiting.shift()();
      return () => new Promise((r) => { waiting.push(r); ch.port2.postMessage(0); });
    }
    return () => new Promise((r) => setTimeout(r, 0));
  })();

  // ---------------------------------------------------------------------------
  // Checksums
  // ---------------------------------------------------------------------------
  const CRC_TABLE = (() => {
    const t = new Int32Array(256);
    for (let n = 0; n < 256; n++) {
      let c = n;
      for (let k = 0; k < 8; k++) c = c & 1 ? 0xedb88320 ^ (c >>> 1) : c >>> 1;
      t[n] = c;
    }
    return t;
  })();

  function crc32(buf, start = 0, end = buf.length) {
    let c = -1;
    for (let i = start; i < end; i++) c = CRC_TABLE[(c ^ buf[i]) & 0xff] ^ (c >>> 8);
    return ~c >>> 0;
  }

  function adler32(buf, start = 0, end = buf.length) {
    let a = 1, b = 0, i = start;
    while (i < end) {
      const stop = Math.min(end, i + 5552);
      for (; i < stop; i++) { a += buf[i]; b += a; }
      a %= 65521; b %= 65521;
    }
    return ((b << 16) | a) >>> 0;
  }

  // ---------------------------------------------------------------------------
  // Inflate (raw DEFLATE, RFC 1951)
  //
  // Own implementation instead of DecompressionStream because we need to know
  // exactly how many compressed bytes a stream used (sizes in protected
  // archives can't be trusted), and whether the stream is strictly valid.
  // ---------------------------------------------------------------------------
  const LEN_BASE = [3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 15, 17, 19, 23, 27, 31, 35, 43, 51, 59, 67, 83, 99, 115, 131, 163, 195, 227, 258];
  const LEN_EXTRA = [0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 2, 2, 2, 2, 3, 3, 3, 3, 4, 4, 4, 4, 5, 5, 5, 5, 0];
  const DIST_BASE = [1, 2, 3, 4, 5, 7, 9, 13, 17, 25, 33, 49, 65, 97, 129, 193, 257, 385, 513, 769, 1025, 1537, 2049, 3073, 4097, 6145, 8193, 12289, 16385, 24577];
  const DIST_EXTRA = [0, 0, 0, 0, 1, 1, 2, 2, 3, 3, 4, 4, 5, 5, 6, 6, 7, 7, 8, 8, 9, 9, 10, 10, 11, 11, 12, 12, 13, 13];
  const CL_ORDER = [16, 17, 18, 0, 8, 7, 9, 6, 10, 5, 11, 4, 12, 3, 13, 2, 14, 1, 15];

  // Builds a single-level lookup table indexed by the next `bits` input bits.
  // Each entry is (symbol << 4) | codeLength; 0 means "no such code".
  function huffTable(lengths, n) {
    const count = new Uint16Array(16);
    let maxLen = 0;
    for (let i = 0; i < n; i++) {
      const l = lengths[i];
      count[l]++;
      if (l > maxLen) maxLen = l;
    }
    count[0] = 0;
    let left = 1;
    for (let l = 1; l <= 15; l++) {
      left = (left << 1) - count[l];
      if (left < 0) throw new Error('invalid Huffman code (over-subscribed)');
    }
    const next = new Uint16Array(16);
    for (let l = 1, code = 0; l <= 15; l++) {
      code = (code + count[l - 1]) << 1;
      next[l] = code;
    }
    const bits = maxLen || 1;
    const size = 1 << bits;
    const table = new Uint16Array(size);
    for (let sym = 0; sym < n; sym++) {
      const l = lengths[sym];
      if (!l) continue;
      let c = next[l]++, r = 0;
      for (let k = 0; k < l; k++) { r = (r << 1) | (c & 1); c >>>= 1; }
      const entry = (sym << 4) | l;
      for (let j = r; j < size; j += 1 << l) table[j] = entry;
    }
    return { table, bits, mask: size - 1, incomplete: left > 0, maxLen };
  }

  let FIXED = null;
  function fixedTables() {
    if (!FIXED) {
      const l = new Uint8Array(288);
      l.fill(8, 0, 144); l.fill(9, 144, 256); l.fill(7, 256, 280); l.fill(8, 280, 288);
      const dl = new Uint8Array(30).fill(5);
      FIXED = { lit: huffTable(l, 288), dist: huffTable(dl, 30) };
    }
    return FIXED;
  }

  /**
   * Decompresses a raw deflate stream starting at src[start].
   * Returns { data, consumed, strict, maxDist }.
   *  - consumed: number of compressed bytes the stream really used
   *  - strict:   false if the stream uses things zlib rejects but stb_image accepts
   *  - lenient:  allow those things instead of throwing (used for PNG pixel data)
   */
  function inflateRaw(src, start, end, opts) {
    opts = opts || {};
    const lenient = !!opts.lenient;
    const limit = opts.maxSize || MAX_ENTRY_SIZE;
    let pos = start, bitbuf = 0, bitcnt = 0, op = 0, strict = true, maxDist = 0;
    let out = new Uint8Array(Math.min(limit, Math.max(4096, opts.sizeHint | 0)));

    function need(n) {
      while (bitcnt < n) {
        bitbuf |= (pos < end ? src[pos] : 0) << bitcnt;
        pos++;
        bitcnt += 8;
      }
    }
    function bits(n) {
      need(n);
      const v = bitbuf & ((1 << n) - 1);
      bitbuf >>>= n;
      bitcnt -= n;
      return v;
    }
    function sym(h) {
      need(h.bits);
      const e = h.table[bitbuf & h.mask];
      if (!e) throw new Error('invalid Huffman code in stream');
      const l = e & 15;
      bitbuf >>>= l;
      bitcnt -= l;
      return e >> 4;
    }
    function grow(n) {
      if (op + n <= out.length) return;
      if (op + n > limit) throw new Error('unpacks to more than ' + (limit >> 20) + ' MB (zip bomb?)');
      let s = out.length * 2;
      while (s < op + n) s *= 2;
      const o = new Uint8Array(Math.min(s, limit));
      o.set(out.subarray(0, op));
      out = o;
    }
    function nonStrict(msg) {
      if (!lenient) throw new Error(msg);
      strict = false;
    }
    function dynamicTables() {
      const hlit = bits(5) + 257, hdist = bits(5) + 1, hclen = bits(4) + 4;
      if (hlit > 286 || hdist > 30) nonStrict('too many length or distance symbols');
      const cl = new Uint8Array(19);
      for (let i = 0; i < hclen; i++) cl[CL_ORDER[i]] = bits(3);
      const clt = huffTable(cl, 19);
      if (clt.incomplete) nonStrict('incomplete code-length code');
      const lens = new Uint8Array(hlit + hdist);
      for (let i = 0; i < hlit + hdist;) {
        const s = sym(clt);
        if (s < 16) { lens[i++] = s; continue; }
        let rep, val = 0;
        if (s === 16) {
          if (!i) throw new Error('repeat code with no previous length');
          val = lens[i - 1];
          rep = 3 + bits(2);
        } else if (s === 17) rep = 3 + bits(3);
        else rep = 11 + bits(7);
        if (i + rep > hlit + hdist) throw new Error('code lengths overflow');
        lens.fill(val, i, i + rep);
        i += rep;
      }
      if (!lens[256]) throw new Error('missing end-of-block code');
      const lit = huffTable(lens.subarray(0, hlit), hlit);
      const dist = huffTable(lens.subarray(hlit), hdist);
      if (lit.incomplete && lit.maxLen !== 1) nonStrict('incomplete literal/length code');
      if (dist.incomplete && dist.maxLen > 1) nonStrict('incomplete distance code');
      return { lit, dist };
    }

    let last = 0;
    do {
      last = bits(1);
      const type = bits(2);
      if (type === 0) {
        // Stored block: drop to the byte boundary and hand unused whole bytes back.
        pos -= bitcnt >> 3;
        bitbuf = 0;
        bitcnt = 0;
        if (pos + 4 > end) throw new Error('unexpected end of stream');
        const len = u16(src, pos), nlen = u16(src, pos + 2);
        if ((len ^ 0xffff) !== nlen) throw new Error('corrupt stored block');
        pos += 4;
        if (pos + len > end) throw new Error('unexpected end of stream');
        grow(len);
        out.set(src.subarray(pos, pos + len), op);
        op += len;
        pos += len;
      } else if (type === 1 || type === 2) {
        const t = type === 1 ? fixedTables() : dynamicTables();
        const lit = t.lit, dist = t.dist;
        for (;;) {
          let s = sym(lit);
          if (s < 256) {
            if (op >= out.length) grow(1);
            out[op++] = s;
          } else if (s === 256) {
            break;
          } else {
            s -= 257;
            if (s >= 29) throw new Error('invalid length symbol');
            const len = LEN_BASE[s] + bits(LEN_EXTRA[s]);
            const ds = sym(dist);
            if (ds >= 30) throw new Error('invalid distance symbol');
            const dd = DIST_BASE[ds] + bits(DIST_EXTRA[ds]);
            if (dd > op) throw new Error('distance too far back');
            if (dd > maxDist) maxDist = dd;
            grow(len);
            for (let k = 0; k < len; k++, op++) out[op] = out[op - dd];
          }
        }
      } else {
        throw new Error('invalid block type');
      }
    } while (!last);

    const consumed = pos - (bitcnt >> 3) - start;
    if (start + consumed > end) throw new Error('unexpected end of stream');
    return { data: out.subarray(0, op), consumed, strict, maxDist };
  }

  // zlib stream made of stored (uncompressed) blocks: always valid, needs no compressor.
  function zlibStored(raw) {
    const blocks = Math.max(1, Math.ceil(raw.length / 65535));
    const out = new Uint8Array(2 + raw.length + blocks * 5 + 4);
    out[0] = 0x78; out[1] = 0x01;
    let p = 2;
    for (let i = 0; i < blocks; i++) {
      const s = i * 65535, n = Math.min(65535, raw.length - s);
      out[p] = i === blocks - 1 ? 1 : 0;
      out[p + 1] = n & 255; out[p + 2] = n >>> 8;
      out[p + 3] = ~n & 255; out[p + 4] = (~n >>> 8) & 255;
      out.set(raw.subarray(s, s + n), p + 5);
      p += 5 + n;
    }
    putBe32(out, p, adler32(raw));
    return out;
  }

  async function zlibCompress(raw) {
    if (typeof CompressionStream === 'function' && typeof Blob === 'function' && typeof Response === 'function') {
      try {
        const stream = new Blob([raw]).stream().pipeThrough(new CompressionStream('deflate'));
        return new Uint8Array(await new Response(stream).arrayBuffer());
      } catch (e) { /* fall back below */ }
    }
    return zlibStored(raw);
  }

  // ---------------------------------------------------------------------------
  // PNG repair
  // ---------------------------------------------------------------------------
  const PNG_SIGNATURE = [0x89, 0x50, 0x4e, 0x47, 0x0d, 0x0a, 0x1a, 0x0a];
  function isPng(d) {
    if (d.length < 8) return false;
    for (let i = 0; i < 8; i++) if (d[i] !== PNG_SIGNATURE[i]) return false;
    return true;
  }
  const isLetter = (c) => (c >= 65 && c <= 90) || (c >= 97 && c <= 122);

  /**
   * Repairs a PNG. Returns null if the file isn't a PNG we can safely parse,
   * otherwise an object describing what was wrong; `data` is the fixed file
   * (or the original bytes if nothing needed fixing).
   */
  async function fixPng(d) {
    if (!isPng(d)) return null;
    const res = {
      changed: false, data: d,
      badCrcChunks: 0, crcKeys: new Set(),
      badAdler: false, adlerKey: null,
      removed: [], trailing: 0,
      badWindow: false, zlibTrailing: 0, recompressed: false, idatMerged: false,
    };

    const chunks = [];
    let pos = 8, ended = false;
    while (pos + 12 <= d.length) {
      const len = be32(d, pos);
      if (len > d.length - pos - 12) return null;
      if (!isLetter(d[pos + 4]) || !isLetter(d[pos + 5]) || !isLetter(d[pos + 6]) || !isLetter(d[pos + 7])) return null;
      const type = String.fromCharCode(d[pos + 4], d[pos + 5], d[pos + 6], d[pos + 7]);
      const stored = be32(d, pos + 8 + len);
      const real = crc32(d, pos + 4, pos + 8 + len);
      if (stored !== real) {
        res.badCrcChunks++;
        res.crcKeys.add((stored ^ real) >>> 0);
      }
      chunks.push({
        type, start: pos + 8, len,
        // Lowercase 1st letter = ancillary (safe to skip); lowercase 2nd letter = private.
        privateAncillary: (d[pos + 4] & 0x20) !== 0 && (d[pos + 5] & 0x20) !== 0,
      });
      pos += 12 + len;
      if (type === 'IEND') { ended = true; break; }
    }
    if (!ended || chunks[0].type !== 'IHDR' || chunks.some((c) => c.type === 'CgBI')) return null;
    res.trailing = d.length - pos;

    // --- IDAT: the zlib stream holding the pixels -------------------------------
    const idat = [];
    chunks.forEach((c, i) => { if (c.type === 'IDAT') idat.push(i); });
    if (!idat.length) return null;
    const contiguous = idat[idat.length - 1] - idat[0] === idat.length - 1;
    let z;
    if (idat.length === 1) {
      const c = chunks[idat[0]];
      z = d.subarray(c.start, c.start + c.len);
    } else {
      z = new Uint8Array(idat.reduce((n, i) => n + chunks[i].len, 0));
      let q = 0;
      for (const i of idat) { const c = chunks[i]; z.set(d.subarray(c.start, c.start + c.len), q); q += c.len; }
    }

    let newZ = null;
    const headerOk = z.length >= 2 && (z[0] & 0x0f) === 8 && !(z[1] & 0x20) && ((z[0] << 8) | z[1]) % 31 === 0;
    if (headerOk) {
      let inf = null;
      try { inf = inflateRaw(z, 2, z.length, { lenient: true }); } catch (e) { inf = null; }
      if (inf) {
        const tail = 2 + inf.consumed;
        const realAdler = adler32(inf.data);
        const storedAdler = tail + 4 <= z.length ? be32(z, tail) : null;
        const cinfo = z[0] >> 4;
        res.badWindow = cinfo > 7 || inf.maxDist > 1 << (cinfo + 8);
        res.zlibTrailing = Math.max(0, z.length - (tail + 4));
        if (storedAdler !== realAdler) {
          res.badAdler = true;
          if (storedAdler !== null) res.adlerKey = (storedAdler ^ realAdler) >>> 0;
        }
        if (!inf.strict) {
          // Only stb_image could read this stream: recompress the pixels properly.
          newZ = await zlibCompress(inf.data);
          res.recompressed = true;
        } else if (res.badAdler || res.badWindow || res.zlibTrailing || !contiguous) {
          let cmf = z[0], flg = z[1];
          if (res.badWindow) {
            cmf = 0x78; // 32 KB window: valid for any deflate stream
            flg &= 0xc0;
            const r = ((cmf << 8) | flg) % 31;
            if (r) flg += 31 - r;
          }
          newZ = new Uint8Array(tail + 4);
          newZ[0] = cmf;
          newZ[1] = flg;
          newZ.set(z.subarray(2, tail), 2);
          putBe32(newZ, tail, realAdler);
        }
        res.idatMerged = !contiguous;
      }
    }

    const pieces = [];
    for (let i = 0; i < chunks.length; i++) {
      const c = chunks[i];
      if (c.privateAncillary) { res.removed.push(c.type); continue; }
      if (c.type === 'IDAT' && newZ) {
        if (i === idat[0]) pieces.push({ type: 'IDAT', body: newZ });
        continue;
      }
      pieces.push({ type: c.type, body: d.subarray(c.start, c.start + c.len) });
    }

    if (!res.badCrcChunks && !res.removed.length && !res.trailing && !newZ) return res;

    let size = 8;
    for (const p of pieces) size += 12 + p.body.length;
    const out = new Uint8Array(size);
    out.set(PNG_SIGNATURE, 0);
    let q = 8;
    for (const p of pieces) {
      const n = p.body.length;
      putBe32(out, q, n);
      for (let k = 0; k < 4; k++) out[q + 4 + k] = p.type.charCodeAt(k);
      out.set(p.body, q + 8);
      putBe32(out, q + 8 + n, crc32(out, q + 4, q + 8 + n));
      q += 12 + n;
    }
    res.data = out;
    res.changed = true;
    return res;
  }

  // ---------------------------------------------------------------------------
  // ZIP reading (mirrors java.util.zip.ZipFile, which Minecraft uses)
  // ---------------------------------------------------------------------------
  function findEnd(d) {
    // Same search window as Java: the EOCD record plus a comment of up to 64 KB.
    const min = Math.max(0, d.length - 22 - 0xffff);
    for (let i = d.length - 22; i >= min; i--) {
      if (d[i] !== 0x50 || d[i + 1] !== 0x4b || d[i + 2] !== 5 || d[i + 3] !== 6) continue;
      let count = u16(d, i + 10), cdSize = u32(d, i + 12), cdOff = u32(d, i + 16);
      let endPos = i;
      if (i >= 20 && u32(d, i - 20) === SIG_EOCD64_LOC) {
        const z = u64(d, i - 12);
        if (z + 56 <= d.length && u32(d, z) === SIG_EOCD64) {
          count = u64(d, z + 32); cdSize = u64(d, z + 40); cdOff = u64(d, z + 48);
          endPos = z;
        }
      }
      // Java locates the central directory as "end record minus its size" and
      // treats any difference to the stored offset as data prepended to the zip.
      let cdPos = endPos - cdSize;
      if (cdPos < 0) continue;
      if (cdSize && u32(d, cdPos) !== SIG_CENTRAL) {
        if (cdOff + 4 <= d.length && u32(d, cdOff) === SIG_CENTRAL) cdPos = cdOff;
        else continue;
      }
      const base = cdPos - cdOff;
      if (base < 0) continue;
      return { cdPos, cdEnd: cdPos + cdSize, count, base };
    }
    return null;
  }

  const textDecoder = typeof TextDecoder === 'function' ? new TextDecoder('utf-8') : null;
  function decodeName(bytes) {
    if (textDecoder) return textDecoder.decode(bytes);
    return String.fromCharCode.apply(null, bytes);
  }

  function readCentral(d, end, s) {
    const list = [];
    let p = end.cdPos;
    while (p + 46 <= end.cdEnd && u32(d, p) === SIG_CENTRAL) {
      const nlen = u16(d, p + 28), xlen = u16(d, p + 30), clen = u16(d, p + 32);
      if (p + 46 + nlen + xlen + clen > d.length) break;
      const e = {
        flags: u16(d, p + 8), method: u16(d, p + 10),
        time: u16(d, p + 12), date: u16(d, p + 14),
        crc: u32(d, p + 16), csize: u32(d, p + 20), usize: u32(d, p + 24),
        disk: u16(d, p + 34), offset: u32(d, p + 42),
        nameBytes: d.subarray(p + 46, p + 46 + nlen),
      };
      e.name = decodeName(e.nameBytes);
      // Zip64 extra field carries the real values when the 32-bit ones are maxed out.
      let x = p + 46 + nlen;
      const xend = x + xlen;
      while (x + 4 <= xend) {
        const id = u16(d, x), sz = u16(d, x + 2);
        if (id === 0x0001) {
          let q = x + 4;
          if (e.usize === 0xffffffff && q + 8 <= x + 4 + sz) { e.usize = u64(d, q); q += 8; }
          if (e.csize === 0xffffffff && q + 8 <= x + 4 + sz) { e.csize = u64(d, q); q += 8; }
          if (e.offset === 0xffffffff && q + 8 <= x + 4 + sz) { e.offset = u64(d, q); q += 8; }
        }
        x += 4 + sz;
      }
      list.push(e);
      p += 46 + nlen + xlen + clen;
    }
    if (list.length < end.count) s.warnings.push('Central directory lists ' + end.count + ' files but only ' + list.length + ' could be read.');
    return list;
  }

  const validDosDate = (date, time) => {
    const day = date & 31, month = (date >> 5) & 15;
    const sec = (time & 31) * 2, min = (time >> 5) & 63, hour = time >> 11;
    return day >= 1 && month >= 1 && month <= 12 && sec < 60 && min < 60 && hour < 24;
  };
  const isEpoch = (date, time) => date === 0x21 && time === 0; // 1980-01-01 00:00
  function dosNow() {
    const t = new Date();
    return {
      date: ((Math.max(1980, t.getFullYear()) - 1980) << 9) | ((t.getMonth() + 1) << 5) | t.getDate(),
      time: (t.getHours() << 11) | (t.getMinutes() << 5) | (t.getSeconds() >> 1),
    };
  }

  function sameBytes(d, start, len, other) {
    if (len !== other.length) return false;
    for (let i = 0; i < len; i++) if (d[start + i] !== other[i]) return false;
    return true;
  }

  async function readEntry(d, c, end, s) {
    let loc = end.base + c.offset;
    if (loc + 30 > d.length || u32(d, loc) !== SIG_LOCAL) {
      if (end.base && c.offset + 30 <= d.length && u32(d, c.offset) === SIG_LOCAL) loc = c.offset;
      else throw new Error('local header not found');
    }
    const lFlags = u16(d, loc + 6), lMethod = u16(d, loc + 8);
    const lTime = u16(d, loc + 10), lDate = u16(d, loc + 12);
    const lCrc = u32(d, loc + 14), lCsize = u32(d, loc + 18), lUsize = u32(d, loc + 22);
    const lNlen = u16(d, loc + 26), lXlen = u16(d, loc + 28);
    // Like Java: the local header's name/extra *lengths* decide where the data starts.
    const start = loc + 30 + lNlen + lXlen;
    if (start > d.length) throw new Error('local header points past the end of the file');

    if (!sameBytes(d, loc + 30, lNlen, c.nameBytes)) {
      s.localNames++;
      if (!s.localNameExample) s.localNameExample = { local: decodeName(d.subarray(loc + 30, loc + 30 + Math.min(lNlen, 80))), central: c.name };
    }
    if (((lFlags & 1) && !(c.flags & 1)) || lMethod !== c.method) s.localMeta++;
    if (c.disk !== 0) { s.disk++; s.diskValues.set(c.disk, (s.diskValues.get(c.disk) || 0) + 1); }

    let raw, comp, consumed;
    if (c.method === 8) {
      const inf = inflateRaw(d, start, d.length, { sizeHint: Math.min(c.usize, 64 << 20) });
      raw = inf.data;
      consumed = inf.consumed;
      comp = d.subarray(start, start + consumed);
    } else if (c.method === 0) {
      if (start + c.csize > d.length) throw new Error('data runs past the end of the file');
      raw = d.subarray(start, start + c.csize);
      consumed = c.csize;
      comp = raw;
    } else {
      throw new Error('unsupported compression method ' + c.method);
    }

    const crc = crc32(raw);
    if (crc !== c.crc) { s.crc++; if (c.crc === 0) s.crcZero++; }
    if (raw.length !== c.usize) { s.usize++; s.usizeValues.set(c.usize, (s.usizeValues.get(c.usize) || 0) + 1); }
    if (consumed !== c.csize) s.csize++;
    if (c.flags & 8) {
      let q = start + consumed;
      if (q + 4 <= d.length && u32(d, q) === SIG_DESCRIPTOR) q += 4;
      if (q + 12 <= d.length && u32(d, q) === crc && c.crc !== crc) s.realInDescriptor++;
    } else if (lCrc !== crc || lCsize !== consumed || lUsize !== raw.length) {
      s.localSizes++;
    }

    // Timestamps: the central directory copy is often zeroed, the local one isn't.
    let time = c.time, date = c.date;
    if (!validDosDate(date, time) || isEpoch(date, time)) {
      if (validDosDate(lDate, lTime) && !isEpoch(lDate, lTime)) { date = lDate; time = lTime; s.timeRestored++; }
      else if (!validDosDate(date, time)) { const t = dosNow(); date = t.date; time = t.time; }
    }

    const entry = { name: c.name, method: c.method, crc, csize: comp.length, usize: raw.length, data: comp, time, date };
    if (isPng(raw)) {
      s.png++;
      const fx = await fixPng(raw);
      if (fx) {
        if (fx.badCrcChunks) { s.pngCrcFiles++; s.pngCrcChunks += fx.badCrcChunks; fx.crcKeys.forEach((k) => s.pngCrcKeys.add(k)); }
        if (fx.badAdler) { s.pngAdler++; if (fx.adlerKey !== null) s.pngAdlerKeys.add(fx.adlerKey); }
        for (const t of fx.removed) s.pngRemoved.set(t, (s.pngRemoved.get(t) || 0) + 1);
        if (fx.trailing) s.pngTrailing++;
        if (fx.badWindow) s.pngWindow++;
        if (fx.zlibTrailing) s.pngZlibTrailing++;
        if (fx.recompressed) s.pngRecompressed++;
        if (fx.idatMerged) s.pngIdatMerged++;
        if (fx.changed) {
          s.pngFixed++;
          entry.method = 0; // PNG data is already compressed; store it as-is
          entry.data = fx.data;
          entry.csize = entry.usize = fx.data.length;
          entry.crc = crc32(fx.data);
        }
      } else {
        s.pngSkipped++;
      }
    }
    return entry;
  }

  // ---------------------------------------------------------------------------
  // File names
  // ---------------------------------------------------------------------------
  const WIN_RESERVED = /^(con|prn|aux|nul|com[0-9¹²³]|lpt[0-9¹²³])(\.|$)/i;
  const MC_PATH = /^[a-z0-9_.\-/]+$/;

  // Makes a name safe to extract on any OS. Unsafe parts are replaced, never
  // resolved, so a decoy like "/assets/x.png" can't turn into a real path.
  function safeName(name) {
    const segs = name.split('/');
    for (let i = 0; i < segs.length; i++) {
      let seg = segs[i];
      if (seg === '' || seg === '.' || seg === '..') seg = seg.replace(/\./g, '_') || '_';
      seg = seg.replace(/[\x00-\x1f<>:"\\|?*\x7f]/g, '_');
      seg = seg.replace(/[. ]+$/, (m) => '_'.repeat(m.length));
      if (WIN_RESERVED.test(seg)) seg = '_' + seg;
      segs[i] = seg;
    }
    return segs.join('/');
  }

  // Resolves names that clash on case-insensitive file systems, and files whose
  // name equals a folder ("assets" as a file next to "assets/..."). Names Minecraft
  // can actually load get priority; the others get a "~N" suffix.
  function resolveClashes(entries, s) {
    const dirs = new Set();
    for (const e of entries) {
      let i = -1;
      while ((i = e.name.indexOf('/', i + 1)) !== -1) dirs.add(e.name.slice(0, i).toLowerCase());
    }
    const taken = new Set();
    const order = entries.slice().sort((a, b) => (MC_PATH.test(b.name) ? 1 : 0) - (MC_PATH.test(a.name) ? 1 : 0));
    for (const e of order) {
      const key = e.name.toLowerCase();
      if (!taken.has(key) && !dirs.has(key)) { taken.add(key); continue; }
      const slash = e.name.lastIndexOf('/'), dot = e.name.lastIndexOf('.');
      const hasExt = dot > slash + 1;
      const stem = hasExt ? e.name.slice(0, dot) : e.name, ext = hasExt ? e.name.slice(dot) : '';
      let n = 1, cand;
      do { cand = stem + '~' + n++ + ext; } while (taken.has(cand.toLowerCase()) || dirs.has(cand.toLowerCase()));
      s.renamed.push(e.name + ' → ' + cand);
      e.name = cand;
      taken.add(cand.toLowerCase());
    }
  }

  // ---------------------------------------------------------------------------
  // ZIP writing
  // ---------------------------------------------------------------------------
  function buildZip(entries) {
    const enc = new TextEncoder();
    const parts = [];
    const central = [];
    let offset = 0;
    for (const e of entries) {
      const name = enc.encode(e.name);
      const flags = name.length !== e.name.length ? 0x0800 : 0; // UTF-8 names
      const version = e.method === 8 ? 20 : 10;
      if (offset > 0xfffffffe || e.usize > 0xfffffffe) throw new Error('Packs larger than 4 GB are not supported.');
      const h = new Uint8Array(30 + name.length);
      const v = new DataView(h.buffer);
      v.setUint32(0, SIG_LOCAL, true);
      v.setUint16(4, version, true);
      v.setUint16(6, flags, true);
      v.setUint16(8, e.method, true);
      v.setUint16(10, e.time, true);
      v.setUint16(12, e.date, true);
      v.setUint32(14, e.crc, true);
      v.setUint32(18, e.csize, true);
      v.setUint32(22, e.usize, true);
      v.setUint16(26, name.length, true);
      v.setUint16(28, 0, true);
      h.set(name, 30);
      central.push({ e, name, flags, version, offset });
      parts.push(h, e.data);
      offset += h.length + e.data.length;
    }
    const cdStart = offset;
    for (const c of central) {
      const h = new Uint8Array(46 + c.name.length);
      const v = new DataView(h.buffer);
      v.setUint32(0, SIG_CENTRAL, true);
      v.setUint16(4, 20, true); // made by: MS-DOS / spec 2.0
      v.setUint16(6, c.version, true);
      v.setUint16(8, c.flags, true);
      v.setUint16(10, c.e.method, true);
      v.setUint16(12, c.e.time, true);
      v.setUint16(14, c.e.date, true);
      v.setUint32(16, c.e.crc, true);
      v.setUint32(20, c.e.csize, true);
      v.setUint32(24, c.e.usize, true);
      v.setUint16(28, c.name.length, true);
      // extra length, comment length, disk number, internal/external attributes: all 0
      v.setUint32(42, c.offset, true);
      h.set(c.name, 46);
      parts.push(h);
      offset += h.length;
    }
    const cdSize = offset - cdStart;
    const count = central.length;
    if (count > 0xfffe || cdStart > 0xfffffffe || cdSize > 0xfffffffe) {
      const z = new Uint8Array(56 + 20);
      const v = new DataView(z.buffer);
      v.setUint32(0, SIG_EOCD64, true);
      v.setBigUint64(4, 44n, true);
      v.setUint16(12, 45, true);
      v.setUint16(14, 45, true);
      v.setBigUint64(24, BigInt(count), true);
      v.setBigUint64(32, BigInt(count), true);
      v.setBigUint64(40, BigInt(cdSize), true);
      v.setBigUint64(48, BigInt(cdStart), true);
      v.setUint32(56, SIG_EOCD64_LOC, true);
      v.setBigUint64(64, BigInt(offset), true);
      v.setUint32(72, 1, true);
      parts.push(z);
      offset += z.length;
    }
    const eocd = new Uint8Array(22);
    const v = new DataView(eocd.buffer);
    v.setUint32(0, SIG_EOCD, true);
    v.setUint16(8, Math.min(count, 0xffff), true);
    v.setUint16(10, Math.min(count, 0xffff), true);
    v.setUint32(12, Math.min(cdSize, 0xffffffff), true);
    v.setUint32(16, Math.min(cdStart, 0xffffffff), true);
    parts.push(eocd);
    offset += 22;
    return { parts, size: offset };
  }

  // ---------------------------------------------------------------------------
  // Report
  // ---------------------------------------------------------------------------
  function topKey(map) {
    let best = null, n = -1;
    map.forEach((v, k) => { if (v > n) { n = v; best = k; } });
    return best;
  }

  function buildReport(s, info) {
    const f = [];
    const add = (id, group, title, count, detail, unit) => {
      if (count) f.push({ id, group, title, count, detail: detail || '', unit: unit === undefined ? (group === 'png' ? 'pngs' : 'files') : unit });
    };
    const ex = s.localNameExample;
    const short = (t) => (t.length > 24 ? t.slice(0, 24) + '…' : t);
    add('local-names', 'zip', 'Fake file names in local headers', s.localNames,
      ex ? 'e.g. "' + short(ex.local) + '" instead of "' + ex.central + '"' : '');
    add('crc', 'zip', 'Wrong CRC-32 checksums', s.crc,
      (s.crcZero === s.crc ? 'all set to 00000000' : '') +
      (s.realInDescriptor ? (s.crcZero === s.crc ? '; ' : '') + 'real values were hidden in data descriptors' : ''));
    const us = topKey(s.usizeValues);
    add('usize', 'zip', 'Fake uncompressed sizes', s.usize,
      s.usizeValues.size === 1 ? 'each claimed to be ' + us + ' bytes' : 'most common fake value: ' + us + ' bytes');
    add('disk', 'zip', 'Bogus disk number (fake multi-volume archive)', s.disk, 'volume #' + topKey(s.diskValues));
    add('csize', 'zip', 'Wrong compressed sizes', s.csize, '');
    add('local-meta', 'zip', 'Fake encryption flag / method in local headers', s.localMeta, '');
    add('local-sizes', 'zip', 'Wrong sizes or CRC in local headers', s.localSizes, '');
    add('timestamps', 'zip', 'Zeroed timestamps', s.timeRestored, 'restored from the local headers');
    add('shift', 'zip', 'Junk data in front of the archive', s.shift ? 1 : 0, s.shift + ' bytes', null);
    add('duplicates', 'zip', 'Duplicate entries', s.duplicates, 'kept the copy Minecraft loads (the last one)');
    add('names', 'zip', 'Unsafe or clashing file names', s.renamed.length,
      s.renamed.slice(0, 3).join(', ') + (s.renamed.length > 3 ? ', …' : ''));

    const keyNote = (set) => (set.size === 1 ? 'XOR-ed with 0x' + hex32([...set][0]) : '');
    add('png-crc', 'png', 'PNG chunks with wrong CRC', s.pngCrcFiles,
      s.pngCrcChunks + ' chunks' + (keyNote(s.pngCrcKeys) ? ', all ' + keyNote(s.pngCrcKeys) : ''));
    add('png-adler', 'png', 'Wrong Adler-32 in PNG pixel data', s.pngAdler,
      keyNote(s.pngAdlerKeys) ? 'all ' + keyNote(s.pngAdlerKeys) : '');
    const removed = [...s.pngRemoved.keys()];
    add('png-chunks', 'png', 'Private marker chunks', s.pngRemoved.size ? [...s.pngRemoved.values()].reduce((a, b) => a + b, 0) : 0,
      'removed: ' + removed.join(', '), 'chunks');
    add('png-trailing', 'png', 'Junk data after the end of a PNG', s.pngTrailing, '');
    add('png-window', 'png', 'Fake zlib window size in PNG data', s.pngWindow, '');
    add('png-zlib-trailing', 'png', 'Junk after PNG pixel data', s.pngZlibTrailing, '');
    add('png-recompressed', 'png', 'Non-standard deflate streams in PNGs', s.pngRecompressed, 'recompressed');
    add('png-idat', 'png', 'Interleaved IDAT chunks', s.pngIdatMerged, 'merged');

    return {
      findings: f,
      warnings: s.warnings.concat(s.broken.map((b) => 'Skipped unreadable file ' + b)),
      files: info.files,
      written: info.written,
      directories: s.dirs,
      png: s.png,
      pngFixed: s.pngFixed,
      inputSize: info.inputSize,
      outputSize: info.outputSize,
    };
  }

  // ---------------------------------------------------------------------------
  // Main entry point
  // ---------------------------------------------------------------------------
  async function unlock(input, opts) {
    opts = opts || {};
    const progress = opts.onProgress || function () {};
    const d = input instanceof Uint8Array ? input : new Uint8Array(input);
    const s = {
      warnings: [], broken: [],
      localNames: 0, localNameExample: null, localMeta: 0, localSizes: 0,
      crc: 0, crcZero: 0, realInDescriptor: 0, usize: 0, usizeValues: new Map(), csize: 0,
      disk: 0, diskValues: new Map(), timeRestored: 0, shift: 0, duplicates: 0, dirs: 0, renamed: [],
      png: 0, pngFixed: 0, pngSkipped: 0, pngCrcFiles: 0, pngCrcChunks: 0, pngCrcKeys: new Set(),
      pngAdler: 0, pngAdlerKeys: new Set(), pngRemoved: new Map(), pngTrailing: 0, pngWindow: 0,
      pngZlibTrailing: 0, pngRecompressed: 0, pngIdatMerged: 0,
    };

    const end = findEnd(d);
    if (!end) throw new Error('This is not a ZIP file (no end-of-central-directory record found).');
    s.shift = end.base;
    const cen = readCentral(d, end, s);
    if (!cen.length) throw new Error('The archive\'s file list (central directory) is empty or unreadable.');

    const kept = new Map(); // name -> entry; for duplicates the last one wins, like Java's ZipFile.getEntry
    let tick = now();
    for (let i = 0; i < cen.length; i++) {
      if (now() - tick > 40) {
        progress(i / cen.length, 'Repairing file ' + i + ' of ' + cen.length);
        await yieldToUi();
        tick = now();
      }
      const c = cen[i];
      if (c.name.endsWith('/')) { s.dirs++; continue; } // folders are recreated implicitly
      let entry;
      try { entry = await readEntry(d, c, end, s); }
      catch (err) { s.broken.push(c.name + ' (' + err.message + ')'); continue; }
      if (kept.has(c.name)) s.duplicates++;
      kept.set(c.name, entry);
    }

    progress(1, 'Writing archive');
    const entries = [...kept.values()];
    for (const e of entries) {
      const safe = safeName(e.name);
      if (safe !== e.name) { s.renamed.push(e.name + ' → ' + safe); e.name = safe; }
    }
    resolveClashes(entries, s);
    if (!entries.length) throw new Error('No readable files were found in this archive.');

    const zip = buildZip(entries);
    const report = buildReport(s, { files: cen.length, written: entries.length, inputSize: d.length, outputSize: zip.size });
    return { parts: zip.parts, size: zip.size, report };
  }

  return { unlock, fixPng, inflateRaw, crc32, adler32 };
});
