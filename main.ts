// PngSqueeze: a lossless PNG encoder that rewrites screenshots into the
// smallest PNG it can.
//
// The program reads every 1280x720 RGBA screenshot under /input/<id>/ and
// writes its answer as /output/<id>/image.png. For each image it:
//   - reduces the colour type (a palette of at most 256 colours, grey,
//     grey with alpha, RGB, or RGBA, with a tRNS transparency key where one
//     applies), because a palette or a narrower type holds the same pixels
//     in far fewer bytes;
//   - tries several per-row filter choices (fixed filters, the minimum-sum
//     and fewest-pairs heuristics, and a brute-force search that weighs each
//     filter by actually compressing the row) and keeps the smallest by a
//     fast zlib screen;
//   - compresses the winner with a purpose-built deflate encoder: lazy
//     hash-chain matching, a dynamic-programming optimal parse over the
//     token stream, and per-block dynamic Huffman tables.
//
// Everything is deterministic: every choice is a fixed function of the
// input bytes, never of the clock or the environment. Node's built-in
// modules only; nothing is read from the network or from outside /input,
// /bot and /output.

import { mkdirSync, readdirSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';
import { deflateSync, inflateSync } from 'node:zlib';

// ---------------------------------------------------------------------------
// DEFLATE tables (RFC 1951)
// ---------------------------------------------------------------------------

const LEN_BASE = [3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 15, 17, 19, 23, 27, 31, 35, 43, 51, 59, 67, 83, 99, 115, 131, 163, 195, 227, 258];
const LEN_EXTRA = [0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 2, 2, 2, 2, 3, 3, 3, 3, 4, 4, 4, 4, 5, 5, 5, 5, 0];
const DIST_BASE = [1, 2, 3, 4, 5, 7, 9, 13, 17, 25, 33, 49, 65, 97, 129, 193, 257, 385, 513, 769, 1025, 1537, 2049, 3073, 4097, 6145, 8193, 12289, 16385, 24577];
const DIST_EXTRA = [0, 0, 0, 0, 1, 1, 2, 2, 3, 3, 4, 4, 5, 5, 6, 6, 7, 7, 8, 8, 9, 9, 10, 10, 11, 11, 12, 12, 13, 13];
const CL_ORDER = [16, 17, 18, 0, 8, 7, 9, 6, 10, 5, 11, 4, 12, 3, 13, 2, 14, 1, 15];

// Match length -> length symbol offset (0..28, symbol is 257 + offset) and extra bits.
const LEN_SYM = new Uint8Array(259);
const LEN_EXT = new Uint8Array(259);
for (let s = 0; s < 29; s++) {
  const count = 1 << LEN_EXTRA[s];
  for (let k = 0; k < count; k++) {
    const l = LEN_BASE[s] + k;
    if (l <= 258) { LEN_SYM[l] = s; LEN_EXT[l] = LEN_EXTRA[s]; }
  }
}
LEN_SYM[258] = 28; LEN_EXT[258] = 0;

// Distance -> distance symbol (0..29) and extra bits.
const DIST_SYM = new Uint16Array(32769);
const DIST_EXT = new Uint8Array(32769);
for (let s = 0; s < 30; s++) {
  const count = 1 << DIST_EXTRA[s];
  for (let k = 0; k < count; k++) {
    const d = DIST_BASE[s] + k;
    if (d <= 32768) { DIST_SYM[d] = s; DIST_EXT[d] = DIST_EXTRA[s]; }
  }
}

// The largest match length in each length code's range (the breakpoints a
// dynamic program needs: within a range the length code costs the same).
const LEN_BP = [3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 15, 17, 19, 23, 27, 31, 35, 43, 51, 59, 67, 83, 99, 115, 131, 163, 195, 227, 258];

const HASH_BITS = 15;
const HASH_SIZE = 1 << HASH_BITS;
const HASH_MASK = HASH_SIZE - 1;
const WINDOW = 32768;
const MAX_MATCH = 258;
const MIN_MATCH = 3;

// A token is one Int32: a literal byte (0..255), or a match packed as
// (1 << 25) | (length << 16) | distance.
const MATCH_FLAG = 1 << 25;

// ---------------------------------------------------------------------------
// Checksums and PNG framing
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

/** CRC-32 (ISO 3309, PNG's) of bytes[start, end). */
function crc32(bytes, start = 0, end = bytes.length) {
  let c = -1;
  for (let i = start; i < end; i++) c = CRC_TABLE[(c ^ bytes[i]) & 0xff] ^ (c >>> 8);
  return (c ^ -1) >>> 0;
}

/** Adler-32 (zlib's) of bytes. */
function adler32(data) {
  let a = 1, b = 0;
  for (let i = 0; i < data.length;) {
    const end = Math.min(data.length, i + 5552);
    for (; i < end; i++) { a += data[i]; b += a; }
    a %= 65521; b %= 65521;
  }
  return ((b << 16) | a) >>> 0;
}

const PNG_SIGNATURE = Uint8Array.of(137, 80, 78, 71, 13, 10, 26, 10);
const CHANNELS = { 0: 1, 2: 3, 3: 1, 4: 2, 6: 4 };
const ascii = (s) => Uint8Array.from(s, (ch) => ch.charCodeAt(0));

/** A PNG file of `chunks`, each [type, data]. */
function pngOf(chunks) {
  let size = PNG_SIGNATURE.length;
  for (const [, data] of chunks) size += 12 + data.length;
  const out = new Uint8Array(size);
  const view = new DataView(out.buffer);
  out.set(PNG_SIGNATURE, 0);
  let at = PNG_SIGNATURE.length;
  for (const [type, data] of chunks) {
    view.setUint32(at, data.length);
    out.set(ascii(type), at + 4);
    out.set(data, at + 8);
    view.setUint32(at + 8 + data.length, crc32(out, at + 4, at + 8 + data.length));
    at += 12 + data.length;
  }
  return out;
}

/** IHDR's data: width, height, bit depth 8, the colour type, compression 0, filter 0, no interlace. */
function ihdrOf(width, height, colourType) {
  const d = new Uint8Array(13);
  const v = new DataView(d.buffer);
  v.setUint32(0, width);
  v.setUint32(4, height);
  d[8] = 8;
  d[9] = colourType;
  return d;
}

// ---------------------------------------------------------------------------
// PNG decoding (bit depth 8, non-interlaced, colour types 0, 2, 3, 4, 6)
// ---------------------------------------------------------------------------

/** The Paeth predictor of PNG's filter 4. */
function paeth(a, b, c) {
  const p = a + b - c;
  const pa = p > a ? p - a : a - p;
  const pb = p > b ? p - b : b - p;
  const pc = p > c ? p - c : c - p;
  if (pa <= pb && pa <= pc) return a;
  return pb <= pc ? b : c;
}

/**
 * The image a PNG holds, as RGBA (4 bytes a pixel, rows top to bottom),
 * or why it is not one this program reads.
 */
function decodePng(bytes) {
  const fail = (why) => ({ ok: false, why });
  if (!(bytes instanceof Uint8Array)) return fail('it is not bytes');
  if (bytes.length < PNG_SIGNATURE.length || PNG_SIGNATURE.some((b, i) => bytes[i] !== b)) {
    return fail('it does not start with the PNG signature');
  }
  const view = new DataView(bytes.buffer, bytes.byteOffset, bytes.byteLength);
  let at = PNG_SIGNATURE.length;
  let header = null;
  let palette = null;
  let trns = null;
  const idat = [];
  let idatDone = false;
  let ended = false;
  const known = ['IHDR', 'PLTE', 'tRNS', 'IDAT', 'IEND'];
  while (at < bytes.length) {
    if (ended) return fail('it holds bytes after IEND');
    if (at + 12 > bytes.length) return fail('a chunk is cut short');
    const len = view.getUint32(at);
    if (len > 0x7fffffff || at + 12 + len > bytes.length) return fail('a chunk claims bytes the file does not hold');
    const type = String.fromCharCode(bytes[at + 4], bytes[at + 5], bytes[at + 6], bytes[at + 7]);
    if (!/^[A-Za-z]{4}$/.test(type)) return fail('a chunk has no chunk type');
    if (crc32(bytes, at + 4, at + 8 + len) !== view.getUint32(at + 8 + len)) return fail(`the ${type} chunk fails its CRC`);
    const data = bytes.subarray(at + 8, at + 8 + len);
    at += 12 + len;
    if (!known.includes(type)) return fail(`it holds a ${type} chunk, which is not read`);
    if (header === null && type !== 'IHDR') return fail('its first chunk is not IHDR');
    if (type !== 'IDAT' && idat.length > 0) idatDone = true;
    if (type === 'IHDR') {
      if (header !== null) return fail('it holds IHDR twice');
      if (len !== 13) return fail('its IHDR is not 13 bytes');
      const dv = new DataView(data.buffer, data.byteOffset, 13);
      header = { width: dv.getUint32(0), height: dv.getUint32(4), depth: data[8], colourType: data[9], compression: data[10], filter: data[11], interlace: data[12] };
      if (header.width === 0 || header.height === 0) return fail('its width or height is 0');
      if (header.depth !== 8) return fail('its bit depth is not 8');
      if (!Object.hasOwn(CHANNELS, header.colourType)) return fail('its colour type is not 0, 2, 3, 4 or 6');
      if (header.compression !== 0 || header.filter !== 0) return fail('its compression or filter method is not 0');
      if (header.interlace !== 0) return fail('it is interlaced');
    } else if (type === 'PLTE') {
      if (palette !== null) return fail('it holds PLTE twice');
      if (header.colourType !== 3) return fail('it holds PLTE with a colour type other than 3');
      if (idat.length > 0) return fail('its PLTE follows IDAT');
      if (len === 0 || len % 3 !== 0 || len > 768) return fail('its PLTE is not 1 to 256 entries of 3 bytes');
      palette = data;
    } else if (type === 'tRNS') {
      if (trns !== null) return fail('it holds tRNS twice');
      if (idat.length > 0) return fail('its tRNS follows IDAT');
      const ct = header.colourType;
      if (ct === 3) {
        if (palette === null) return fail('its tRNS comes before PLTE');
        if (len > palette.length / 3) return fail('its tRNS holds more entries than its palette');
      } else if (ct === 0 || ct === 2) {
        if (len !== (ct === 0 ? 2 : 6)) return fail('its tRNS has the wrong length for its colour type');
        for (let i = 0; i < len; i += 2) if (data[i] !== 0) return fail('its tRNS names a sample over 255');
      } else return fail(`it holds tRNS with colour type ${ct}`);
      trns = data;
    } else if (type === 'IDAT') {
      if (idatDone) return fail('its IDAT chunks are not in a row');
      if (header.colourType === 3 && palette === null) return fail('its IDAT comes before PLTE');
      idat.push(data);
    } else {
      if (len !== 0) return fail('its IEND is not empty');
      ended = true;
    }
  }
  if (!ended) return fail('it has no IEND');
  if (idat.length === 0) return fail('it has no IDAT');
  const { width, height, colourType } = header;
  const bpp = CHANNELS[colourType];
  const stride = width * bpp;
  const expected = height * (stride + 1);
  let raw;
  try {
    raw = inflateSync(idat.length === 1 ? idat[0] : Buffer.concat(idat), { maxOutputLength: expected + 1 });
  } catch (err) {
    return fail(`its IDAT data is not one whole zlib stream (${String(err && err.message).split('\n')[0]})`);
  }
  if (raw.length !== expected) return fail(`its IDAT data inflates to ${raw.length} bytes, not ${expected}`);

  // Unfilter in place, row by row.
  const samples = new Uint8Array(height * stride);
  for (let y = 0; y < height; y++) {
    const ft = raw[y * (stride + 1)];
    if (ft > 4) return fail(`row ${y} has filter type ${ft}`);
    const src = y * (stride + 1) + 1;
    const o = y * stride;
    const p = o - stride;
    if (ft === 0) samples.set(raw.subarray(src, src + stride), o);
    else if (ft === 1) {
      for (let i = 0; i < stride; i++) samples[o + i] = raw[src + i] + (i >= bpp ? samples[o + i - bpp] : 0);
    } else if (ft === 2) {
      for (let i = 0; i < stride; i++) samples[o + i] = raw[src + i] + (y > 0 ? samples[p + i] : 0);
    } else if (ft === 3) {
      for (let i = 0; i < stride; i++) samples[o + i] = raw[src + i] + (((i >= bpp ? samples[o + i - bpp] : 0) + (y > 0 ? samples[p + i] : 0)) >> 1);
    } else {
      for (let i = 0; i < stride; i++) {
        const a = i >= bpp ? samples[o + i - bpp] : 0;
        const b = y > 0 ? samples[p + i] : 0;
        const c = y > 0 && i >= bpp ? samples[p + i - bpp] : 0;
        samples[o + i] = raw[src + i] + paeth(a, b, c);
      }
    }
  }

  // Expand to RGBA.
  const n = width * height;
  const rgba = new Uint8Array(n * 4);
  if (colourType === 6) rgba.set(samples);
  else if (colourType === 2) {
    const key = trns === null ? -1 : (trns[1] << 16) | (trns[3] << 8) | trns[5];
    for (let i = 0, s = 0, d = 0; i < n; i++, s += 3, d += 4) {
      rgba[d] = samples[s];
      rgba[d + 1] = samples[s + 1];
      rgba[d + 2] = samples[s + 2];
      rgba[d + 3] = ((samples[s] << 16) | (samples[s + 1] << 8) | samples[s + 2]) === key ? 0 : 255;
    }
  } else if (colourType === 0) {
    const key = trns === null ? -1 : trns[1];
    for (let i = 0, d = 0; i < n; i++, d += 4) {
      const g = samples[i];
      rgba[d] = rgba[d + 1] = rgba[d + 2] = g;
      rgba[d + 3] = g === key ? 0 : 255;
    }
  } else if (colourType === 4) {
    for (let i = 0, s = 0, d = 0; i < n; i++, s += 2, d += 4) {
      rgba[d] = rgba[d + 1] = rgba[d + 2] = samples[s];
      rgba[d + 3] = samples[s + 1];
    }
  } else {
    const entries = palette.length / 3;
    const lut = new Uint8Array(entries * 4);
    for (let e = 0; e < entries; e++) {
      lut[e * 4] = palette[e * 3];
      lut[e * 4 + 1] = palette[e * 3 + 1];
      lut[e * 4 + 2] = palette[e * 3 + 2];
      lut[e * 4 + 3] = trns !== null && e < trns.length ? trns[e] : 255;
    }
    for (let i = 0, d = 0; i < n; i++, d += 4) {
      const e = samples[i];
      if (e >= entries) return fail(`pixel ${i} names palette entry ${e} of ${entries}`);
      rgba[d] = lut[e * 4];
      rgba[d + 1] = lut[e * 4 + 1];
      rgba[d + 2] = lut[e * 4 + 2];
      rgba[d + 3] = lut[e * 4 + 3];
    }
  }
  return { ok: true, width, height, colourType, rgba };
}

// ---------------------------------------------------------------------------
// Filters
// ---------------------------------------------------------------------------

/** Row `cur` (stride samples, bpp a pixel, `prev` the row above or null) filtered by `type` into out[0, stride). */
function filterRow(type, cur, prev, bpp, out) {
  const n = cur.length;
  if (type === 0) out.set(cur);
  else if (type === 1) {
    for (let i = 0; i < n; i++) out[i] = cur[i] - (i >= bpp ? cur[i - bpp] : 0);
  } else if (type === 2) {
    for (let i = 0; i < n; i++) out[i] = cur[i] - (prev === null ? 0 : prev[i]);
  } else if (type === 3) {
    for (let i = 0; i < n; i++) out[i] = cur[i] - (((i >= bpp ? cur[i - bpp] : 0) + (prev === null ? 0 : prev[i])) >> 1);
  } else {
    for (let i = 0; i < n; i++) {
      const a = i >= bpp ? cur[i - bpp] : 0;
      const b = prev === null ? 0 : prev[i];
      const c = prev !== null && i >= bpp ? prev[i - bpp] : 0;
      out[i] = cur[i] - paeth(a, b, c);
    }
  }
}

/** The sum of a filtered row's bytes read as signed (-128 to 127), absolute: the minimum-sum heuristic's cost. */
function signedSum(row) {
  let s = 0;
  for (let i = 0; i < row.length; i++) {
    const v = row[i];
    s += v < 128 ? v : 256 - v;
  }
  return s;
}

// ---------------------------------------------------------------------------
// Colour analysis and the forms an image can be written in
// ---------------------------------------------------------------------------

/** The image's pixels as 32-bit words (a copy when its bytes do not start on a word boundary). */
function wordsOf(rgba) {
  const at = rgba.byteOffset % 4 === 0 ? rgba : rgba.slice();
  return new Uint32Array(at.buffer, at.byteOffset, at.length >>> 2);
}

/** What the image holds: whether every pixel is opaque, whether every pixel is grey, and its colours when at most 256. */
function analyse(rgba) {
  const n = rgba.length >>> 2;
  const u32 = wordsOf(rgba);
  let opaque = true;
  let grey = true;
  const counts = new Map();
  let many = false;
  for (let i = 0, d = 0; i < n; i++, d += 4) {
    if (rgba[d + 3] !== 255) opaque = false;
    if (rgba[d] !== rgba[d + 1] || rgba[d] !== rgba[d + 2]) grey = false;
    if (!many) {
      const c = u32[i];
      const k = counts.get(c);
      if (k === undefined) {
        if (counts.size === 256) many = true;
        else counts.set(c, 1);
      } else counts.set(c, k + 1);
    }
  }
  // A colour as [r, g, b, a] whatever the platform's byte order: read back from the bytes, never from the word.
  const colours = many ? null : [...counts.keys()].map((c) => {
    const b = new Uint8Array(Uint32Array.of(c).buffer);
    return { rgba: [b[0], b[1], b[2], b[3]], word: c, count: counts.get(c) };
  });
  return { opaque, grey, colours };
}

/**
 * The one fully transparent value (grey or RGB) the image may key by tRNS instead of an alpha channel: every pixel
 * opaque or that exact value at alpha 0, and no opaque pixel of the same value. Null when there is none.
 */
function transparentKey(rgba, grey) {
  let key = -1;
  for (let d = 0; d < rgba.length; d += 4) {
    const a = rgba[d + 3];
    if (a === 255) continue;
    if (a !== 0) return null;
    const v = grey ? rgba[d] : (rgba[d] << 16) | (rgba[d + 1] << 8) | rgba[d + 2];
    if (key === -1) key = v;
    else if (key !== v) return null;
  }
  if (key === -1) return null;
  for (let d = 0; d < rgba.length; d += 4) {
    if (rgba[d + 3] !== 255) continue;
    const v = grey ? rgba[d] : (rgba[d] << 16) | (rgba[d + 1] << 8) | rgba[d + 2];
    if (v === key) return null;
  }
  return key;
}

/** The image's samples in colour type `ct` (0, 2, 4 or 6) from its RGBA. */
function samplesOf(rgba, ct) {
  const n = rgba.length >>> 2;
  if (ct === 6) return rgba;
  const ch = ct === 0 ? 1 : ct === 4 ? 2 : 3;
  const out = new Uint8Array(n * ch);
  for (let i = 0, d = 0, s = 0; i < n; i++, d += 4, s += ch) {
    if (ct === 0) out[s] = rgba[d];
    else if (ct === 4) {
      out[s] = rgba[d];
      out[s + 1] = rgba[d + 3];
    } else {
      out[s] = rgba[d];
      out[s + 1] = rgba[d + 1];
      out[s + 2] = rgba[d + 2];
    }
  }
  return out;
}

/** A palette's entries in the order a trial writes them: the transparent ones first (by alpha), then by `order`. */
function paletteOrder(colours, order) {
  const lum = (c) => 299 * c.rgba[0] + 587 * c.rgba[1] + 114 * c.rgba[2];
  return [...colours].sort((x, y) => {
    const ta = x.rgba[3] === 255 ? 1 : 0;
    const tb = y.rgba[3] === 255 ? 1 : 0;
    if (ta !== tb) return ta - tb;
    if (ta === 0 && x.rgba[3] !== y.rgba[3]) return x.rgba[3] - y.rgba[3];
    if (order === 'luminance') return lum(x) - lum(y) || x.word - y.word;
    return y.count - x.count || x.word - y.word;
  });
}

/** The palette form: {plte, trns, indices}. */
function paletteForm(rgba, colours, order) {
  const entries = paletteOrder(colours, order);
  const index = new Map(entries.map((c, i) => [c.word, i]));
  const plte = new Uint8Array(entries.length * 3);
  let transparent = 0;
  entries.forEach((c, i) => {
    plte[i * 3] = c.rgba[0];
    plte[i * 3 + 1] = c.rgba[1];
    plte[i * 3 + 2] = c.rgba[2];
    if (c.rgba[3] !== 255) transparent = i + 1;
  });
  const trns = transparent === 0 ? null : Uint8Array.from(entries.slice(0, transparent), (c) => c.rgba[3]);
  const n = rgba.length >>> 2;
  const u32 = wordsOf(rgba);
  const indices = new Uint8Array(n);
  for (let i = 0; i < n; i++) indices[i] = index.get(u32[i]);
  return { plte, trns, indices };
}

/** The filter choices each form is screened with. */
const FILTERS = {
  palette: [0],
  paletteByLuminance: [0, 'minsum', 'brute'],
  channels: [0, 1, 2, 4, 'minsum', 'pairs', 'brute'],
};

/** The forms the encoder screens for an image: each {colourType, bpp, samples, plte, trns, filters}. */
function formsOf(rgba) {
  const { opaque, grey, colours } = analyse(rgba);
  const forms = [];
  if (colours !== null) {
    for (const [order, filters] of [
      ['count', FILTERS.palette],
      ['luminance', FILTERS.paletteByLuminance],
    ]) {
      const p = paletteForm(rgba, colours, order);
      forms.push({ colourType: 3, bpp: 1, samples: p.indices, plte: p.plte, trns: p.trns, filters });
    }
    if (!grey) return forms;
  }
  const key = opaque ? null : transparentKey(rgba, grey);
  let ct;
  let trns = null;
  if (grey) {
    ct = opaque || key !== null ? 0 : 4;
    if (key !== null) trns = Uint8Array.of(0, key);
  } else {
    ct = opaque || key !== null ? 2 : 6;
    if (key !== null) trns = Uint8Array.of(0, key >>> 16, 0, (key >>> 8) & 0xff, 0, key & 0xff);
  }
  const bpp = { 0: 1, 2: 3, 4: 2, 6: 4 }[ct];
  forms.push({ colourType: ct, bpp, samples: samplesOf(rgba, ct), plte: null, trns, filters: FILTERS.channels });
  return forms;
}

/** The bytes a form's PLTE and tRNS chunks take in its file (each 12 bytes of length, type and CRC around its data). */
const chunkBytes = (form) => (form.plte === null ? 0 : 12 + form.plte.length) + (form.trns === null ? 0 : 12 + form.trns.length);

/** How many bytes written before a row brute force compresses its trials after. */
const BRUTE_CONTEXT = 32768;
/** The zlib level brute force weighs a row's trials at. */
const BRUTE_LEVEL = 4;

/** The zlib setting every choice is screened by. */
const SCREEN = { level: 6, memLevel: 8, strategy: 0 };

/** The fewest-distinct-pairs heuristic's cost: how many distinct pairs of neighbouring bytes a filtered row holds. */
function pairsOf(row, seen, stamp) {
  let n = 0;
  for (let i = 1; i < row.length; i++) {
    const pair = (row[i - 1] << 8) | row[i];
    if (seen[pair] !== stamp) {
      seen[pair] = stamp;
      n++;
    }
  }
  return n;
}

/**
 * The raw data of an image of `samples` (height rows of width x bpp samples), each row behind its filter byte, by
 * `choice`: a filter type (0 to 4) for every row, or 'minsum', 'pairs' or 'brute' (the header), the lower type on a tie.
 */
function filtered(samples, width, height, bpp, choice) {
  const stride = width * bpp;
  const raw = new Uint8Array(height * (stride + 1));
  const trial = Array.from({ length: 5 }, (_, t) => {
    const row = new Uint8Array(stride + 1);
    row[0] = t;
    return row;
  });
  const seen = new Uint32Array(65536);
  let stamp = 0;
  for (let y = 0; y < height; y++) {
    const cur = samples.subarray(y * stride, (y + 1) * stride);
    const prev = y === 0 ? null : samples.subarray((y - 1) * stride, y * stride);
    const at = y * (stride + 1);
    if (typeof choice === 'number') {
      raw[at] = choice;
      filterRow(choice, cur, prev, bpp, raw.subarray(at + 1, at + 1 + stride));
      continue;
    }
    const before = raw.subarray(Math.max(0, at - BRUTE_CONTEXT), at);
    let type = 0;
    let best = Infinity;
    for (let t = 0; t < 5; t++) {
      filterRow(t, cur, prev, bpp, trial[t].subarray(1));
      let cost;
      if (choice === 'minsum') cost = signedSum(trial[t].subarray(1));
      else if (choice === 'pairs') cost = pairsOf(trial[t].subarray(1), seen, ++stamp);
      else cost = deflateSync(trial[t], before.length === 0 ? { level: BRUTE_LEVEL, memLevel: 9 } : { level: BRUTE_LEVEL, memLevel: 9, dictionary: before }).length;
      if (cost < best) {
        best = cost;
        type = t;
      }
    }
    raw.set(trial[type], at);
  }
  return raw;
}

// ---------------------------------------------------------------------------
// A small, fast LZ77 + dynamic-Huffman deflate encoder (RFC 1951)
// ---------------------------------------------------------------------------

/** Length of the match between data starting at a and at b, at most max. */
function matchLength(data, a, b, max) {
  let l = 0;
  // Compare four bytes per iteration; the loop body breaks on the first
  // differing byte, so the cost stays proportional to the match.
  while (l + 4 <= max) {
    if (data[a + l] !== data[b + l]) return l;
    if (data[a + l + 1] !== data[b + l + 1]) return l + 1;
    if (data[a + l + 2] !== data[b + l + 2]) return l + 2;
    if (data[a + l + 3] !== data[b + l + 3]) return l + 3;
    l += 4;
  }
  while (l < max && data[a + l] === data[b + l]) l++;
  return l;
}

/**
 * The best match at position pos. When costLen/costDist are given, a match is
 * scored by its bit cost; otherwise by length (ties: the nearer distance).
 * head/prev are the hash chains; hash is the 3-byte hash at pos. The chain
 * is ordered most-recent-first, so distances only grow as it is walked.
 */
function findMatch(data, pos, hash, head, prev, maxChain, maxLen, costLen, costDist) {
  let bestLen = 0;
  let bestDist = 0;
  let bestScore = Infinity;
  let cand = head[hash];
  let tries = 0;
  while (cand >= 0 && pos - cand <= WINDOW && tries < maxChain) {
    tries++;
    const dist = pos - cand;
    if (bestLen === 0) {
      const len = matchLength(data, pos, cand, maxLen);
      if (len >= MIN_MATCH) {
        if (costLen !== null) {
          const score = costLen[len] + costDist[dist];
          if (score < bestScore) { bestScore = score; bestLen = len; bestDist = dist; }
          if (len >= maxLen) break; // later candidates are farther: no cheaper max-length match
        } else if (len > bestLen) {
          bestLen = len; bestDist = dist;
          if (len >= maxLen) break;
        }
      }
    } else if (data[cand + bestLen] === data[pos + bestLen]) {
      const len = matchLength(data, pos, cand, maxLen);
      if (len >= MIN_MATCH) {
        if (costLen !== null) {
          const score = costLen[len] + costDist[dist];
          if (score < bestScore || (score === bestScore && (len > bestLen || (len === bestLen && dist < bestDist)))) {
            bestScore = score; bestLen = len; bestDist = dist;
          }
          if (len >= maxLen) break;
        } else if (len > bestLen || (len === bestLen && dist < bestDist)) {
          bestLen = len; bestDist = dist;
          if (len >= maxLen) break;
        }
      }
    } else if (costLen !== null) {
      // The byte at bestLen differs, so this candidate's match is at most
      // bestLen long; it can only win on cost, at that length, if its
      // distance is cheap enough. Skip the comparison otherwise.
      if (costLen[bestLen] + costDist[dist] < bestScore) {
        const len = matchLength(data, pos, cand, bestLen);
        if (len >= MIN_MATCH) {
          const score = costLen[len] + costDist[dist];
          if (score < bestScore || (score === bestScore && (len > bestLen || (len === bestLen && dist < bestDist)))) {
            bestScore = score; bestLen = len; bestDist = dist;
          }
        }
      }
    }
    cand = prev[cand];
  }
  return [bestLen, bestDist];
}

/**
 * Tokenize data into literal/match tokens. costLen/costDist (bit costs per
 * length and distance, or null for longest-match mode) steer the choice.
 */
function tokenize(data, costLen, costDist, maxChain) {
  const n = data.length;
  const ops = new Int32Array(n + 1);
  let count = 0;
  const head = new Int32Array(HASH_SIZE).fill(-1);
  const prev = new Int32Array(n);
  if (n < MIN_MATCH) {
    for (let i = 0; i < n; i++) ops[count++] = data[i];
    return { ops, count };
  }
  // Rolling 3-byte hash: h = ((b0 << 10) ^ (b1 << 5) ^ b2) & mask.
  let h = ((data[0] << 10) ^ (data[1] << 5) ^ data[2]) & HASH_MASK;
  let i = 0;
  let curLen = 0, curDist = 0, haveCur = false;
  while (i < n) {
    if (i > n - MIN_MATCH) {
      ops[count++] = data[i];
      i++;
      continue;
    }
    if (!haveCur) {
      const m = findMatch(data, i, h, head, prev, maxChain, Math.min(MAX_MATCH, n - i), costLen, costDist);
      curLen = m[0]; curDist = m[1];
      haveCur = true;
    }
    // Insert position i so the lookahead can match against it (distance 1).
    prev[i] = head[h];
    head[h] = i;
    // Lazy evaluation: a match already this long is taken as it is; only a
    // short match is worth checking against the next position.
    if (curLen >= MIN_MATCH && curLen < 32 && i + 1 <= n - MIN_MATCH) {
      const h2 = ((h << 5) ^ data[i + 3]) & HASH_MASK;
      const m2 = findMatch(data, i + 1, h2, head, prev, maxChain, Math.min(MAX_MATCH, n - i - 1), costLen, costDist);
      if (m2[0] > curLen) {
        ops[count++] = data[i];
        i++;
        h = h2;
        curLen = m2[0]; curDist = m2[1];
        haveCur = true;
        continue;
      }
    }
    if (curLen >= MIN_MATCH) {
      ops[count++] = MATCH_FLAG | (curLen << 16) | curDist;
      // Insert every position the match covers, so later matches can use it.
      const end = i + curLen;
      let hj = h;
      for (let j = i + 1; j < end && j + 2 < n; j++) {
        hj = ((hj << 5) ^ data[j + 2]) & HASH_MASK;
        prev[j] = head[hj];
        head[hj] = j;
      }
      i = end;
      if (i <= n - MIN_MATCH) h = ((data[i] << 10) ^ (data[i + 1] << 5) ^ data[i + 2]) & HASH_MASK;
      haveCur = false;
    } else {
      ops[count++] = data[i];
      i++;
      if (i <= n - MIN_MATCH) h = ((h << 5) ^ data[i + 2]) & HASH_MASK;
      haveCur = false;
    }
  }
  return { ops, count };
}

/**
 * The cheapest tokenization of data under the given Huffman code lengths
 * (litLen per literal/length symbol, distLen per distance symbol).
 * greedyTok[i] holds a match starting at i, packed (length << 16) |
 * distance (0 when none): the parser can always replay it, so it never
 * does worse than the greedy parse under these costs.
 * Returns {ops, count} in the same packed token format as tokenize().
 */
function optimalParse(data, litLen, distLen, maxChain, greedyTok) {
  const n = data.length;
  const lenCost = new Int32Array(259);
  for (let l = 3; l <= 258; l++) lenCost[l] = litLen[257 + LEN_SYM[l]] + LEN_EXT[l];
  const distCost = new Int32Array(32769);
  for (let d = 1; d <= 32768; d++) distCost[d] = distLen[DIST_SYM[d]] + DIST_EXT[d];

  const costs = new Float64Array(n + 1);
  for (let i = 0; i <= n; i++) costs[i] = Infinity;
  costs[0] = 0;
  const choiceLen = new Uint16Array(n + 1);
  const choiceDist = new Int32Array(n + 1);

  const head = new Int32Array(HASH_SIZE).fill(-1);
  const prev = new Int32Array(n);
  let h = n >= 3 ? ((data[0] << 10) ^ (data[1] << 5) ^ data[2]) & HASH_MASK : 0;

  const distFor = new Int32Array(LEN_BP.length);
  for (let i = 0; i < n; i++) {
    const base = costs[i];
    if (base !== Infinity) {
      // Literal.
      const lc = base + litLen[data[i]];
      if (lc < costs[i + 1]) { costs[i + 1] = lc; choiceLen[i + 1] = 1; choiceDist[i + 1] = 0; }
      // Matches.
      if (i <= n - MIN_MATCH) {
        const maxLen = Math.min(MAX_MATCH, n - i);
        // Walk the chain once, recording for each length breakpoint the
        // nearest distance reaching it (the chain is nearest-first).
        distFor.fill(0);
        let maxM = 0;
        let maxMDist = 0;
        let cand = head[h];
        let tries = 0;
        while (cand >= 0 && i - cand <= WINDOW && tries < maxChain) {
          tries++;
          const dist = i - cand;
          if (maxM === 0 || data[cand + maxM] === data[i + maxM]) {
            const m = matchLength(data, i, cand, maxLen);
            if (m > maxM) {
              // Fill every breakpoint in (maxM, m] with this distance.
              for (let k = 0; k < LEN_BP.length; k++) {
                if (LEN_BP[k] > maxM && LEN_BP[k] <= m) distFor[k] = dist;
              }
              maxM = m;
              maxMDist = dist;
              if (m >= maxLen) break;
            }
          }
          cand = prev[cand];
        }
        if (maxM >= MIN_MATCH) {
          for (let k = 0; k < LEN_BP.length; k++) {
            const L = LEN_BP[k];
            if (L > maxM) break;
            const d = distFor[k];
            if (d === 0) continue;
            const c = base + lenCost[L] + distCost[d];
            const j = i + L;
            if (c < costs[j]) { costs[j] = c; choiceLen[j] = L; choiceDist[j] = d; }
          }
          // The full longest match, even when it is not a breakpoint.
          {
            const c = base + lenCost[maxM] + distCost[maxMDist];
            const j = i + maxM;
            if (c < costs[j]) { costs[j] = c; choiceLen[j] = maxM; choiceDist[j] = maxMDist; }
          }
        }
        // The greedy parse's match at this position, if any.
        const g = greedyTok !== null ? greedyTok[i] : 0;
        if (g !== 0) {
          const gl = (g >>> 16) & 0x1ff;
          const gd = g & 0xffff;
          if (gl >= MIN_MATCH && gl <= maxLen) {
            const c = base + lenCost[gl] + distCost[gd];
            const j = i + gl;
            if (c < costs[j]) { costs[j] = c; choiceLen[j] = gl; choiceDist[j] = gd; }
          }
        }
      }
    }
    // Insert this position for later matches.
    if (i <= n - MIN_MATCH) {
      prev[i] = head[h];
      head[h] = i;
      if (i + 1 <= n - MIN_MATCH) h = ((h << 5) ^ data[i + 3]) & HASH_MASK;
    }
  }

  // Backtrack from the end into tokens.
  const ops = new Int32Array(n + 1);
  let count = 0;
  const rev = new Int32Array(n + 1);
  let rc = 0;
  let j = n;
  while (j > 0) {
    const l = choiceLen[j];
    const d = choiceDist[j];
    if (l === 0 || d === 0) {
      rev[rc++] = data[j - 1];
      j -= 1;
    } else {
      rev[rc++] = MATCH_FLAG | (l << 16) | d;
      j -= l;
    }
  }
  for (let k = rc - 1; k >= 0; k--) ops[count++] = rev[k];
  return { ops, count };
}

// ---- Huffman code lengths (length-limited, by a heap-built tree) ----

/** Depths of a Huffman tree built from freq (unlimited), via a binary heap. */
function huffmanDepths(freq) {
  const n = freq.length;
  const nodeFreq = [];
  const nodeLeft = [];
  const nodeRight = [];
  for (let i = 0; i < n; i++) { nodeFreq.push(freq[i]); nodeLeft.push(-1); nodeRight.push(-1); }
  const heap = [];
  const less = (a, b) => nodeFreq[a] < nodeFreq[b] || (nodeFreq[a] === nodeFreq[b] && a < b);
  const push = (v) => {
    heap.push(v);
    let c = heap.length - 1;
    while (c > 0) {
      const p = (c - 1) >> 1;
      if (!less(heap[c], heap[p])) break;
      [heap[c], heap[p]] = [heap[p], heap[c]];
      c = p;
    }
  };
  const pop = () => {
    const top = heap[0];
    const last = heap.pop();
    if (heap.length > 0) {
      heap[0] = last;
      let p = 0;
      for (;;) {
        const l = p * 2 + 1, r = l + 1;
        let s = p;
        if (l < heap.length && less(heap[l], heap[s])) s = l;
        if (r < heap.length && less(heap[r], heap[s])) s = r;
        if (s === p) break;
        [heap[p], heap[s]] = [heap[s], heap[p]];
        p = s;
      }
    }
    return top;
  };
  for (let i = 0; i < n; i++) if (freq[i] > 0) push(i);
  let next = n;
  while (heap.length > 1) {
    const a = pop(), b = pop();
    nodeFreq.push(nodeFreq[a] + nodeFreq[b]);
    nodeLeft.push(a); nodeRight.push(b);
    push(next++);
  }
  const depths = new Uint8Array(n);
  const root = heap[0];
  const stack = [root, 0];
  while (stack.length > 0) {
    const d = stack.pop(), node = stack.pop();
    if (node < n) { if (freq[node] > 0) depths[node] = d; }
    else { stack.push(nodeLeft[node], d + 1); stack.push(nodeRight[node], d + 1); }
  }
  return depths;
}

/** Code lengths for freq, capped at maxBits (frequencies are halved and the tree rebuilt until it fits). */
function codeLengths(freq, maxBits) {
  const n = freq.length;
  const lengths = new Uint8Array(n);
  let symbols = 0;
  for (let i = 0; i < n; i++) if (freq[i] > 0) symbols++;
  if (symbols === 0) return lengths;
  if (symbols === 1) {
    for (let i = 0; i < n; i++) if (freq[i] > 0) lengths[i] = 1;
    return lengths;
  }
  let f = freq;
  for (let attempt = 0; attempt < 32; attempt++) {
    const depths = huffmanDepths(f);
    let max = 0;
    for (let i = 0; i < n; i++) if (depths[i] > max) max = depths[i];
    if (max <= maxBits) return depths;
    const g = new Int32Array(n);
    for (let i = 0; i < n; i++) g[i] = freq[i] > 0 ? Math.max(1, f[i] >> 1) : 0;
    f = g;
  }
  return huffmanDepths(f);
}

/** Canonical Huffman codes from lengths; returns codes with bits reversed for LSB-first writing. */
function canonicalCodes(lengths) {
  let maxBits = 0;
  for (const l of lengths) if (l > maxBits) maxBits = l;
  const blCount = new Uint16Array(maxBits + 1);
  for (const l of lengths) if (l > 0) blCount[l]++;
  const nextCode = new Uint16Array(maxBits + 1);
  let code = 0;
  for (let b = 1; b <= maxBits; b++) { code = (code + blCount[b - 1]) << 1; nextCode[b] = code; }
  const codes = new Uint16Array(lengths.length);
  for (let i = 0; i < lengths.length; i++) {
    if (lengths[i] === 0) continue;
    const c = nextCode[lengths[i]]++;
    // Reverse the bits of the code so it can be written LSB-first.
    let r = 0;
    for (let k = 0; k < lengths[i]; k++) r = (r << 1) | ((c >> k) & 1);
    codes[i] = r;
  }
  return codes;
}

/** Fixed Huffman code lengths (RFC 1951 section 3.2.6). */
const FIXED_LIT_LEN = (() => {
  const l = new Uint8Array(288);
  for (let i = 0; i < 144; i++) l[i] = 8;
  for (let i = 144; i < 256; i++) l[i] = 9;
  for (let i = 256; i < 280; i++) l[i] = 7;
  for (let i = 280; i < 288; i++) l[i] = 8;
  return l;
})();
const FIXED_DIST_LEN = new Uint8Array(30).fill(5);

// ---- Bit writer ----

class BitWriter {
  constructor(capacity) {
    this.out = new Uint8Array(Math.max(1024, capacity));
    this.pos = 0;
    this.bitbuf = 0;
    this.bitcnt = 0;
  }
  grow() {
    const next = new Uint8Array(this.out.length * 2);
    next.set(this.out.subarray(0, this.pos));
    this.out = next;
  }
  write(bits, len) {
    if (len === 0) return;
    this.bitbuf |= (bits << this.bitcnt) >>> 0;
    this.bitcnt += len;
    while (this.bitcnt >= 8) {
      if (this.pos >= this.out.length) this.grow();
      this.out[this.pos++] = this.bitbuf & 255;
      this.bitbuf >>>= 8;
      this.bitcnt -= 8;
    }
  }
  align() {
    if (this.bitcnt > 0) {
      if (this.pos >= this.out.length) this.grow();
      this.out[this.pos++] = this.bitbuf & 255;
      this.bitbuf = 0;
      this.bitcnt = 0;
    }
  }
  bytes() { return this.out.subarray(0, this.pos); }
}

// ---- Block emission ----

/**
 * Run-length encode the literal/length and distance code lengths into
 * code-length-code operations: [symbol, extraValue, extraBits].
 */
function rleLengths(litLen, litCount, distLen, distCount) {
  const ops = [];
  const total = litCount + distCount;
  const get = (i) => (i < litCount ? litLen[i] : distLen[i - litCount]);
  let i = 0;
  while (i < total) {
    const v = get(i);
    let run = 1;
    while (i + run < total && get(i + run) === v) run++;
    if (v === 0) {
      let left = run;
      while (left >= 11) { const take = Math.min(left, 138); ops.push([18, take - 11, 7]); left -= take; }
      while (left >= 3) { const take = Math.min(left, 10); ops.push([17, take - 3, 3]); left -= take; }
      while (left > 0) { ops.push([0, 0, 0]); left--; }
    } else {
      ops.push([v, 0, 0]);
      let left = run - 1;
      while (left >= 3) { const take = Math.min(left, 6); ops.push([16, take - 3, 2]); left -= take; }
      while (left > 0) { ops.push([v, 0, 0]); left--; }
    }
    i += run;
  }
  return ops;
}

/** Bit cost of emitting ops with the code-length code lengths clLen. */
function rleCost(ops, clLen) {
  let cost = 0;
  for (const [s, , e] of ops) cost += clLen[s] + e;
  return cost;
}

/** Emit one dynamic-Huffman block's tokens (ops[start, end)) plus end-of-block. */
function emitDynamicBlock(bw, ops, start, end, isLast, litLen, litCode, distLen, distCode) {
  bw.write(isLast ? 1 : 0, 1);
  bw.write(2, 2);
  // Trim trailing zero lengths (HLIT >= 257, HDIST >= 1).
  let hlit = 286;
  while (hlit > 257 && litLen[hlit - 1] === 0) hlit--;
  let hdist = 30;
  while (hdist > 1 && distLen[hdist - 1] === 0) hdist--;
  const rle = rleLengths(litLen, hlit, distLen, hdist);
  const clFreq = new Int32Array(19);
  for (const [s] of rle) clFreq[s]++;
  let clLen = codeLengths(clFreq, 7);
  // A code-length code needs at least two symbols; add an unused one if needed.
  let clSymbols = 0;
  for (let i = 0; i < 19; i++) if (clLen[i] > 0) clSymbols++;
  if (clSymbols < 2) clLen[0] = 1;
  let hclen = 19;
  while (hclen > 4 && clLen[CL_ORDER[hclen - 1]] === 0) hclen--;
  bw.write(hlit - 257, 5);
  bw.write(hdist - 1, 5);
  bw.write(hclen - 4, 4);
  for (let k = 0; k < hclen; k++) bw.write(clLen[CL_ORDER[k]], 3);
  const clCode = canonicalCodes(clLen);
  for (const [s, extra, ebits] of rle) {
    bw.write(clCode[s], clLen[s]);
    if (ebits > 0) bw.write(extra, ebits);
  }
  for (let t = start; t < end; t++) {
    const op = ops[t];
    if (op < 256) {
      bw.write(litCode[op], litLen[op]);
    } else {
      const len = (op >>> 16) & 0x1ff;
      const dist = op & 0xffff;
      const s = 257 + LEN_SYM[len];
      bw.write(litCode[s], litLen[s]);
      if (LEN_EXT[len] > 0) bw.write(len - LEN_BASE[LEN_SYM[len]], LEN_EXT[len]);
      const ds = DIST_SYM[dist];
      bw.write(distCode[ds], distLen[ds]);
      if (DIST_EXT[dist] > 0) bw.write(dist - DIST_BASE[ds], DIST_EXT[dist]);
    }
  }
  bw.write(litCode[256], litLen[256]);
}

/** Emit one fixed-Huffman block's tokens. */
function emitFixedBlock(bw, ops, start, end, isLast, litCode, distCode) {
  bw.write(isLast ? 1 : 0, 1);
  bw.write(1, 2);
  for (let t = start; t < end; t++) {
    const op = ops[t];
    if (op < 256) {
      bw.write(litCode[op], FIXED_LIT_LEN[op]);
    } else {
      const len = (op >>> 16) & 0x1ff;
      const dist = op & 0xffff;
      const s = 257 + LEN_SYM[len];
      bw.write(litCode[s], FIXED_LIT_LEN[s]);
      if (LEN_EXT[len] > 0) bw.write(len - LEN_BASE[LEN_SYM[len]], LEN_EXT[len]);
      const ds = DIST_SYM[dist];
      bw.write(distCode[ds], 5);
      if (DIST_EXT[dist] > 0) bw.write(dist - DIST_BASE[ds], DIST_EXT[dist]);
    }
  }
  bw.write(litCode[256], 7);
}

/** Estimate a block's bit size under the given code lengths. */
function blockBitEstimate(ops, start, end, litLen, distLen) {
  let bits = 0;
  for (let t = start; t < end; t++) {
    const op = ops[t];
    if (op < 256) bits += litLen[op];
    else {
      const len = (op >>> 16) & 0x1ff;
      const dist = op & 0xffff;
      bits += litLen[257 + LEN_SYM[len]] + LEN_EXT[len] + distLen[DIST_SYM[dist]] + DIST_EXT[dist];
    }
  }
  bits += litLen[256];
  return bits;
}

/**
 * Compress data to a raw deflate stream: a greedy lazy parse, then one
 * optimal-parsing pass under the greedy parse's Huffman costs, then
 * per-block dynamic Huffman emission (or fixed Huffman when it is smaller).
 */
function deflateRaw(data) {
  const maxChain = 2048;
  const dpChain = 192;
  const blockBytes = 262144;
  const n = data.length;
  if (n === 0) {
    const bw = new BitWriter(8);
    emitFixedBlock(bw, new Int32Array(0), 0, 0, true, canonicalCodes(FIXED_LIT_LEN), canonicalCodes(FIXED_DIST_LEN));
    bw.align();
    return bw.bytes();
  }
  // Pass 1: longest-match greedy tokenization.
  let { ops, count } = tokenize(data, null, null, maxChain);
  // The greedy parse's matches, by start position, for the optimal parser.
  const greedyTok = new Int32Array(n);
  {
    let pos = 0;
    for (let t = 0; t < count; t++) {
      const op = ops[t];
      if (op < 256) pos += 1;
      else {
        const len = (op >>> 16) & 0x1ff;
        const dist = op & 0xffff;
        greedyTok[pos] = (len << 16) | dist;
        pos += len;
      }
    }
  }
  // Huffman costs from the greedy tokenization, then an optimal parse.
  const litFreq = new Int32Array(288);
  const distFreq = new Int32Array(30);
  for (let t = 0; t < count; t++) {
    const op = ops[t];
    if (op < 256) litFreq[op]++;
    else {
      const len = (op >>> 16) & 0x1ff;
      const dist = op & 0xffff;
      litFreq[257 + LEN_SYM[len]]++;
      distFreq[DIST_SYM[dist]]++;
    }
  }
  litFreq[256]++;
  const litLen = codeLengths(litFreq, 15);
  const distLen = codeLengths(distFreq, 15);
  // Unused symbols get no code length; the parser must not treat them as
  // free, so fall back to the fixed-Huffman lengths for their cost.
  const litLenEff = new Uint8Array(288);
  for (let s = 0; s < 288; s++) litLenEff[s] = litLen[s] > 0 ? litLen[s] : FIXED_LIT_LEN[s];
  const distLenEff = new Uint8Array(30);
  for (let s = 0; s < 30; s++) distLenEff[s] = distLen[s] > 0 ? distLen[s] : 5;
  const parsed = optimalParse(data, litLenEff, distLenEff, dpChain, greedyTok);
  ops = parsed.ops;
  count = parsed.count;
  // Split tokens into blocks by raw bytes consumed.
  const bounds = [];
  let consumed = 0, start = 0;
  for (let t = 0; t < count; t++) {
    const op = ops[t];
    consumed += op < 256 ? 1 : (op >>> 16) & 0x1ff;
    if (consumed >= blockBytes && t + 1 < count) {
      bounds.push([start, t + 1]);
      start = t + 1;
      consumed = 0;
    }
  }
  bounds.push([start, count]);
  const bw = new BitWriter(Math.max(1024, n >> 2));
  const fixedLitCode = canonicalCodes(FIXED_LIT_LEN);
  const fixedDistCode = canonicalCodes(FIXED_DIST_LEN);
  for (let b = 0; b < bounds.length; b++) {
    const [s, e] = bounds[b];
    const isLast = b === bounds.length - 1;
    const blockLitFreq = new Int32Array(288);
    const blockDistFreq = new Int32Array(30);
    for (let t = s; t < e; t++) {
      const op = ops[t];
      if (op < 256) blockLitFreq[op]++;
      else {
        const len = (op >>> 16) & 0x1ff;
        const dist = op & 0xffff;
        blockLitFreq[257 + LEN_SYM[len]]++;
        blockDistFreq[DIST_SYM[dist]]++;
      }
    }
    blockLitFreq[256]++;
    let hasDist = false;
    for (let d = 0; d < 30; d++) if (blockDistFreq[d] > 0) { hasDist = true; break; }
    const blockLitLen = codeLengths(blockLitFreq, 15);
    const blockDistLen = hasDist ? codeLengths(blockDistFreq, 15) : (() => { const d = new Uint8Array(30); d[0] = 1; return d; })();
    const litCode = canonicalCodes(blockLitLen);
    const distCode = canonicalCodes(blockDistLen);
    // Choose dynamic vs fixed by estimated size.
    let hlit = 286;
    while (hlit > 257 && blockLitLen[hlit - 1] === 0) hlit--;
    let hdist = 30;
    while (hdist > 1 && blockDistLen[hdist - 1] === 0) hdist--;
    const rle = rleLengths(blockLitLen, hlit, blockDistLen, hdist);
    const clFreq = new Int32Array(19);
    for (const [s] of rle) clFreq[s]++;
    let clLen = codeLengths(clFreq, 7);
    let clSymbols = 0;
    for (let i = 0; i < 19; i++) if (clLen[i] > 0) clSymbols++;
    if (clSymbols < 2) clLen[0] = 1;
    let hclen = 19;
    while (hclen > 4 && clLen[CL_ORDER[hclen - 1]] === 0) hclen--;
    const dynHeaderBits = 14 + hclen * 3 + rleCost(rle, clLen);
    const dynBits = blockBitEstimate(ops, s, e, blockLitLen, blockDistLen) + dynHeaderBits;
    const fixBits = blockBitEstimate(ops, s, e, FIXED_LIT_LEN, FIXED_DIST_LEN);
    if (fixBits + 3 <= dynBits) {
      emitFixedBlock(bw, ops, s, e, isLast, fixedLitCode, fixedDistCode);
    } else {
      emitDynamicBlock(bw, ops, s, e, isLast, blockLitLen, litCode, blockDistLen, distCode);
    }
  }
  bw.align();
  return bw.bytes();
}

/** Compress data to a full zlib stream (header + deflate + Adler-32). */
function deflateZlib(data) {
  const raw = deflateRaw(data);
  const out = new Uint8Array(raw.length + 6);
  out[0] = 0x78; out[1] = 0x9c;
  out.set(raw, 2);
  const adler = adler32(data);
  out[2 + raw.length] = (adler >>> 24) & 255;
  out[3 + raw.length] = (adler >>> 16) & 255;
  out[4 + raw.length] = (adler >>> 8) & 255;
  out[5 + raw.length] = adler & 255;
  return out;
}

// ---------------------------------------------------------------------------
// Per-image encoding
// ---------------------------------------------------------------------------

/** The PNG of an image of `form` whose IDAT holds the zlib stream `idat`. */
function pngOfForm(width, height, form, idat) {
  const chunks = [['IHDR', ihdrOf(width, height, form.colourType)]];
  if (form.plte !== null) chunks.push(['PLTE', form.plte]);
  if (form.trns !== null) chunks.push(['tRNS', form.trns]);
  chunks.push(['IDAT', idat]);
  chunks.push(['IEND', new Uint8Array(0)]);
  return pngOf(chunks);
}

/**
 * The smallest PNG this encoder writes for one RGBA image: every form and
 * filter choice is screened by zlib at level 6, the winner is compressed
 * with the custom deflate encoder, and zlib at levels 6 and 9 is kept as a
 * safety net when it happens to be smaller.
 */
function encodeImage(rgba, width, height) {
  const forms = formsOf(rgba);
  let best = null;
  for (const form of forms) {
    const chunks = chunkBytes(form);
    for (const choice of form.filters) {
      const data = filtered(form.samples, width, height, form.bpp, choice);
      const zlib = deflateSync(data, SCREEN);
      const bytes = zlib.length + chunks;
      if (best === null || bytes < best.bytes) best = { form, data, bytes };
    }
  }
  const { form, data } = best;
  const chunks = chunkBytes(form);
  let idat = deflateZlib(data);
  const z9 = deflateSync(data, { level: 9, memLevel: 9 });
  if (z9.length < idat.length) idat = z9;
  const z9m8 = deflateSync(data, { level: 9, memLevel: 8 });
  if (z9m8.length < idat.length) idat = z9m8;
  const z6 = deflateSync(data, SCREEN);
  if (z6.length < idat.length) idat = z6;
  return pngOfForm(width, height, form, idat);
}

// ---------------------------------------------------------------------------
// Main: answer every instance of the set in one run.
// ---------------------------------------------------------------------------

const I = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const O = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';

for (const id of readdirSync(I).sort()) {
  const image = decodePng(new Uint8Array(readFileSync(join(I, id, 'image.png'))));
  if (!image.ok) throw new Error(`${id}/image.png: ${image.why}`);
  mkdirSync(join(O, id), { recursive: true });
  writeFileSync(join(O, id, 'image.png'), encodeImage(image.rgba, image.width, image.height));
}
