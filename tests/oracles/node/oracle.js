// The npm oracle for tests/run_tests.py: the bech32 package (bitcoinjs)
// at the version package-lock.json pins, driven line by line.
//
//   node oracle.js NODE_MODULES
//
// loads the package from NODE_MODULES, where tests/run_tests.py
// installs it with `npm ci`. Each line of standard input is one
// request, with fields in hex as for `bech32 serve` (`-` for an empty
// field):
//
//   d STRING               bech32.decode, else bech32m.decode
//   e VARIANT HRP VALUES   bech32.encode or bech32m.encode
//
// Each answer is "OK VARIANT HRP VALUES" for a decoding, "OK STRING"
// for an encoding, "FAIL" and the message the package threw, or
// "error" for a line this script cannot read. Both decoders run with
// the package's default limit of 90 characters.
'use strict';
const path = require('path');
const readline = require('readline');
const { bech32, bech32m } = require(path.resolve(process.argv[2], 'bech32'));

function field(f) {
  if (f === '-') return Buffer.alloc(0);
  if (f === '' || f.length % 2 !== 0 || !/^[0-9a-f]*$/.test(f)) return null;
  return Buffer.from(f, 'hex');
}

function toField(bytes) {
  return bytes.length === 0 ? '-' : Buffer.from(bytes).toString('hex');
}

function utf8(bytes) {
  // Strict UTF-8, with a byte order mark at the start kept as the
  // character U+FEFF: TextDecoder drops it unless told not to.
  return new TextDecoder('utf-8', { fatal: true, ignoreBOM: true }).decode(bytes);
}

function fail(e) {
  // The message on one line, escaped, with no spaces.
  return 'FAIL ' + JSON.stringify(String(e && e.message)).replace(/\s+/g, '_');
}

function decode(s) {
  let name = 'bech32';
  let r = bech32.decodeUnsafe(s);
  if (r === undefined) {
    name = 'bech32m';
    try {
      r = bech32m.decode(s);
    } catch (e) {
      return fail(e);
    }
  }
  return `OK ${name} ${toField(Buffer.from(r.prefix, 'utf8'))} ${toField(r.words)}`;
}

function encode(variant, hrp, values) {
  const lib = variant === 'bech32' ? bech32 : variant === 'bech32m' ? bech32m : null;
  if (lib === null) return 'error';
  try {
    return 'OK ' + toField(Buffer.from(lib.encode(hrp, Array.from(values)), 'utf8'));
  } catch (e) {
    return fail(e);
  }
}

function answer(line) {
  const parts = line.split(' ');
  try {
    if (parts.length === 2 && parts[0] === 'd') {
      const s = field(parts[1]);
      return s === null ? 'error' : decode(utf8(s));
    }
    if (parts.length === 4 && parts[0] === 'e') {
      const hrp = field(parts[2]);
      const values = field(parts[3]);
      return hrp === null || values === null ? 'error' : encode(parts[1], utf8(hrp), values);
    }
  } catch (e) {
    return 'error';
  }
  return 'error';
}

const out = [];
const rl = readline.createInterface({ input: process.stdin, crlfDelay: Infinity });
rl.on('line', (line) => {
  out.push(answer(line));
  if (out.length >= 1024) {
    process.stdout.write(out.join('\n') + '\n');
    out.length = 0;
  }
});
rl.on('close', () => {
  if (out.length) process.stdout.write(out.join('\n') + '\n');
});
