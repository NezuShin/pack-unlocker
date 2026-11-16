# Pack Unlocker

Removes the ZIP and PNG "protection" from Minecraft Java Edition resource packs, so they open in WinRAR, 7-Zip, Windows Explorer and image editors again. The repaired pack still works in the game.

Everything runs locally in your browser. The pack is never uploaded, and there are no dependencies or build step.

## Usage

### In the browser

1. Open `index.html` (straight from disk, or host the folder anywhere as static files).
2. Choose or drop a `.zip` resource pack.
3. Click **Remove protection**. The repaired pack downloads as `<name>-unlocked.zip`, along with a report of what was fixed.

The page also explains how each protection layer works and how it is undone.

### In Node.js (18+)

`unlocker.js` works as a CommonJS module:

```js
const fs = require('fs');
const PackUnlocker = require('./unlocker.js');

(async () => {
  const { parts, report } = await PackUnlocker.unlock(fs.readFileSync('pack.zip'));
  fs.writeFileSync('pack-unlocked.zip', Buffer.concat(parts));
  console.log(report.findings);
})();
```

`unlock(bytes, { onProgress })` takes a `Uint8Array` or `ArrayBuffer` and returns `{ parts, size, report }`. `parts` is a list of byte arrays that make up the new ZIP.

## What it fixes

Protection tools rely on the fact that Minecraft reads only part of the ZIP and PNG structures, then fill the parts it ignores with garbage. Pack Unlocker reads the archive the way Minecraft does and writes a clean copy.

**ZIP**
- Fake file names, flags and sizes in local headers
- Wrong or zeroed CRC-32 checksums and fake uncompressed sizes
- Bogus disk numbers (fake split archives)
- Zeroed timestamps
- Junk data in front of the archive, duplicate entries
- File names that can't be extracted on Windows, or that clash

**PNG**
- Chunk CRCs and Adler-32 checksums that were XOR-ed or broken
- Private marker chunks and junk after `IEND`
- Fake zlib window sizes, interleaved `IDAT` chunks, and deflate streams only Minecraft can read

Files that need no repair keep their original bytes. Entries that unpack to more than 512 MB, or can't be decompressed, are skipped and listed as warnings.

## What it doesn't do

It repairs packaging, not content. Hashed file names, minified JSON and stripped shaders are left as they are.

Unlocking a pack doesn't change who owns it. Respect the author's license before reusing or redistributing anything.

## Files

| File          | Purpose                                                      |
| ------------- | ------------------------------------------------------------ |
| `index.html`  | Web page: the tool's interface plus a write-up of each layer |
| `unlocker.js` | The repair engine (browser and Node.js)                      |
