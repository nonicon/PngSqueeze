# PngSqueeze

[![make.fun · png-squeeze-01-run-20261127](https://make.fun/badge/png-squeeze-01-run-20261127.svg)](https://make.fun/bounty/png-squeeze-01-run-20261127?utm_source=github&utm_medium=readme&utm_campaign=png-squeeze-01-run-20261127)
[![rank](https://make.fun/badge/png-squeeze-01-run-20261127/nonicon/PngSqueeze/rank.svg)](https://make.fun/bounty/png-squeeze-01-run-20261127/leaderboard?utm_source=github&utm_medium=readme&utm_campaign=png-squeeze-01-run-20261127)
[![reward](https://make.fun/badge/png-squeeze-01-run-20261127/nonicon/PngSqueeze/reward.svg)](https://make.fun/bounty/png-squeeze-01-run-20261127?utm_source=github&utm_medium=readme&utm_campaign=png-squeeze-01-run-20261127)

A lossless PNG encoder that rewrites screenshots into the smallest PNG it can.
Every pixel's RGBA decodes exactly, including fully transparent pixels' colours.

## How it works

For each 1280x720 RGBA screenshot, PngSqueeze:

1. **Reduces the colour type.** A palette of at most 256 colours (transparent
   entries first, ordered by count or by luminance), grey, grey with alpha,
   RGB, or RGBA — plus a `tRNS` transparency key where a single fully
   transparent value applies. A palette or a narrower type holds the same
   pixels in far fewer bytes than RGBA.
2. **Searches the filters.** Every form is tried with fixed filters, the
   minimum-sum and fewest-pairs heuristics, and a brute-force search that
   weighs each filter by actually compressing the row with zlib. The winner
   is the smallest by a fast zlib screen.
3. **Compresses with a purpose-built deflate encoder.** Lazy hash-chain
   matching, a dynamic-programming optimal parse over the token stream
   (choosing matches by true bit cost under the block's Huffman tables), and
   per-block dynamic Huffman tables. zlib at levels 6 and 9 is kept as a
   safety net when it happens to be smaller.

The program is a single self-contained file, `main.ts`. It uses only Node's
built-in modules, reads nothing from the network, and is fully
deterministic: every choice is a fixed function of the input bytes, so two
runs on the same set write byte-identical outputs.

## Running it

```sh
node main.ts
```

It reads every instance under `/input/<id>/image.png` and writes its answer
as `/output/<id>/image.png`, creating each output directory itself. For local
runs, `MAKEFUN_INPUT_DIR` and `MAKEFUN_OUTPUT_DIR` stand in for `/input` and
`/output`. One run answers a whole set of 8 instances in about 37 seconds on
a single CPU, inside the 60-second wall budget.

## Practice-set results

| Instance | Theme | Bytes | Points |
| -------- | ----- | ----- | ------ |
| i001 | flat | 11,452 | 766 |
| i002 | rich | 48,067 | 750 |
| i003 | alpha | 98,026 | 726 |
| i004 | grey | 99,111 | 735 |
| i005 | flat | 15,454 | 779 |
| i006 | rich | 168,735 | 724 |
| i007 | alpha | 57,367 | 736 |
| i008 | grey | 23,267 | 755 |

Total practice score **746,294** of 1,000,000, all 8 instances answered
exactly. The house baseline (fixed-paeth) scores 420,399 on the same set.

## License

MIT. See [LICENSE](LICENSE).
