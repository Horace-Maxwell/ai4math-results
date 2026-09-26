# Packaging notes: certificates for the paper on integral generalized sun graphs

Staged on 2026-09-26 (UTC), 22:45–23:16, for release v1.6.0 by an AI agent (Claude Code) that finalised the paper and did the release packaging.

- Paper: `papers/sun-graphs/note.tex` and `note.pdf` (12 pages), *The minimum order of a counterexample to a conjecture on integral generalized sun graphs*. It cites this directory as "version 1.6.0 of ai4math-results, directory `certificates/sun-graphs/`".
- There is no Lean code for this paper. Nothing in it is formally verified; the results rest on the written proofs and on the computations below.
- Everything in this folder comes from the project's working folders:
  - `code/`, `logs/`, `review/`, `CONTRACT.md` and `PROOF-working-note.md` (= `PROOF.md`) come from `<project>/work/round6/sun-graphs/`;
  - `checks-addition/` comes from `<project>/outputs/Sun-graphs/checks-addition/`, next to the paper.
- Who wrote what:
  - `code/`: implementations A (`sunsearch*.c`) and B, B2 (`sunB*.c`), and the checking scripts of the agent that did the research;
  - `review/REVIEW.md`, `review/code/`, `review/logs/`: the first referee agent (implementations C and C2, `sunC.c`, `sunC2.c`);
  - `review/REVIEW-paper7.md`, `review/paper7/`: the second referee agent (implementation D, `sunD*.c`);
  - `checks-addition/`: checks re-run while the paper was written and finalised.

## What backs what

| Claim (paper) | Programs | Logs |
|---|---|---|
| Table 1, column A (versions 4, 5, 6) | `code/sunsearch_v4_f5a38c28.c`, `code/sunsearch_v5_bfcca593.c`, `code/sunsearch_v6_39a87195.c` | `logs/A_*` (version 4); `logs/n42/A_*`, `A6_*`, `A6ctrl_*` (versions 5 and 6) |
| Table 1, column B, B2 | `code/sunB_v1_4d92eb48.c`, `code/sunB_v2_8311d32e.c`, `code/sunB.c` (version 3); `code/sunB2_v1_54531ad0.c`, `code/sunB2.c` (version 2) | `logs/B_*`, `logs/B2_b10_N41_p*` (versions 1); `logs/n42/B_*`, `Bctrl_*`, `B2_*`, `B2ctrl_*` |
| Table 1, column C | `review/code/sunC.c`, `review/code/sunC2.c` | `review/logs/C_*`, `review/logs/C2_*` (times in the `.err` files) |
| Table 1, column D | `review/paper7/code/sunD_v1.c`, `sunD2.c`, `sunD3.c`, `sunD3_maxb16.c` | `review/paper7/logs/D1_*`, `D2_*`, `D3_*`, `D_small_controls.log` |
| Table 2 (hashes) | – | `logs/code_hashes.txt`, `logs/n42/code_hashes_n42.txt`, `review/logs/C_code_hash.txt`, `review/logs/C2_code_hash.txt`, `review/paper7/logs/D_code_hashes.txt` |
| SymPy confirmation of the integral graphs found (§5.1) | `code/confirm_exact.py`, `review/code/confirmC.py`, `review/paper7/code/confirm_D.py`, `checks-addition/spectra.py` | `checks-addition/confirmC.log`, `checks-addition/spectra.log`, `review/paper7/logs/confirm_D.log` |
| A v4 and B2 v1 have the same 52,652 leaves at b = 10, N = 41, none integral (§5.3) | `review/code/A4_dump.c`, `B2v1_dump.c` (the audited sources plus one `printf`), `compare_leaves.py`, `sunC_batch.c` | `review/logs/A4dump_*`, `B2v1dump_*`, `compare_leaves_b10_N41.out`, `dump_provenance.txt` |
| Lemmas 2.2, 2.3(a) and 4.4(a) on 2,968 random graphs (§5.3) | `review/code/check_lemmas.py` | `checks-addition/check_lemmas_3000_7.log`, `check_lemmas_count.log` |
| C's polynomials on 400 graphs; A's multiplicities on 3,877 graphs; D's bounds on 3,250 graphs (§5.3) | `review/code/validate_C.py`; `code/validate_leaf.py`; `review/paper7/code/validate_D.py` | `checks-addition/validate_C_400.log`; `checks-addition/validate_leaf_seeds12.log`; `review/paper7/logs/validate_D_250_seed11.log`, `validate_D_3000_seed2026.log` |
| The numbers of §3, §4 and §7: the list of κ_b, 203, σ(t), r_max, the minimal S_2, (96n)^{1/3} + 7, N_{>1}(C_b) | `checks-addition/check_numbers.py`, `checks-addition/spectra.py`, `review/paper7/code/numcheck.py` | `checks-addition/numbers.log`, `checks-addition/spectra.log`, `review/paper7/logs/numcheck.log` |
| The second referee rebuilt A v5, A v6 and B v3 and reproduced five logged runs (§5.3) | the shipped sources | `review/paper7/logs/reproduce_unrefereed/` |
| B2 v2 at b = 6, N = 42 ran to completion (§5.3) | `code/sunB2.c` | `logs/n42/B2ctrl_b6_N42.out`, `checks-addition/B2v2_b6_N42_rerun.log` |
| Veras 2021 and the arXiv version of Braga–Moraes–Santos (§1) | – | `checks-addition/veras_eprint_check.log`, `checks-addition/arxiv_version_check.log` |
| The two errors in earlier versions of A; the superseded logs are kept (§5.3) | `code/sunsearch_v1.c`, `sunsearch_v2.c`, `sunsearch_v3_ub4break.c` | `logs/invalid_v1/`, `logs/superseded_v2/`, `logs/superseded_v3_ub4break/`, `logs/killed_timebox/` |
| Working note only: N_{>1} of C_b with attachments for b = 10, 14; trace identities on 352 graphs; Theorem 2.1 of BMS spot-checked on 3,000 graphs (second report) | `code/b10_lemma.py`, `code/check_moments.py`, `review/paper7/code/bms21_spot.py` | `logs/b10_b14_lemma.out`, `logs/check_moments.out`, `review/paper7/logs/bms21_spot.log` |

The paper names these programs, and all of them are here: `sunsearch.c` (versions 4, 5, 6 as named in Table 2), `sunB.c`, `sunB2.c`, `sunC.c`, `sunC2.c`, `sunD_v1.c`, `sunD2.c`, `sunD3.c` and `sunD3_maxb16.c`. The ten file names of the first report's Table 2 and the four D files are unchanged, so their hashes can be checked (see the smoke tests).

## How to run (from this folder)

Build with `cc -O2`; add `-lm` for A, and link LAPACK for B2 (`-framework Accelerate` on macOS; elsewhere a LAPACK that provides `dsyev_`, e.g. `-llapack`).

```
cc -O2 -o sunsearch_v4 code/sunsearch_v4_f5a38c28.c -lm
./sunsearch_v4 4 41            # stdout = logs/A_b4_N41.out: 5 INTEGRAL lines (3 graphs), nodes=398136, exacttested=85505
cc -O2 -o sunB_v1 code/sunB_v1_4d92eb48.c
./sunB_v1 4 41                 # stdout = logs/B_b4_N41.out
cc -O2 -o sunB2 code/sunB2.c -framework Accelerate
./sunB2 6 42                   # about 3 min; = the first two lines of logs/n42/B2ctrl_b6_N42.out
cc -O2 -o sunC review/code/sunC.c
./sunC 4 41 noprune 1 0 1      # about 1 min; stdout = review/logs/C_b4_N41_noprune_p0of1.out
cc -O2 -o sunD2 review/paper7/code/sunD2.c
./sunD2 4 41 0 1 all           # = the "sunD2 b=4 N=41 ... mode=all" part of review/paper7/logs/D_small_controls.log
cc -O2 -o review/code/sunC_batch review/code/sunC_batch.c
python3 review/code/compare_leaves.py   # = lines 1-5 of review/logs/compare_leaves_b10_N41.out
```

Usage:
- A: `sunsearch b NMAX [part nparts]`; version 6 takes a fifth argument, and `1` switches Lemma 4.2 on (the working note calls it "Lemma N").
- B: `sunB b NMAX` (versions 1 and 2) or `sunB b NMAX [part nparts]` (version 3); B2: `sunB2 b NMAX [part nparts]`.
- C: `sunC b N prune|noprune [allow3=1] [part nparts]`; C2 also accepts `prune2`.
- D: `sunD2 b N part nparts {all|canon} [dry] [l6] [wmax]`; version 1 (`sunD_v1.c`) has only `all|canon [dry]`; version 3 adds `np` (no pruning, also for odd b). The runs used `all` (with `dry` for counts only), `canon wmax` or `all np`; none used `l6`.
- `code/validate_leaf.py` expects the A binary as `./sunsearch` in the current directory; `review/paper7/code/validate_D.py SUND_BINARY NGRAPHS SEED`; `review/code/validate_C.py SUNC_BINARY NGRAPHS`.

## Smoke tests of this package

Run on 2026-09-26 from 22:52 to 23:08 UTC, from this folder after staging. Tools: Apple clang 21.0.0 (`cc -O2 -Wall`), Python 3.12.4 with SymPy 1.13.1 and NumPy 1.26.4, macOS 26.6 on arm64. The binaries were built outside the package, Python was run with `-B`, at most three runs were at the same time, and each used one core.

1. **Required test: A version 4 at b = 4, N = 41.** `code/sunsearch_v4_f5a38c28.c` compiles with one warning (`variable 'P' set but not used`). The run takes 1.2 s. Its stdout is identical to `logs/A_b4_N41.out`: the three graphs of Theorem 2 as 5 `INTEGRAL` lines, and `DONE b=4 NMAX=41 part=0/1 nodes=398136 pruned=72800 leaves=250424 momentfail=164919 exacttested=85505 integral=5 overflow_skips=0`.
2. **B2 version 2 at b = 6, N = 42** (review of paper 7, N9). 22:52:46–22:55:55 UTC, 189 s. The `CANDIDATE` line and `B2-DONE b=6 NMAX=42 part=0/1 spectra=21 moment_ok=1128560 canonical=449500 tested=449500 candidates=1 lapack_pruned=3266845` are identical to the first two lines of `logs/n42/B2ctrl_b6_N42.out`. The output is kept as `checks-addition/B2v2_b6_N42_rerun.log`.
3. **B version 1 at b = 4, N = 41.** 4.1 s; stdout identical to `logs/B_b4_N41.out` (3 candidates; moment_ok 410,544, canonical 52,641).
4. **C at b = 4, N = 41, no pruning.** 54.4 s; stdout identical to `review/logs/C_b4_N41_noprune_p0of1.out` (5 candidates, 5,683,267 leaves).
5. **D version 2 at b = 4, N = 41, all sequences.** 2.0 s; stdout identical to the corresponding part of `review/paper7/logs/D_small_controls.log` (12 candidate sequences; 410,544 tested).
6. **The relativised `review/code/compare_leaves.py`**, run from a copy of `review/code/` and `review/logs/` with `sunC_batch` built there. Its five lines are identical to lines 1–5 of `review/logs/compare_leaves_b10_N41.out`: A = B2 as sets, 52,652 leaves, 0 integral.
7. **Table 2 hashes.** For all 14 rows of Table 2 of the paper, the 16-digit prefix equals the start of `shasum -a 256` of the shipped file: 10 files in `code/` and `review/code/`, 4 in `review/paper7/code/`. Each full hash also appears in one of the hash files listed above.
8. **No machine paths.** A recursive `grep` for the home-directory prefix, the temporary-directory prefix and the user name finds nothing in this folder or in `papers/sun-graphs/`; neither does `strings` on `note.pdf`. The PDF metadata has the title and author set. The only e-mail address is the author's, in the paper.
9. **Compile check.** All 24 C sources in this folder compile with `cc -O2 -Wall` (B2 and the B2 dumps with `-framework Accelerate`, `code/trace.c` with `-Icode`). The only warning, in every version of A and in the A dumps, is `variable 'P' set but not used`. Apart from the programs of items 1–6, none was run.

The paper was compiled with pdflatex three times in a scratch directory: exit 0 each time, no warnings, no overfull or underfull boxes, no undefined references, 12 pages, all fonts embedded.

## Changes made during packaging

1. Five programs of the first referee had the absolute path of the `review/` folder written in them:
   - `review/code/compare_leaves.py`: `R = '<absolute path>'` became `R = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..')`, and `os` was added to the imports. SHA-256 525ea971… before, e3c936aa… after.
   - `review/code/runjob.sh`, `runjob3.sh`, `sched.sh`, `waitlaunch.sh` (zsh): `R=<absolute path>` became `R=${0:A:h:h}`, the parent of the script's folder. SHA-256 before → after: 6819d17d… → d299efb5…, c7d950ff… → 36046f95…, 8eeb6871… → e336881e…, 0ea779af… → 7a16d2a8….
   - No hash of these five files is recorded anywhere, and none of them appears in Table 2.
2. Three logs had absolute prefixes replaced by `<project>` (the project root). A script checked that the substitution reverses exactly and that the digit runs and 64-hex hashes outside the prefix are unchanged:
   - `review/logs/queue3.log`: 2 lines (880b09b0… → 7300c4a2…);
   - `review/logs/queue5.log`: 4 lines (ca0a78d0… → ce5ffaad…);
   - `review/logs/dump_provenance.txt`: 2 lines (4e6fa1fe… → d030cf46…).
3. `PROOF.md` was renamed to `PROOF-working-note.md`.
4. Two corrections were made in the project folder before copying, so the copies here equal their sources (review of paper 7, N9):
   - `logs/n42/INDEX.txt`: the line for `B2ctrl_b6_N42` said "stopped after the hit"; it now says the run completed, and a dated correction note was appended (SHA-256 bfe94695… → ef8ed182…);
   - `PROOF-working-note.md`, line 276: the same correction, marked "Correction at 23:05 UTC" (SHA-256 of `PROOF.md` 00f27f61… → c2861daf…).
   - The log `logs/n42/B2ctrl_b6_N42.out` itself was not changed.
5. Two logs were added to `checks-addition/` while the paper was finalised: `B2v2_b6_N42_rerun.log` (item 2 of the smoke tests) and `veras_eprint_check.log` (S1 of the second report).

All other files are byte-identical copies with their timestamps preserved: `cmp` against the sources found 370 identical files, and the 8 files of items 1 and 2 differ only as described.

## Not included, and why

- `g1/` (22 MB) and the JSON/XML files in `review/lit/`: raw responses of the literature searches.
- `querylog.tsv` and `review/querylog.tsv`: the literature query logs (earlier packages do not ship theirs either), and the two copies of `qlog.sh`, the helper that wrote them, which contain machine paths.
- Copies of other people's work: the papers and text extractions in `review/lit/` (`brt2017.pdf`, `cw2509.pdf`, `sr3.pdf`, `vdh.pdf`, `wang_thesis.pdf`, their `.txt` files and the rendered page `brt_p297-25.png`), and `review/src/`, the arXiv source of Braga–Moraes–Santos. The e-print and the Veras abstract downloaded during packaging stay outside the repository; `checks-addition/veras_eprint_check.log` records their SHA-256.
- Compiled binaries: `code/sunsearch`, `code/sunsearch_v6`, `code/sunB`, `code/sunB2`, `code/trace`, and `review/code/A4_dump`, `A_dump`, `A_orig_O2`, `B2_dump`, `B2v1_dump`, `sunC`, `sunC2`, `sunC_batch`. Only their sources are shipped.
- `review/code/__pycache__/`.
- Size: no file here is near 50 MB. The largest are the leaf dumps `review/logs/A4dump_b10_N41_p0of2.out` and `review/logs/superseded_modified_versions/Adump_b10_N41_p0of2.out`, 1,394,108 bytes each.

## Notes for readers

- `PROOF-working-note.md` is the working note of the agent that did the research, kept as it was apart from the correction above. Where it differs from the paper, the paper is authoritative. Its numbering differs: its Theorems 1′ and 1 are Theorem 1 and (part of) Theorem 2 of the paper, its Theorem 2 is Proposition 3, its cycle filter L6′ is Lemma 4.1, its Lemma N is Lemma 4.2 and the corollary of Lemma N is Corollary 4.3. It calls A, B and B2 "independent"; they were written separately by the same agent (paper, §5.1).
- `code/sunsearch.c` is the working copy of A and equals `sunsearch_v6_39a87195.c`. `code/trace.c`, a debugging tool, includes it. In `logs/code_hashes.txt`, written earlier, the names `code/sunsearch.c`, `code/sunB.c` and `code/sunB2.c` stand for the files now called `sunsearch_v4_f5a38c28.c`, `sunB_v1_4d92eb48.c` and `sunB2_v1_54531ad0.c` (same hashes).
- The header comments of `code/sunB.c` (version 3) and of both versions of B2 say "lexicographically least" image, but these versions take the greatest image; the code comments next to `canonical()` say so. The comments were not changed, to keep the hashes (paper, §5.1).
- `logs/n42/B2ctrl_b6_N42.out` ends with a note "STOPPED by agent at 20:08:29Z". The run had in fact completed: the line before it is the `B2-DONE` line, which `sunB2.c` prints only after the search has finished, and smoke test 2 reproduced both result lines. The note was appended afterwards; see `logs/n42/INDEX.txt`. The other runs marked "STOPPED" have no `DONE` line and are not used.
- `review/logs/compare_leaves_b10_N41.out`: lines 1–5 are the output of `compare_leaves.py`. Lines 6–7, the split into leaves with and without a P2, come from a further step described in §3.5 of `review/REVIEW.md` and not kept as a script. `compare_leaves.py` needs `review/code/sunC_batch` to be built first.
- The D logs whose names start with `D3_` print the label `sunD2`: version 3 is version 2 plus the `np` option and a guard against the bare cycle, and its output label was not changed. `review/paper7/logs/D_code_hashes.txt` also lists `sunD2_frozen.c`, a copy of `sunD2.c` with the same hash, not shipped separately. According to the second report, `sunD3_maxb16.c` (arrays for b ≤ 16) was the build used for the b = 3 runs and `sunD3.c` for the others; the two files differ only in the constant `MAXB`.
- `review/logs/queue3.log` and `queue5.log` show zsh parse errors in `runjob3.sh`, which was edited while queued jobs were reading it. `review/REVIEW.md` §3.6 lists the runs that were used.
- `review/logs/superseded_modified_versions/` holds dumps from modified versions that the first referee replaced (see its `README.txt` and MINOR-7 of `review/REVIEW.md`).
- The two reports mention files that are not shipped: `review/lit/…`, `review/src/`, `g1/oa_doi.json`, the query logs, and the second referee's scratch directory.

## File list

This list gives the size in bytes and the SHA-256 of each file. It covers every file in this folder except this one; the two paper files follow.

In this folder (`certificates/sun-graphs/`):

```
    bytes  sha256                                                            path
     3817  60212ee772cd7bdb47636265485ccf949ea5cfe30714aff33aece0ad58a81e27  CONTRACT.md
    27903  c2861daf1819aa622634b95aaca38e29667889c5d7fedef19ed42c8b243b9a64  PROOF-working-note.md
     1145  edad268f7ae681b064d177411d10bbc48ee4e0044693a5f3030d7534be84e6a1  checks-addition/B2v2_b6_N42_rerun.log
      287  d47412a90e0ade158b3d1a8f97ff78e2f47cfd3820ebe3d53460e8958dc88e0a  checks-addition/arxiv_version_check.log
      186  a556b451068d338d7f790ecb4e8ee6996fc66e6a92c6826a020ae61e2369ef5f  checks-addition/check_lemmas_3000_7.log
      266  300ce0a41c5b2fdf99cb929301e71fbd23654dbdd35a67b6dc5e3a7e783b0b11  checks-addition/check_lemmas_count.log
     1775  3efd63cdbcc6ff434bd77aaad34ab89e716cb45756ae8dffa7483f89356706b4  checks-addition/check_numbers.py
      575  2eb35df48d0fd3be8a28fe556a437950ab1b3d0134c86b12e839f70ac5ba9e7c  checks-addition/confirmC.log
     1585  46fcf62d43167a669c66c6671771c7f82ed81ebc08aeb87a064c1a4a91df2320  checks-addition/numbers.log
      869  4cd9e46f5cd0b1542c2216c504ad6caa093021957e1feca237bb1958ca4cd9d8  checks-addition/spectra.log
     1547  a8ba270790525784a8df7af66657272f03508395b76bdb8c81c72892f52d57c2  checks-addition/spectra.py
      174  bc157ae0e95797ba6024457aebb5bc80870f9c9b5403a2f66fd235f61c53313d  checks-addition/validate_C_400.log
      407  207b565c1e69e6739bdf21d839f32094296de5bc0c48475f1fb272db03fddc6f  checks-addition/validate_leaf_seeds12.log
     3271  eec1843f0530444096c95630d2d079e863dd275b3e6439a8ec28d9e050548b62  checks-addition/veras_eprint_check.log
     1520  c63f5ee4417cac0d18826c2480eb2de6812bcc11017967f91e7706bbcf505849  code/b10_lemma.py
     1153  107e792e4c1d382821e746355afee7979103331cffd43a7fa7d0e93eb007b15c  code/check_moments.py
      726  153faf0c54efe5557c17a07ff98ec55be5dc5238d008ece08552ea9d89fb6921  code/confirm_exact.py
    10932  f0eb3d9ca506a3f7cef0e494ea89f6a25bc27d0ac3e73193ec913e3fad4b8d7c  code/sunB.c
    11857  c80538f9d4359954bae36101d0678e8957cece6c21fa8580c961f43fd76d4855  code/sunB2.c
    11245  54531ad075d1015fbec450c285f5a42a90a9f6589e45e3b78e8a86527dfa4e87  code/sunB2_v1_54531ad0.c
     8369  4d92eb484cefea14e675e12afd2fa62877ef7a6609d13aa3b42c7a540c978694  code/sunB_v1_4d92eb48.c
     9367  8311d32e74f0cfbde05d8ec82f81cd0a3139c4ec95ac946f526f6149873d0e4b  code/sunB_v2_8311d32e.c
    21608  39a871959d2b3d9250a60e847b93d144f3b7a28d644d9a17f3bc6ed33f3580bf  code/sunsearch.c
    16274  6cdfe7b4b036d6ee0588cc984c4a3d8c4545122b89ad98a514661f22f6f7f3c4  code/sunsearch_v1.c
    18787  a5567a06943f16b9ed8a19442c2056b3fbbc202f1f039c3350bc7b944d698219  code/sunsearch_v2.c
    19364  71f4983649e9fc424374d379b07412419208b7d0c86bdc2ed4006aad14428188  code/sunsearch_v3_ub4break.c
    19764  f5a38c28cf3958862a5a30ebfeb4d166d23225e5801412a722697cb25421eb67  code/sunsearch_v4_f5a38c28.c
    20845  bfcca593dc3ea0b2811e7a2c496a9d271875caf074cb61d595f6307ab01c5862  code/sunsearch_v5_bfcca593.c
    21608  39a871959d2b3d9250a60e847b93d144f3b7a28d644d9a17f3bc6ed33f3580bf  code/sunsearch_v6_39a87195.c
     1230  80fccecf93bfa95e785982890ef05295a45b8628c3b1dac2fde48a9b23e63a88  code/trace.c
     1727  4ea4bbd840d13fcde3869d22f22798d7267a5fc097d3c5604ea893aeda8f54f3  code/validate_leaf.py
       44  788c7dd57cd8c13e68fc8eb2dbc1fd8e880fb422d999a9268c73b3fbb7e2a143  logs/A_b10_N41_p0.err
      138  a91e713fb4b26e49b652bbae04b1043a940aa82cacce584b7120caeec9c23d66  logs/A_b10_N41_p0.out
       44  788c7dd57cd8c13e68fc8eb2dbc1fd8e880fb422d999a9268c73b3fbb7e2a143  logs/A_b10_N41_p1.err
      138  f2803b5d50bf96eeecaa6c07b54ca82a2194c4f625c02228e9ff210c13243fd3  logs/A_b10_N41_p1.out
       44  03a7d953d8e96dba5415e93405437899886547234bc037f939f64508be75ea5c  logs/A_b12_N41.err
      134  e93eef9524cab7d6a400a04a4d558f56199d55217dde3f230064c7cbb2d192d5  logs/A_b12_N41.out
       42  805219f5da612a3189e1bcdbcc46cbb17c90e3467e57a6396d1dc8623418b8f6  logs/A_b3_N41.err
      121  cb12ee03be923eaeda284902b306f91e7ead01307c9d53e2290c4bcd9511c204  logs/A_b3_N41.out
       42  eba792bd4dd1a399b708193b1976293dfafe69e00f55c6ba4e11efd36cbd7f39  logs/A_b3_N42.err
      121  60d09d85e1b371882002ff1b52357e20317bf7b0283326f0da60e38d02c3ef60  logs/A_b3_N42.out
       43  2e6cae1f1d4764fa9cb7379c91677fb7ac923cffb6699df4fc5dc275b70e5946  logs/A_b3_N49.err
      123  04fed195744e2e7cc9bd5c5cbd272d7f8e9cc2263cb560b6805f772e5edf7c45  logs/A_b3_N49.out
       43  516abe56ddd84821bdd9e27e2f616b00da9c368626c7e1c3e41742c2f982add7  logs/A_b4_N36.err
      529  9bf9a7978714495d8a761a6c3a4f3342cb6ca1d454bc2d4e5f99dd55c00c1fd8  logs/A_b4_N36.out
       43  2f7f60f3883b93a8f7a23b205dc8bdf29216e8c0c3802da204d0ebe0f0464f88  logs/A_b4_N41.err
      531  0b9f0d4af658a1e10f1694d78c1d753510e453acf590c724ff554d01355f0eaf  logs/A_b4_N41.out
       42  da17aed7abae1d808849bc5d98960dde8d88e8f74791bee7b888e983dc07945b  logs/A_b5_N41.err
      107  638f623bd791fd7aeb4cf42138f11ad447d6f5bd0845c68233716bfa375b1c1a  logs/A_b5_N41.out
       42  ce783af066408ac80f69f5d354886df4c41fd8b6f53600de2776bd3e0f4005aa  logs/A_b5_N42.err
      107  350846b6774874715cdc50e654d1c1c406852c9deb436c3fce6d9359c7e4b921  logs/A_b5_N42.out
       43  1a5d67daa98efc287bbb81bfc6fac83c3178f151771790d4ecbb45d4393beb97  logs/A_b6_N42.err
      237  f5a5ca2c902f9ff9ae2481f890a16514906ec3021af9c02d256c3b768f94be64  logs/A_b6_N42.out
       42  9cff23f94c1965be922d6c24096053f9b64ae84dece92de3e0d4d79482189c24  logs/A_b7_N41.err
      107  b50df665926548cb8d286e9df1afa8b6f485e26745ba5f072d2d72d84fada9a3  logs/A_b7_N41.out
       42  c2a2ffc1259b58f568bd795e2f3e8af9a9eaaf90568a9a435753d69bb940fca3  logs/A_b7_N42.err
      107  807d8b6870c8e940c11995aedb2da21c9056e8040f76d66f95e2bb9ec2226e0b  logs/A_b7_N42.out
       43  2a1405d32b15937bb05c9750a8e4be3f9f97e5d28c09c3489e658ef7b4d00e3f  logs/A_b8_N41.err
      140  6ff920c6d6c3a92d6a96a521b39153a8be7e00beab74726d89589937c6cd16c5  logs/A_b8_N41.out
       42  13b4025b506abe634eb54c84ae2115cacdc293632fe1445629608db4125da0d5  logs/A_b9_N41.err
      107  b12e25e325a0ecec60120602d50426b273cfbaf6b1202a14b42196c54b54a989  logs/A_b9_N41.out
       42  4f7c3d8b3988a3245aecc8379caa52e5ba5e39b8b196b5e2b478f01d3b52170b  logs/A_b9_N42.err
      107  800b31495886adcf62a323a805a35f7fd0541e13617f14355fd33b15d745fd51  logs/A_b9_N42.out
       37  03c3b9568ac505463e63e4a1c5fd9a9077f451349e6bbe9b6e3bccc52e77b5e8  logs/B2_b10_N41_p0.err
      120  51d61985c6986ed20f02b01e5c335269dca4566c0ff34a0017bee54fa52ceb93  logs/B2_b10_N41_p0.out
       37  03c3b9568ac505463e63e4a1c5fd9a9077f451349e6bbe9b6e3bccc52e77b5e8  logs/B2_b10_N41_p1.err
      120  106c81a6e579be06ec28570b4c4986bd9a1ee2df7cfbb9019bffb88b38c472d4  logs/B2_b10_N41_p1.out
       37  03c3b9568ac505463e63e4a1c5fd9a9077f451349e6bbe9b6e3bccc52e77b5e8  logs/B2_b10_N41_p2.err
      120  f62bfaccbe6500985296cf7637e69fd7c3dbb637703817c8f26b90f1762b3c7f  logs/B2_b10_N41_p2.out
       37  03c3b9568ac505463e63e4a1c5fd9a9077f451349e6bbe9b6e3bccc52e77b5e8  logs/B2_b10_N41_p3.err
      119  21ebbebff8fbb87e255bb0a4947a3a9b368b8b140535e31ca8e07fb6e7ee732b  logs/B2_b10_N41_p3.out
       33  08757660cd00a3da2aab8ff33cbf930c1ce4ae0bd10e47e30a91d9b13e4da68c  logs/B_b11_N41.err
       76  b955fc40828b54aa39c67a9e39e50c2bfee81c7309884a8c4cabfc081bb7bde6  logs/B_b11_N41.out
       33  4a6f9b2d109479df9d133392c3f45103a12705f4f788c0256110fe786465fbb0  logs/B_b11_N42.err
       76  bf93ac8a238d028ef9135d0f582789da01159e3bb5043f76b8398230af0f4caf  logs/B_b11_N42.out
       33  dfddb13c98a761de3e4ea483b217e3e0e9c549b3c650427016d6778047662d16  logs/B_b13_N41.err
       76  74f3c374dd96e069f187f714e264c35c2e15b4b8d2c95baba0cfa9069c4b7811  logs/B_b13_N41.out
       33  a930eec518010e30fcb6fe86746a3b8636743c7437e1debe912853952b05153b  logs/B_b13_N42.err
       76  9c3c180fb7d492d00860c2cf97d38f711c0b7fdf2db82fa600a0afabbb8fced0  logs/B_b13_N42.out
       33  b01f29b86e73ebd652af19616cb42c4e339e2a5981372d4410f6969e2308da06  logs/B_b15_N41.err
       76  aa9d289e64746e892aff43c0e8451d1c45a93c41ed27447c6b9875e9383aed94  logs/B_b15_N41.out
       33  8be17fc77cf6cab9485417cef3b1f62abb857dcc896bf8248e5cd29b693e38f6  logs/B_b15_N42.err
       76  6347e803cd80c9489bd165906715b7cc333d1c64f944e47df8140e41e70763f9  logs/B_b15_N42.out
       35  f43d8969e24ed487ec09d0f9e218cbe3105a55edecb2eae229cbe224fed402e5  logs/B_b3_N41.err
       85  4ee031839dea54dea9cd1418bee658ac03101d3c2a98c94ff821bb6ff0fb2cda  logs/B_b3_N41.out
       35  2219ac5a302eeaeebab2e8489b3d4565050e84f48647a70815e6f316ef03e792  logs/B_b3_N42.err
       85  18f1baca9158ebd8b6b9c49dc5addebc8a413f241997b570241ee37d657e0ac6  logs/B_b3_N42.out
       36  838e6ba1e383b0393c6431dedd20825f38f76a375b7f1ccece78c4083b686844  logs/B_b4_N36.err
      223  24d714d0e64e23fee35edeb9ca30da9757032984900ab87ad58f285f2f6032de  logs/B_b4_N36.out
       36  2d7c603c934592c4548045f121fc1355fa21f16425105ffbea13a529f72f6180  logs/B_b4_N41.err
      224  5908944f352cb50db895da392f29ce1298ea0f8ceb19d751d1754ad1ac6d9f5d  logs/B_b4_N41.out
       32  aaf86c9f4dc80d337a358c548b64223de9e947093c48f40f2267a98da7ffe824  logs/B_b5_N41.err
       75  dba99ed854b71a303db1ade91d1d95fae3c0c4077e1090d5a47f2155e1b9a826  logs/B_b5_N41.out
       32  3c7f3e77908b1fd78f719cb204c7fd4d9c94bfad6bde32ae6debcef8fe808475  logs/B_b5_N42.err
       75  e4bfaef08b5343d36ef80857670d3a7618ba1e9e52f554f16af3bf2f4435aea7  logs/B_b5_N42.out
       36  166c9af0a456515c9d6b971e801f8e3ff5e11a19b5148a40f25ca60c866a407b  logs/B_b6_N42.err
      153  18f1ef387054e3be370a5092bd45d8840793e959a926bc6fafdda3757db4da1f  logs/B_b6_N42.out
       32  06b7c208ab55618c0350c5af09052e069ac7d5b0175ccc3bd46aa70d8714efa3  logs/B_b7_N41.err
       75  5f75eb6fdf55021a7b99394b4ddcd8b92b810aba237f992405a384027f5f124f  logs/B_b7_N41.out
       32  bb70d584ff42edbca5a2cde487c92ec0b762b0fb70cf65eec45a24c6bd810c6c  logs/B_b7_N42.err
       75  12d6981deaeb8c410b1cca0cb6d691d3c95dd62135c2a6cb87958d80740b8a50  logs/B_b7_N42.out
       32  6d7aa66035ea39839c479a6349aa178e38cdc454df4db66fcd2c86c510185db1  logs/B_b9_N41.err
       75  b5ce670013bc908515c3bb7e59cbcf7330197fe544aeeb3dcd656b5cbdf8cbbf  logs/B_b9_N41.out
       32  2e14b07a93bd028b5876dcedc40fa49ace0f91b594e5a18717d048908544104e  logs/B_b9_N42.err
       75  77d62c5286bf0a34566821b2c5b0295b38bb0c7146e69ebb6256cb85082e0549  logs/B_b9_N42.out
     2242  cdcfd653eb71fd1bdb7d71704abf7f435998f2fa09ba376292422776811c840e  logs/b10_b14_lemma.out
       31  15c9af5d1466fa05eda516cc3fa521974329f6758dd701b5a35ac0172aef95d0  logs/check_moments.out
      240  54bcb938ad8060be9f24201d26c5f8fa2f1328b623af9805487da10abc9ae158  logs/code_hashes.txt
       44  788c7dd57cd8c13e68fc8eb2dbc1fd8e880fb422d999a9268c73b3fbb7e2a143  logs/invalid_v1/A_b10_N41.err
        0  e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855  logs/invalid_v1/A_b10_N41.out
      165  e6d85b0d637edae6676075e444ca69bd38b8e3187424f79ba2f6c953b174c74f  logs/invalid_v1/A_b3_N41.err
       94  f95e3b7a841b229afd51b8d4c8ce9a3cdba67da374dc13a497e772796c64a8cf  logs/invalid_v1/A_b3_N41.out
       43  1a5d67daa98efc287bbb81bfc6fac83c3178f151771790d4ecbb45d4393beb97  logs/invalid_v1/A_b6_N42_p0.err
      139  a8987cfb193cd5e6119acf5fe1e860e4a22b799597f8fd71fc6621cfb6347450  logs/invalid_v1/A_b6_N42_p0.out
       43  1a5d67daa98efc287bbb81bfc6fac83c3178f151771790d4ecbb45d4393beb97  logs/invalid_v1/A_b6_N42_p1.err
      140  e56facba634a4b28a45c2495afaacbef649bd55935f676201d29d58d3167bdb6  logs/invalid_v1/A_b6_N42_p1.out
       43  1a5d67daa98efc287bbb81bfc6fac83c3178f151771790d4ecbb45d4393beb97  logs/invalid_v1/A_b6_N42_p2.err
      140  f13b60296153dcbb1f9e58fdf98d18fcd04981c3b1750238ff77d5f159839e03  logs/invalid_v1/A_b6_N42_p2.out
       44  9b4cd584e936167f99a3eafb0dfc6549ecf6f38dbdbf66832c253ef13bee1e69  logs/killed_timebox/A_b10_N42_p0.err
        0  e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855  logs/killed_timebox/A_b10_N42_p0.out
       44  9b4cd584e936167f99a3eafb0dfc6549ecf6f38dbdbf66832c253ef13bee1e69  logs/killed_timebox/A_b10_N42_p1.err
        0  e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855  logs/killed_timebox/A_b10_N42_p1.out
       44  7205604b0f1e05a8a20956de1423f1b0c065a2ab69b6524428c6200f4d358bac  logs/killed_timebox/A_b14_N42.err
        0  e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855  logs/killed_timebox/A_b14_N42.out
       94  eacd4b396c92dd9a9771e49c385122e79ce97919ace3c4b082374d19fd72be44  logs/n42/A6_b10_N42.err
      138  6edb4786e8c2b3737c3e2c1ea240ef7fd77bf5132bbf9093a3a17cde24061bb3  logs/n42/A6_b10_N42.out
       93  445cbec57243aabf0f14cac5efee6c5c6d84c0a08d3caa8d9318a4c99334655c  logs/n42/A6_b22_N42.err
      108  d592c0f027b3dab7c17702e6234bfbb147beac6c630142539d8218ecf9976281  logs/n42/A6_b22_N42.out
       93  2277c7d70cfc0d9337dec83c3ddf27c22d3d78821ac2cea0fee52394542e3e18  logs/n42/A6_b26_N42.err
      108  3c042a4314fc5f57ca7465560fac2cfef926b5798a5f104fc8573d085594e37a  logs/n42/A6_b26_N42.out
       77  40e3e56f38dd82d01c40c01eb657c60493be54808cdbfd4d45931377bd247aa5  logs/n42/A6ctrl_b4_N49_lemN0.err
      706  514a2407c1dc51df264b1b6bd51e5bdbd2136b51adaeae7401cc23c8fc84f3c1  logs/n42/A6ctrl_b4_N49_lemN0.out
       92  9ef6a28fa2ea04b8869a8da3c65d0403a5abbda3828885bad4b75601eb1d6ba7  logs/n42/A6ctrl_b4_N49_lemN1.err
      704  f50f63a705204b67d588e3384b5408736cc01d377da089976fc14b9f4c877a4e  logs/n42/A6ctrl_b4_N49_lemN1.out
       92  c06adb1a6c186768a2cfa9f434425c14838d1c770e1dbdf3a603305ca362d110  logs/n42/A6ctrl_b6_N42.err
      233  7440a4f7dc2d8cf983ce1f424782d3382811ed8fe2b81de5bad9c09065754d76  logs/n42/A6ctrl_b6_N42.out
       79  f4acf454f90e77fce366469dea25c644cd4e40246bb5efe9b695545eec0bb191  logs/n42/A_b10_N42_p0.err
      143  09d75936aa29084d5e1f58a3fa8c95c662c524955cf32b52aeeb991f889eff5c  logs/n42/A_b10_N42_p0.out
       79  f4acf454f90e77fce366469dea25c644cd4e40246bb5efe9b695545eec0bb191  logs/n42/A_b10_N42_p1.err
      143  203a8bb4e4fcf42c9b07cb5580cc9ef0efc8e370e914aa80aab1ff242154c451  logs/n42/A_b10_N42_p1.out
       78  2fa769f5d1532ab0c555fcff6d7eade5816f31912488799eb6ee435b66de4621  logs/n42/A_b14_N42.err
      126  7f6277de35bf9817d5f8ca74091bfbc720488236e9d82e3a01f4e6ab4df57c5f  logs/n42/A_b14_N42.out
       78  86151c64556e80b9805f5119bdbebd4dc3a9cebbdbb4c1b4eeb75fc65b60a3aa  logs/n42/A_b18_N42.err
      109  8c5af4493b3f3bb62f2276d5514221106f23f8288670044dd258fcca572f7367  logs/n42/A_b18_N42.out
       36  bbec510971bd16794a7ff420f9bc46095457a2f0888fe337398de212952d6315  logs/n42/B2_b10_N42_p0.err
      116  d8a3a4a6dbf5f551a68d2590edd5b5963e835959e4b99e6d134bf96295e4fa7d  logs/n42/B2_b10_N42_p0.out
       36  bbec510971bd16794a7ff420f9bc46095457a2f0888fe337398de212952d6315  logs/n42/B2_b10_N42_p1.err
      116  d8a3a4a6dbf5f551a68d2590edd5b5963e835959e4b99e6d134bf96295e4fa7d  logs/n42/B2_b10_N42_p1.out
       35  f50a7d21c08d97e4a08b2f3cb681e611769481dfcc9f9de42570f061b2f14ffe  logs/n42/B2_b14_N42.err
       88  a96b305202842bd97d7a473c3edd7cd4517ba710512acf0ba3cf2ff8a21c4ccf  logs/n42/B2_b14_N42.out
       35  d56e6c96210503e9ca0b5f1323cedc84491dccaa2d6dd1eb8037bc314d95cded  logs/n42/B2_b18_N42.err
      102  3c4b92cc158d2a64ae9b2aed34efba70cd5f4695e992cacc43bd505bea5fa6b1  logs/n42/B2_b18_N42.out
       36  166c9af0a456515c9d6b971e801f8e3ff5e11a19b5148a40f25ca60c866a407b  logs/n42/B2ctrl_b6_N42.err
      260  780393363c8c7205cdb305ac5ecca6d6e800300f67159507710c1b4c8560b93e  logs/n42/B2ctrl_b6_N42.out
       36  bbec510971bd16794a7ff420f9bc46095457a2f0888fe337398de212952d6315  logs/n42/B_b10_N42.err
      101  52771ba4398d2bead7c6c7d889716d64c459821f414f0a96a3fea92d8f11c341  logs/n42/B_b10_N42.out
       33  4a6f9b2d109479df9d133392c3f45103a12705f4f788c0256110fe786465fbb0  logs/n42/B_b11_N42_v3.err
       85  aa10ec17d0a1b5a79e3477fdb1139e00ae3a56d77b0d086fa94a66212c3a6011  logs/n42/B_b11_N42_v3.out
       33  a930eec518010e30fcb6fe86746a3b8636743c7437e1debe912853952b05153b  logs/n42/B_b13_N42_v3.err
       85  f2bbec2c69b9f8c229a8d83e0ccf14f486bbcc226b88fcb911a8612288818922  logs/n42/B_b13_N42_v3.out
       35  f50a7d21c08d97e4a08b2f3cb681e611769481dfcc9f9de42570f061b2f14ffe  logs/n42/B_b14_N42.err
       88  a96b305202842bd97d7a473c3edd7cd4517ba710512acf0ba3cf2ff8a21c4ccf  logs/n42/B_b14_N42.out
       35  f50a7d21c08d97e4a08b2f3cb681e611769481dfcc9f9de42570f061b2f14ffe  logs/n42/B_b14_N42_v3.err
       85  bdce2bec98bb3e1c3c93a7aea93f6c3aab6c79c88b17f7bd5d2cb1399dadc2ed  logs/n42/B_b14_N42_v3.out
       33  8be17fc77cf6cab9485417cef3b1f62abb857dcc896bf8248e5cd29b693e38f6  logs/n42/B_b15_N42_v3.err
       85  8555b1c680b5ace10cb017f6077b23ced6684bfbdaa7bc573d0ae438876156d1  logs/n42/B_b15_N42_v3.out
       35  d56e6c96210503e9ca0b5f1323cedc84491dccaa2d6dd1eb8037bc314d95cded  logs/n42/B_b18_N42.err
       90  3764c4c47a4135dd3afaf6b0883ac2b76668ef2dba183625a2ce196d1fea1a94  logs/n42/B_b18_N42.out
       35  d56e6c96210503e9ca0b5f1323cedc84491dccaa2d6dd1eb8037bc314d95cded  logs/n42/B_b18_N42_v3.err
       85  bea0bd9086296882f00ede52994f3446037c995b0f943653fa10649be4181597  logs/n42/B_b18_N42_v3.out
       35  2219ac5a302eeaeebab2e8489b3d4565050e84f48647a70815e6f316ef03e792  logs/n42/B_b3_N42_v3.err
       93  4a228907034b94b138c28b68f6cc8a1e952879668edd7716b1f5e2caa7313263  logs/n42/B_b3_N42_v3.out
       32  3c7f3e77908b1fd78f719cb204c7fd4d9c94bfad6bde32ae6debcef8fe808475  logs/n42/B_b5_N42_v3.err
       84  3bc0d75d0ea546c304f71069b9aa0cc418bed56478e270330db46db6e212b730  logs/n42/B_b5_N42_v3.out
       32  bb70d584ff42edbca5a2cde487c92ec0b762b0fb70cf65eec45a24c6bd810c6c  logs/n42/B_b7_N42_v3.err
       84  38dd5db268a84a79d756c100d4a1adcd660e45a9c76f5599415671220fe5b4b6  logs/n42/B_b7_N42_v3.out
       32  2e14b07a93bd028b5876dcedc40fa49ace0f91b594e5a18717d048908544104e  logs/n42/B_b9_N42_v3.err
       84  d7edf3e6494dd67962bbf1a26e7fca20ab7bdb9a27f838baf100bfda9f7ba5f3  logs/n42/B_b9_N42_v3.out
       36  166c9af0a456515c9d6b971e801f8e3ff5e11a19b5148a40f25ca60c866a407b  logs/n42/Bctrl_b6_N42.err
      159  e9be86943b61246cbfef7059ddb0428307ea144c72ec3c0725ecefe7213fc11c  logs/n42/Bctrl_b6_N42.out
     2736  ef8ed182fe108d0a9ed35e1349b0a9bf058fbd07fd2c44414e0c641c16ff8da4  logs/n42/INDEX.txt
      520  a6054959396641e2eb093cd5e9007f3fb7cc2254c5b6a3975c769dcd0252f3d9  logs/n42/code_hashes_n42.txt
       43  1a5d67daa98efc287bbb81bfc6fac83c3178f151771790d4ecbb45d4393beb97  logs/superseded_v2/A_b6_N42_p0.err
      233  dbb2af8ce6c344027a272ad99c04c3d57633cd6fcad484638dc442d4530038fe  logs/superseded_v2/A_b6_N42_p0.out
       43  1a5d67daa98efc287bbb81bfc6fac83c3178f151771790d4ecbb45d4393beb97  logs/superseded_v2/A_b6_N42_p1.err
      137  2203b74bb95dd6b48cde14c8f6ab43f4a4f1f72400ce648f41d12a96ce0a0d81  logs/superseded_v2/A_b6_N42_p1.out
       43  1a5d67daa98efc287bbb81bfc6fac83c3178f151771790d4ecbb45d4393beb97  logs/superseded_v2/A_b6_N42_p2.err
      137  4d049dbcc8371a515f451057e38ba8d4487e1a5195bf46414cf9b44cd7829635  logs/superseded_v2/A_b6_N42_p2.out
       44  788c7dd57cd8c13e68fc8eb2dbc1fd8e880fb422d999a9268c73b3fbb7e2a143  logs/superseded_v3_ub4break/A_b10_N41_p0.err
      137  62944311a7b34aa43b521171ee3cf70f8c098b5435fd460418a1ebefabcb4d32  logs/superseded_v3_ub4break/A_b10_N41_p0.out
       44  788c7dd57cd8c13e68fc8eb2dbc1fd8e880fb422d999a9268c73b3fbb7e2a143  logs/superseded_v3_ub4break/A_b10_N41_p1.err
      137  100df16c76cb325b082419d7e755221838aee2b5d11855b39df456e5e0327a9c  logs/superseded_v3_ub4break/A_b10_N41_p1.out
       44  788c7dd57cd8c13e68fc8eb2dbc1fd8e880fb422d999a9268c73b3fbb7e2a143  logs/superseded_v3_ub4break/A_b10_N41_p2.err
      138  1a51bfa5ca6ae5d1288c86c2ac8c42b47fdd9e87491d0b107eff61f0694f5370  logs/superseded_v3_ub4break/A_b10_N41_p2.out
       44  03a7d953d8e96dba5415e93405437899886547234bc037f939f64508be75ea5c  logs/superseded_v3_ub4break/A_b12_N41.err
      134  947cd1e842d55b9bd05c4b6b6fef68f94e062c432d29fb46d2b853f8221b7652  logs/superseded_v3_ub4break/A_b12_N41.out
       42  805219f5da612a3189e1bcdbcc46cbb17c90e3467e57a6396d1dc8623418b8f6  logs/superseded_v3_ub4break/A_b3_N41.err
      120  55c88d9ab67d8ac87c4e4ab973d86a80c784cd9cf98ac6e7a6ae939747b02ca3  logs/superseded_v3_ub4break/A_b3_N41.out
       42  eba792bd4dd1a399b708193b1976293dfafe69e00f55c6ba4e11efd36cbd7f39  logs/superseded_v3_ub4break/A_b3_N42.err
      120  6a62e0724e592ee19804d59c56fc981f2d29b00f9591da110ad9e51b2bd74bb1  logs/superseded_v3_ub4break/A_b3_N42.out
       43  2e6cae1f1d4764fa9cb7379c91677fb7ac923cffb6699df4fc5dc275b70e5946  logs/superseded_v3_ub4break/A_b3_N49.err
      123  80a5d91f2cd153515111c919c17cbd6b3dcd534d8d38c710edcac79f2fc043ef  logs/superseded_v3_ub4break/A_b3_N49.out
       43  516abe56ddd84821bdd9e27e2f616b00da9c368626c7e1c3e41742c2f982add7  logs/superseded_v3_ub4break/A_b4_N36.err
      529  2e8fbbf17336847ef1c02906900e7b814194cf40aba5472d2ac49536f504332b  logs/superseded_v3_ub4break/A_b4_N36.out
       43  2f7f60f3883b93a8f7a23b205dc8bdf29216e8c0c3802da204d0ebe0f0464f88  logs/superseded_v3_ub4break/A_b4_N41.err
      531  3dca66c8e66c4f462d6d9b06f0218a512ca07977e5500197d62f6d9f33f04de1  logs/superseded_v3_ub4break/A_b4_N41.out
       42  da17aed7abae1d808849bc5d98960dde8d88e8f74791bee7b888e983dc07945b  logs/superseded_v3_ub4break/A_b5_N41.err
      107  638f623bd791fd7aeb4cf42138f11ad447d6f5bd0845c68233716bfa375b1c1a  logs/superseded_v3_ub4break/A_b5_N41.out
       42  ce783af066408ac80f69f5d354886df4c41fd8b6f53600de2776bd3e0f4005aa  logs/superseded_v3_ub4break/A_b5_N42.err
      107  350846b6774874715cdc50e654d1c1c406852c9deb436c3fce6d9359c7e4b921  logs/superseded_v3_ub4break/A_b5_N42.out
       43  1a5d67daa98efc287bbb81bfc6fac83c3178f151771790d4ecbb45d4393beb97  logs/superseded_v3_ub4break/A_b6_N42.err
      236  dc26deb444fc8d45ab308431793a11d252bfa854b780c5681ad752b6893caa6a  logs/superseded_v3_ub4break/A_b6_N42.out
       42  9cff23f94c1965be922d6c24096053f9b64ae84dece92de3e0d4d79482189c24  logs/superseded_v3_ub4break/A_b7_N41.err
      107  b50df665926548cb8d286e9df1afa8b6f485e26745ba5f072d2d72d84fada9a3  logs/superseded_v3_ub4break/A_b7_N41.out
       42  c2a2ffc1259b58f568bd795e2f3e8af9a9eaaf90568a9a435753d69bb940fca3  logs/superseded_v3_ub4break/A_b7_N42.err
      107  807d8b6870c8e940c11995aedb2da21c9056e8040f76d66f95e2bb9ec2226e0b  logs/superseded_v3_ub4break/A_b7_N42.out
       43  2a1405d32b15937bb05c9750a8e4be3f9f97e5d28c09c3489e658ef7b4d00e3f  logs/superseded_v3_ub4break/A_b8_N41.err
        0  e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855  logs/superseded_v3_ub4break/A_b8_N41.out
       42  13b4025b506abe634eb54c84ae2115cacdc293632fe1445629608db4125da0d5  logs/superseded_v3_ub4break/A_b9_N41.err
      107  b12e25e325a0ecec60120602d50426b273cfbaf6b1202a14b42196c54b54a989  logs/superseded_v3_ub4break/A_b9_N41.out
       42  4f7c3d8b3988a3245aecc8379caa52e5ba5e39b8b196b5e2b478f01d3b52170b  logs/superseded_v3_ub4break/A_b9_N42.err
      107  800b31495886adcf62a323a805a35f7fd0541e13617f14355fd33b15d745fd51  logs/superseded_v3_ub4break/A_b9_N42.out
    23539  8109ef57b52de665fa6ad8301e57329c79d7ddd6cce08c3cf717833dd7f2260f  review/REVIEW-paper7.md
    30771  30a187e835c4862a590067544b937302cbfaf7ce4c1279eb2bfca25dccdc06a7  review/REVIEW.md
    19862  16994e6bedd421f3058da87961546176ea81560c7daa515026c371157519b701  review/code/A4_dump.c
    20943  2ba024ee473520347b6b215f82c72890396e86012707cfcb14fc7a94ffff5516  review/code/A_dump.c
    11951  8bf4fe2a0f0c128fe12e62f3776bdda5f32865f6ff7b129d242497bc87c88da6  review/code/B2_dump.c
    11339  c540e747764e9c7d3afe2d0f95b81d9309b0cbe50364e77faeb8dfb522e57c3c  review/code/B2v1_dump.c
     4644  2e3895e81c980db16f9a72ef19705b87e0c9eb62fc94f383dcb2d433b348bc4e  review/code/check_lemmas.py
     1818  e3c936aad8cdc4ba7758ecb841302fd22841d4816979404e7073c67d7bf818fb  review/code/compare_leaves.py
     1830  88fe5f31b475472820c6e4c9e343e4236fa705f76412c269c79b32a0385a224c  review/code/confirmC.py
      228  cc8533f7c1c17238ec3e3316406a012199e00e580dbee95f99d55b7ff86192df  review/code/jobs1.txt
       51  97afc5123093f599a01ed20aa03a6f13ff2481e3ca3de91c4b89254f3b47c775  review/code/jobs2.txt
      127  c71927b19745b00c2c9ab8c5ebede20c8a8e83579c787789c7764c92f67928fa  review/code/jobs3.txt
      137  bf785ee15384d348c855837110c3959000bed8a5218a6647e83afd5aca1db9d6  review/code/jobs5.txt
       81  1655d8b454cae58393a671c543e6118ea030efff4ab97f4ae02d45f113c2f8d0  review/code/jobs6.txt
      303  d299efb52ebadd6fa91c412c87710fdc17be3350574e7fe0057582f3d3b9ba1b  review/code/runjob.sh
     1144  36046f954e11bd9c78aa666c0ecdb58064fe5c22059cb9a020cbeddd2d311e32  review/code/runjob3.sh
      513  e336881ed8c8760d2265b56ccd7fe65c9bd7f69012c6661bf96b7a4b337976f1  review/code/sched.sh
    10501  9401061cc17eff93803767b74aaf31660e9561aa4212109d370ea1cec5feb8d9  review/code/sunC.c
    11212  b3e35c7bc97529ac61559ce9ac373124654d55145a3fdeff5ec0d0347eb3d6a6  review/code/sunC2.c
    11072  f1877f9b08b0c6b40b4be803331595fc1916d6f4c0574f1d6de9009d9287276e  review/code/sunC_batch.c
     1518  0f24c83d09e83da4de408229aa7092c46a14d22b2bb83e8a03e443bf002ed430  review/code/validate_C.py
      346  7a16d2a883acea6513d8eb1c88067c9c51299a09fa3f52b2d3e5282fb4557ce2  review/code/waitlaunch.sh
       72  368f0ea4e36208dee026ad27f539de282a93955bbe6aedf749e0e11bed3530af  review/logs/A4dump_b10_N41_p0of2.err
  1394108  257f3c0520f78b7ddb46946690994d1d5802b578bb6a68d3bb68ae151c6439ae  review/logs/A4dump_b10_N41_p0of2.out
       72  8eb7fa40a1f5d994d1ddc33d62821d8840f22d74f3051f621c57fa6b9a5e6b98  review/logs/A4dump_b10_N41_p1of2.err
  1020927  ad83003ee38f9387adb09dcf2b83fbb2dbaf01f7d3c1cdaa4becce31337f3c6e  review/logs/A4dump_b10_N41_p1of2.out
       65  4e45ff897db6a2945651a4393ce5f92adec192142f6e4e0dcaa113d0c5271900  review/logs/B2v1dump_b10_N41_p0of4.err
   916131  255669090b9fddecd122eb3b4bfd466a67d606c21ff05ab461fbdfe354a108d7  review/logs/B2v1dump_b10_N41_p0of4.out
       65  70b57f7958c5c1397b4cf80851a58e7944cba1436245f1fb8bea947188aca9b5  review/logs/B2v1dump_b10_N41_p1of4.err
   631211  0c660c9bafa023bff544fe79de7f60c5e73c331aeb02b547be3529bd0d53f5db  review/logs/B2v1dump_b10_N41_p1of4.out
       65  c3bd0fffee79e90b3ca7fc52bc6c75f7feb73041f54760ed35f5082d0cfd1c21  review/logs/B2v1dump_b10_N41_p2of4.err
   478079  3e9ce3246d9b2718856a2d0442ca64e6fd823d04e671d2934e3c38f35e67af25  review/logs/B2v1dump_b10_N41_p2of4.out
       65  d0aa75605f41cc468d7fc37170463d6838cc0d34ddc1efda7ed57274582120fd  review/logs/B2v1dump_b10_N41_p3of4.err
   389817  5b46e6a8195e29720381e61d8c9fdb974f147c10dddbdc203af4f78a1a1cda99  review/logs/B2v1dump_b10_N41_p3of4.out
       28  fc6a934d2d5d97da0aa723917273241305d8e6592ba39a67460ad26556f84509  review/logs/C2_b10_N42_prune2_p0of1.err
      113  0afbd34c6d13af50a93ad1c0f6dd3566065f0253c42b6dd9a4a8a94b61e15c75  review/logs/C2_b10_N42_prune2_p0of1.out
       28  9d12bb1187a19a1b24dc71c95aed996cad9bc83ba678dfd508eac0b23a635b8c  review/logs/C2_b6_N42_prune2_p2of3.err
      209  379e8963717d668290f78a5f3ab0f58a35fc89a1009e166ff1d9e9f2ea69e6f7  review/logs/C2_b6_N42_prune2_p2of3.out
       74  6b92c445674bd068cd4e0710d2dcd33f659393a9b6f27270396dc032e691b792  review/logs/C2_code_hash.txt
       59  6edbcd1e6068d0086b5068d3b9dd32d7f32055eb9fbef6186a03381832f9b967  review/logs/C_b10_N41_prune_p0of1.err
      101  b485fc0fcad5ead3ffdb7fa7a3787b1aca04c51b8bd8d6ea5f91a8911fc5c651  review/logs/C_b10_N41_prune_p0of1.out
       28  c644dc249218e97b8e9aaeac713048e52979b937d0772e716866bcea0eb0e177  review/logs/C_b10_N42_prune_p1of4.err
      101  a79df14cab822a3fde750765af30fafa132d595aebe6302b107e9d5fd0121a67  review/logs/C_b10_N42_prune_p1of4.out
       28  a88df30a7f1cb7005dc1710d3597c7c373bccee459a3fb7802e40d8d60fed9ad  review/logs/C_b10_N42_prune_p2of4.err
       96  cee0bf442fab6bdcbc1db50e5390675f703bb7ae382370effc0e27576f998b69  review/logs/C_b10_N42_prune_p2of4.out
       28  b523f67bec20afc2c0f9001668071260e10abb42221610b531d1de5f821734a2  review/logs/C_b10_N42_prune_p3of4.err
       91  0fd0e56bd8b810d41283612c8057f466da7f718f8f94a2f8311e39b3d3c4df89  review/logs/C_b10_N42_prune_p3of4.out
       59  55c3b289de674fc1b92da699f5a9eb8078bedfe32afaf09427af7ade6a38db0a  review/logs/C_b11_N41_prune_p0of1.err
      102  e857778b7a6297365b46bafffa1cf11922a32c1dce5c41020bff220082d12eb0  review/logs/C_b11_N41_prune_p0of1.out
       57  591310191ffca74cbc718747fffe4a62a41bdb86bec4a8b6c165b1b8acd68f6c  review/logs/C_b12_N41_prune_p0of1.err
      101  ec0c4a9e28981cf3713d79dcaeed91604988ad0cf00581553dba649a35bd15c7  review/logs/C_b12_N41_prune_p0of1.out
       57  9b3cc2365c39addf777732e2cfe94aadb98305cacea1990beafd8419bc9d9ea0  review/logs/C_b13_N41_prune_p0of1.err
       96  1f778658c8985c2cdb6460c7796e5835c87b3a8754702b473509382184ff4d71  review/logs/C_b13_N41_prune_p0of1.out
       59  198f38f75caaea1a051c1316306b19682c0a8e2be8fe6a83148758026e1e6e69  review/logs/C_b14_N42_prune_p0of1.err
      104  2daa3f27105858be1e4055dc80f128e7e0a18ccdc68a00474af634100a8c5503  review/logs/C_b14_N42_prune_p0of1.out
       96  6f4f9167e1b01bf58d9de7eee06f19ec538b58ada9c14ba613963068960d223b  review/logs/C_b3_N41_noprune.out
       97  b1324ada214adcf6a773e602fcd0755715e5d0c211335b0f3fd2ca19f75df762  review/logs/C_b3_N42_noprune.out
       28  c1aff37bcab6c56cefd7624cabe5c92bd0d0a6c94b5464951095421899ec1b7c  review/logs/C_b3_N49_noprune_p0of1.err
       98  32afb89e03af8791a3e2915333ca5f8ccbdcec61e71a6450d934b543247548d3  review/logs/C_b3_N49_noprune_p0of1.out
       59  7b5fa5d0808ccc23eb0b9a977445979cb249137ddc64497d0397c8c6b2283fca  review/logs/C_b4_N41_noprune_p0of1.err
      494  cfe2c4f0b29d1499c17fdf588ec6ebf263b75552dac1a4ab3741828e5221463e  review/logs/C_b4_N41_noprune_p0of1.out
       61  bb31b1ae6db20e1a62142d7482ec4887d5d5e6bc3450330351c443d9cf7df3a8  review/logs/C_b5_N41_prune_p0of1.err
      100  6c72e6f31cd7bb763f2d0ae19dc68ca3d8cc32c5efd7eeac573b73cb9188022d  review/logs/C_b5_N41_prune_p0of1.out
       61  94ac138aa9d555ca7f7e062bb13ab9cfeaf1da9d6dd12ea3acfba013d22e0bb8  review/logs/C_b6_N42_prune_p0of3.err
      101  68970ed4b0ca1a67aaf0aec797f4b15a503dcbafa303280f05db897a36d8c21e  review/logs/C_b6_N42_prune_p0of3.out
       61  20baf03669c7951d08db7acef06ccc5dab993e8a812dc936aebbd255ec18ad08  review/logs/C_b6_N42_prune_p1of3.err
      101  31d125c451e5b27991b614235422a516522c460e6eaba5ec8ee07257822be799  review/logs/C_b6_N42_prune_p1of3.out
       61  a85c758b5399797963f18598759a7f4160c7155997694c40295c4c09d639eb5d  review/logs/C_b6_N42_prune_p2of3.err
      198  b01225bc267a3f6aa72ecb06e5ad4662514092a05fb0e118a327a92079af0de0  review/logs/C_b6_N42_prune_p2of3.out
       61  4bfdd0785a3422666d8db9aa127bfcb14f319c1f06c4956048cdeea12929d254  review/logs/C_b7_N41_prune_p0of2.err
      101  ce38574a3334e1cf90d7b4829b8608196a2edbb6e4438706bc348fb6e7a57bfa  review/logs/C_b7_N41_prune_p0of2.out
       61  52ab7f03bacd00605265c996ba2553dc4568ce5e66ac4fc239d3d2a3ea96386c  review/logs/C_b7_N41_prune_p1of2.err
       98  cc2bade5f0a8bb0b84e9e2caf866492f4ad5908d80c7ce1dd578e20866c7483a  review/logs/C_b7_N41_prune_p1of2.out
       61  74ebfc3b7a933412e1ef986c0bf8f1301359734726bc5592cc438b54aa59bd7a  review/logs/C_b8_N41_prune_p0of3.err
      101  88b884441866f5e515f0c3bb745657bba6aa89b1cd130dcb0ae558bf94314842  review/logs/C_b8_N41_prune_p0of3.out
       61  9891e504b7cc0af896dbd25b8045cfb48e0125d8624897d9ead52a0229e60dae  review/logs/C_b8_N41_prune_p1of3.err
      101  1194fa1c2acd86e5add675d662db6fc7dcb9013847e10b779a574edadc6fd8fd  review/logs/C_b8_N41_prune_p1of3.out
       61  126b42a7bf8ea560bd5657f4a352f8a6b5eb6d88ffdc007cea578b602cb88441  review/logs/C_b8_N41_prune_p2of3.err
      101  2efd0684467acc6b03984c04d47cf69684938197b8734f903448d670a1cc1db6  review/logs/C_b8_N41_prune_p2of3.out
       59  3ae9b71bdc840893c412803385de0d28592c7da9a995dbf1dba380ec14cf1462  review/logs/C_b9_N41_prune_p0of1.err
      100  18632b8900d15156862735ebb6de2e1bf0f4d933061134ac599563a0e6757438  review/logs/C_b9_N41_prune_p0of1.out
       73  f2ae6942f961cf1ff633945549bca607085cc0baa024c08b26cb319a88cbd2e4  review/logs/C_code_hash.txt
      548  4ef889548204e3d9de0e52fd2a2a56ead443d896c2c2df6bde0d4fd3df5f0d55  review/logs/compare_leaves_b10_N41.out
      406  d030cf46dac23fe941ee6b0218d12bbb719c00484717f28fc6f61cfe37e02a15  review/logs/dump_provenance.txt
        0  e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855  review/logs/queue1.log
        0  e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855  review/logs/queue2.log
      373  7300c4a24d3d3662615ec850d91d837ad71ee6cf01048b2d6e769ef0f764ae7e  review/logs/queue3.log
      448  ce5ffaad12eff09209310943acc2f09960a640a3625ca4db5d8893f0a258d9e5  review/logs/queue5.log
      197  df2b093bda5fbd2268beb80bf1d354b498f8b26ba6871a4856d3edec2ada2d2c  review/logs/queue6.log
      106  dcc1dd9e9291592e4c7b5f2d22bba0f8035ce3d49eaa416e36a933b23ff85b53  review/logs/superseded_modified_versions/Adump_b10_N41_p0of2.err
  1394108  0baf009b16751870fb7105d72241341a5580bd04c355baa94bf3ed21752a06c2  review/logs/superseded_modified_versions/Adump_b10_N41_p0of2.out
      106  8b6bd1a82e211368a324a5fad27f032233c40770bb39e2a4ee6ee5c9bcc7cd92  review/logs/superseded_modified_versions/Adump_b10_N41_p1of2.err
        0  e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855  review/logs/superseded_modified_versions/Adump_b10_N41_p1of2.out
       63  63a185024f69c3f8bc4d69ab70d2bd888a57219cd9ad988f4fcb9f499ffd715c  review/logs/superseded_modified_versions/B2dump_b10_N41_p0of4.err
   135168  252629dde81ae5e26a603ad487896c91c42cddc4ca89d6a3b72112c22df09600  review/logs/superseded_modified_versions/B2dump_b10_N41_p0of4.out
       63  2376664bbae425a3e41c5ad77a77f79cf8d40dcd492ed3711d31e5f433052ec9  review/logs/superseded_modified_versions/B2dump_b10_N41_p1of4.err
   417792  e14f79c9726b33f7d7cb81b13fd8276d9c8a01b44bd9de945bf16c45bd65f7fd  review/logs/superseded_modified_versions/B2dump_b10_N41_p1of4.out
       63  0bd8f5668b19198185116c254797cbe748fa06abc9b12343901bfa8aaaf285b5  review/logs/superseded_modified_versions/B2dump_b10_N41_p2of4.err
   478078  3b34e7dd204a0bb4659518d9a8d6105c468270e60d7683f6bcb10f131f47b4b3  review/logs/superseded_modified_versions/B2dump_b10_N41_p2of4.out
       63  e3b4857de4258900e507c6e0e0d05b361dfee2e7cb778a5f9155163941e75000  review/logs/superseded_modified_versions/B2dump_b10_N41_p3of4.err
        0  e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855  review/logs/superseded_modified_versions/B2dump_b10_N41_p3of4.out
       28  9ba55b20f27ca07ba22a95dbadbc7df6fa2c51c3953ce4bc631172d468a2f556  review/logs/superseded_modified_versions/C_b10_N42_prune_p0of4.err
        0  e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855  review/logs/superseded_modified_versions/C_b10_N42_prune_p0of4.out
      116  1fb8a6202a9d032c81ae40be86c8d02ddac5b831e732fb0676403a114b14aae4  review/logs/superseded_modified_versions/README.txt
     1044  4a71eab91449b04ead4e6e0fd1ce458c3cb2b26dc085cb7e0bdf5445b08c79cf  review/paper7/code/bms21_spot.py
     1401  44da905e5273232b303aa743824abed867480ad8f71ef716f00f44d341a228c7  review/paper7/code/confirm_D.py
     2394  5f9cf51615af3ca22a80d1fcc10e8e955efaad802de3ba410e03b3db2dd7e5dc  review/paper7/code/numcheck.py
    12910  5d913b626f9dc685c4fa1c8781780033de0caa316162b3a3cfd615c3fddc5323  review/paper7/code/sunD2.c
    13177  e1a42832a46bd85deda333e8d8a4f243c4556e0c970ff7ac85dcd59b14b65fea  review/paper7/code/sunD3.c
    13177  18a172d9cb9e42da66db8709d12c3d4a51fee34857a0182e21ae77af130a2629  review/paper7/code/sunD3_maxb16.c
    10551  167d5a43514c4ef999e566ac22ed5f19b09230be3e65039e601b6f1b5e4f98d9  review/paper7/code/sunD_v1.c
     4195  a4af9b8b5f5cfa32963284253c80f3a1068499154491cb22a69717efa70981f3  review/paper7/code/validate_D.py
      134  ddce2889c61e008f959a349ca3c705578e58ce5b84a52a70a68879a5cfb0515d  review/paper7/logs/D1_b6_N42_all_p0of3.err
       98  e79318ccd4bf120f19cc50fa4a1cf2a9ec711cc09404ffc91c385ab99be0aeab  review/paper7/logs/D1_b6_N42_all_p0of3.out
      134  4004459712665a1c4777ed2c82b56d15abca08ccd07f8be9db1eb1e0e1d0d019  review/paper7/logs/D1_b6_N42_all_p1of3.err
      548  236e3b35a192f9e0e728368eed671b52b98ee00a6b8d8467fee9d19a42f8216e  review/paper7/logs/D1_b6_N42_all_p1of3.out
      134  b0f9e9a411956cc6ebca403827297f6400ae68f9d9163bafd9ee07d311664ec1  review/paper7/logs/D1_b6_N42_all_p2of3.err
      188  fede41f2a4812887265c3098ce349bf35ff2563484152dbc9958c08aa7f71580  review/paper7/logs/D1_b6_N42_all_p2of3.out
      136  7a9bef0d207eac693e49f95a41c136b0c3f490b21c568b524b65277a4f2c1952  review/paper7/logs/D2_b10_N42_all_p0of3.err
      106  3ac6547a9ea56a3127454ce90d6a916d79361a3aac2a3f603799ce9940025a50  review/paper7/logs/D2_b10_N42_all_p0of3.out
      136  e1cd27cdd4d4b1666e7cdfb81a3c9c798d8d5ab5497020caee2431ca3bc3d5fd  review/paper7/logs/D2_b10_N42_all_p1of3.err
      106  ad1597a9beb255d11038093b60838f21d234ad904822f5cdb5815f0827dc9ede  review/paper7/logs/D2_b10_N42_all_p1of3.out
      136  cf85f2fab1ef2ca5f9f387b9ed03a196bf47865721c73b3fd3208fdfbeee5c5a  review/paper7/logs/D2_b10_N42_all_p2of3.err
      105  d1555adda351306848e7d3764006dbbd35b6a4db9e916727ee6f4b95abea56a9  review/paper7/logs/D2_b10_N42_all_p2of3.out
      143  16d348ba367f6368cbdf4f9010a1f6ed33f961bdb7b64bbcfd1680fd0b75f77e  review/paper7/logs/D2_b10_N42_canon_wmax.err
      111  1a0036fe788e769b32ea1ef9910044b886332db68bd1e0859b4f73fbdc211638  review/paper7/logs/D2_b10_N42_canon_wmax.out
     1433  9b3ddc11a438d6d26930079950c21e5bdd72a1fb40870ca6402849147c60863e  review/paper7/logs/D2_b4_N49_all.out
      340  9dc3e8910a185354306b56da20638d9f9b5f66cee83cb02360f8c7e416af7246  review/paper7/logs/D2_b6_N42_canon_wmax.out
      251  fec84be8a49d2d03f59f604d6ec4394f371c3c330bd7a9c2073c866cfc210763  review/paper7/logs/D2_b8_N41_canon_wmax.out
      253  85e2c816f364b7750022efab044d673b523996772eaff189bed97fe79f4097aa  review/paper7/logs/D3_b10_N41_canon_wmax.out
      251  ed6217049a93ea865b0ee239935a6d239480d29de2d995c30873eb37a6ef2fa7  review/paper7/logs/D3_b12_N41_canon_wmax.out
      252  9f8ea666d8d6292efc4da02372db67fd57fc0ae0b1c759b11e06c5a41ced12fd  review/paper7/logs/D3_b14_N42_canon_wmax.out
      248  3ef260f0a61c6a1d44edaaac9144c9761fd9d95cbc2ebf5c160d3746fe2db3dd  review/paper7/logs/D3_b18_N42_canon_wmax.out
      234  36adb39a9d032cb98246ca24ab82e3d2926c9cd530c0700beca139a28c0643d2  review/paper7/logs/D3_b22_N42_canon_wmax.out
      234  2f7d2018b35012b45dea6274a46feb45250c5277c1e6760ac8c506526fa3eeb6  review/paper7/logs/D3_b26_N42_canon_wmax.out
      234  1115b9f494fe424db5841b1e02a51c66e741faef0a47dbb8dc16853c2f2e4740  review/paper7/logs/D3_b30_N42_canon_wmax.out
      239  1589cf87a392d3aaed3de87d387911dcb9104e67ce1b83dbe4769bcaa825a4a0  review/paper7/logs/D3_b3_N42_all_np.out
      239  c905fdeeb74e1dbf12dee90bf7927d7d2da1c9a1cab504d499a8884cf9c73733  review/paper7/logs/D3_b3_N49_all_np.out
      703  243e9c1c5bfac5232a4c7f7492c0ccfde9f0f1a6cf9b0987b57b92709b668574  review/paper7/logs/D_code_hashes.txt
     2809  01b3934770de19851bddd737d50b037a626e54c7fb82cef998c51767a2310c94  review/paper7/logs/D_small_controls.log
       25  068424f06e6789983345f13e23f3b31276e2807ce304ce2057b1e8020ad55a76  review/paper7/logs/bms21_spot.log
      788  d3d79866296321cf79ac0a6044147ae084c203ef0485b1c80d012715660e8429  review/paper7/logs/confirm_D.log
      440  cab6c6e7b7a65beb8f20fa72c55bfc087a6f7450e4c221125cfe44d84ce665ff  review/paper7/logs/numcheck.log
      233  636c461adcb7cb05654f2a69ecbaeaef6614666bf7b5600e78c24b6a8b1ceac6  review/paper7/logs/reproduce_unrefereed/A5_b14_N42.err
      126  7f6277de35bf9817d5f8ca74091bfbc720488236e9d82e3a01f4e6ab4df57c5f  review/paper7/logs/reproduce_unrefereed/A5_b14_N42.out
      122  94bebb1d26c3b3075d3153735962c559e2a7be98282039f9625b7e61f3ddc3dc  review/paper7/logs/reproduce_unrefereed/A6_b10_N42_lemN1.err
      138  6edb4786e8c2b3737c3e2c1ea240ef7fd77bf5132bbf9093a3a17cde24061bb3  review/paper7/logs/reproduce_unrefereed/A6_b10_N42_lemN1.out
      704  f50f63a705204b67d588e3384b5408736cc01d377da089976fc14b9f4c877a4e  review/paper7/logs/reproduce_unrefereed/A6_b4_N49_lemN1.out
       64  a16bd7c25957ecc1f14e3f82f5ff92687f198f580e330542f002f8dd5de06705  review/paper7/logs/reproduce_unrefereed/B3_b10_N42.err
      101  52771ba4398d2bead7c6c7d889716d64c459821f414f0a96a3fea92d8f11c341  review/paper7/logs/reproduce_unrefereed/B3_b10_N42.out
       93  4a228907034b94b138c28b68f6cc8a1e952879668edd7716b1f5e2caa7313263  review/paper7/logs/reproduce_unrefereed/B3_b3_N42.out
       74  bf055242030d83806c23c5df19c9fbe3a8643701986c3984220856ef9de08717  review/paper7/logs/sunD2.sha256
       74  113150f49d00637d60fa50fecc233d9893761b1d247da94ee7fd231644fd2658  review/paper7/logs/sunD3.sha256
       76  8a377dc4c231cbe3a905c507bf94b85d930512240fdea0d24a7cea255781d24b  review/paper7/logs/sunD_v1.sha256
      180  868da8ec71ddbf927f1670ae240fe111fa011fc3437b8a056915e1c465c3cfc9  review/paper7/logs/validate_D_250_seed11.log
      184  f43194e6fa9d74b07fcaa464a45fdcbf1c903493d224cbb43c5ac116d34700d7  review/paper7/logs/validate_D_3000_seed2026.log
```

The folder holds 378 files (7762249 bytes), plus this file. By folder:

- `code/`: 17 files, 196376 bytes;
- `logs/` (with `logs/n42/` and the superseded logs): 191 files, 23253 bytes;
- `review/`: the two reports (54310 bytes), `review/code/` (20 files, 109620 bytes), `review/logs/` (82 files, 7262677 bytes) and `review/paper7/` (52 files, 72206 bytes);
- `checks-addition/`: 12 files, 12087 bytes;
- the top level: `CONTRACT.md` and `PROOF-working-note.md`.

The paper (`papers/sun-graphs/`):

```
    bytes  sha256                                                            path
   524593  beb237c7add868991fb033b2a225480b2d511fd3d40a0f5f1ef35bb823d77d23  papers/sun-graphs/note.pdf
    48957  ff83e00f475556446a7d484794850b13057e2e1235b44d81aff830ac36711686  papers/sun-graphs/note.tex
```
