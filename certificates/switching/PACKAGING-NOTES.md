# Packaging notes: certificates for the paper on the switching conjecture for trees of diameter at most 4

Staged on 27 September 2026 (UTC), 01:40–01:58, for release v1.7.0, by an AI agent (Claude Code) that did the release packaging. Nothing was pushed or published.

- Paper: `papers/switching-diam4/note.tex` and `note.pdf` (15 pages), *The switching conjecture for main eigenvalues holds for trees of diameter at most 4*. Both are byte-identical copies of `<project>/outputs/Switching-diam4/note.tex` and `note.pdf` after the author's sentence was added (27 September 2026); the hashes are at the end of this file.
- The paper cites this directory for its programs and logs and for the Lean build and replay logs ("version 1.7.0 …, directory `certificates/switching/`"). The Lean sources are not here: they are in `lean/Research/` of this repository (`SwitchingThmH`, `SwitchingRowCount`, `SwitchingDiam4Cubic`, `SwitchingWalkProfile` and their `…Audit` files), which this packaging did not touch.
- Everything except `checks-addition/` comes from the working folder `<project>/work/round6/switching/`, with the same relative paths:
  - `code/`, `logs/`: session 1 (all trees with n ≤ 24; the sequence a(n) of Remark 8.1);
  - `diam4/code/`, `diam4/logs/`, `diam4/s3/`: sessions 2 and 3 (trees of diameter at most 4, including the finite search of the proof);
  - `review/`: the referee's report `REVIEW-diam4.md`, its programs (`code/rv_*.py`), logs and `SHA256SUMS`;
  - `lean/`: the logs of the four clean-directory Lean replays and the checksum list of the replayed sources;
  - `PROOF-working-note.md` (= `PROOF.md`) and `CONTRACT.md`.
- Who wrote what:
  - `code/`, `logs/`, `diam4/`, `lean/`, `PROOF-working-note.md`, `CONTRACT.md`: the agent that did the research (Claude Code);
  - `review/`: the independent referee agent (Claude Code, same model), which had not produced the work;
  - `checks-addition/`: this packaging agent (see "Changes made during packaging", item 4).

## What backs what

Paper numbering: Lemma 3.1 (spectrum), 3.2 (main eigenvalues after switching), 4.2 (leaf row), 4.3 (bare row), Corollary 4.4, Proposition 5.1 (no branch with two leaves), Lemma 5.2 (counting), Proposition 5.3 (b* ≥ 13), Lemma 5.4 (the finite set R), Propositions 5.5 (the search) and 5.6 (the three trees), Remark 8.1 (a(n)).

| Claim (paper) | Programs | Logs |
|---|---|---|
| Prop. 5.5, program (1): R has 13,376 trees; 10 fail the cheap test; 3 remain | `diam4/code/final_region.py` | `diam4/s3/final_region.log` |
| Prop. 5.5, program (2): a superset of 7,892,382 multisets; the same 10 and 3 | `diam4/code/final_region_indep.py` (imports `region_indep.py`, `row_lemmas.py`) | `diam4/s3/final_region_indep.log` |
| Prop. 5.5, program (3), the referee's: the same set; 13,199 / 176 / 1 trees with 0 / 1 / 2 non-even pairs; the same 3 | `review/code/rv_region.py` | `review/logs/rv_region.log`; the set itself in `review/logs/rv_region_list.txt` |
| A certified good switching for every tree of R, exact rank for the 3,029 with n ≤ 40 (referee) | `review/code/rv_certify.py` | `review/logs/rv_certify_region.log` |
| The designated rows of the other 13,373 trees of R | `diam4/code/final_region_witness.py` | `diam4/s3/final_region_witness_s0.log`, `_s1.log` |
| Prop. 5.6: the switchings of T(2,2), D(2,2) and K₁,₄, by rank and by the (μ/p)(A)s test | `diam4/code/five_refined.py` | `diam4/s3/five_refined.log` |
| Prop. 5.6, the referee: 72 of 128, 16 of 64 and 12 of 32 switchings are good | `review/code/rv_exceptional.py` | `review/logs/rv_exceptional.log` |
| Prop. 5.1(c) redone; certificates for the families of Prop. 5.1 (referee) | `review/code/rv_families.py` | `review/logs/rv_families.log` |
| Lemmas 4.2, 4.3: 41,039 rows (380,520 switchings) of 11,535 multisets | `diam4/code/test_refined_rows.py` | `diam4/s3/test_refined_rows_*.log` |
| Lemma 5.2, (a′) at β = b* for b* ≥ 13, only the three trees fail (a′) and (b′): 375,820 multisets | `diam4/code/test_bounds.py` | `diam4/s3/test_bounds_*_s*.log` |
| Lemmas 3.1 and 3.2 on 400 trees (referee) | `review/code/rv_spectrum.py` | `review/logs/rv_spectrum_seed7_400.log` |
| Rows of 69 trees (51 + 18), including T(15) and T(18,0,0); 9,114 multisets (3,374 + 5,740) end to end (referee) | `review/code/rv_rows.py`, `rv_endtoend.py` | `review/logs/rv_rows_b2-12.log`, `rv_rows_b13-40.log`, `rv_endtoend_3-22.log`, `rv_endtoend_23-26.log` |
| Section 6: all 63,242,254 trees with 3 ≤ n ≤ 24, implementation B | `code/swtrees.c`; for n ≥ 19 run by `code/run_swtrees.sh` | `logs/swtrees_B_n3-18.out`, `logs/swtrees_B_n19_s0.out` … `n24_s2.out`, `logs/swtrees_B.log` |
| Implementation A for n ≤ 21, and with NetworkX trees for n = 22 | `code/swtrees_A.py`; `code/swtrees_A_shard.py` (n = 21); `code/swtrees_A_nx.py`, started by `code/launch_A22_after_B.sh` | `logs/swtrees_A.log` (n ≤ 20), `logs/swtrees_A_n21.log`, `logs/swtrees_Anx_n22_s*.log`, `logs/launch_A22.log` |
| 376,324 multisets with 3 ≤ n ≤ 44; d also from gcd(φ, φ′) for n ≤ 30 | `diam4/code/verify_diam4.py` | `diam4/logs/verify_diam4_*.log` |
| 23,023 multisets with n ≤ 30, by the rank over ℚ (referee) | `review/code/rv_certify.py` | `review/logs/rv_certify_upto30.log` |
| Non-even pairs: 373,837 / 2,442 / 44 / 1 of the 376,324 multisets | `diam4/code/noneven_census.py` | `diam4/s3/census_*_s*.log` |
| Remark 8.1, lower bounds of a(n) | `code/lower_bounds.py` (runs a binary built from `code/swtrees_witness.c`), `code/crosscheck_galois.py` | `logs/lower_bounds.log`, `logs/crosscheck_galois_all.log` |
| Remark 8.1, upper bounds of a(n) | `code/swtrees.c`; `code/swtrees_A_tiers.py` (n ≤ 20) | the `logs/swtrees_B_*` files above; `logs/swtrees_A_tiers_fast.log` |
| Remark 8.1, the 39 trees at n = 24 | `code/swtrees_print.c`, `code/verify_hard24.py`; `checks-addition/` | `logs/swtrees_print_n24_s*.out`, `logs/hard24_*.txt`, `logs/verify_hard24_*.log`; `checks-addition/verify_hard24_missing7.log` (see item 4 below) |
| Remark 8.1, the 13-vertex tree needs three switched vertices | `code/three_flips_needed.py` (also the n = 13 witness of `lower_bounds.py`) | `logs/three_flips_needed.log` |
| Section 7: builds and clean-directory replays of the four Lean files | the sources in `lean/Research/`; `code/lean_clean_replay.sh`, `code/lean_clean_replay_thmH.sh` | `lean/replay-*/replay.log` and `build.log`; `logs/lake_build_SwitchingWalkProfile.log`, `diam4/logs/lake_build_SwitchingDiam4Cubic.log`, `diam4/s3/lake_build_SwitchingRowCount.log`, `diam4/s3/lake_build_SwitchingThmH.log` |

Working note only (not cited by the paper): the other programs of `diam4/code/` with their logs in `diam4/logs/` and `diam4/s3/` (the constructions and families of sessions 2 and 3, and the NT = 2 … 5 region searches and their re-check, which the final search supersedes); `review/code/rv_hard13.py` with `review/logs/rv_hard13.log`, `rv_endtoend_big34.log` and `rv_realizability.log`, cited in the report; `logs/crosscheck_galois_n24_tree0.log`.

Every program the paper names is here, checked by a script against the `\code{…}` names in `note.tex`: 8 in `code/`, 8 in `diam4/code/` and 7 in `review/code/`. The four Lean files and their audit files exist in `lean/Research/`.

## How to run (from this folder)

Python 3 with SymPy and NumPy (NetworkX for `code/swtrees_A_nx.py`) and a C compiler. The programs find their modules relative to their own location, so they can be started from any directory; add `-B` to keep the folder free of `__pycache__`.

```
python3 -B diam4/code/final_region.py            # = diam4/s3/final_region.log, under a second
cc -O2 -o swtrees code/swtrees.c
for n in {3..18}; do ./swtrees $n; done          # = logs/swtrees_B_n3-18.out, about 12 s
python3 -B diam4/code/verify_diam4.py 3 16 1 0 --check-d    # = diam4/logs/verify_diam4_3-16.log
cc -O2 -o code/swtrees_witness code/swtrees_witness.c
python3 -B code/lower_bounds.py                  # = logs/lower_bounds.log; needs code/swtrees_witness
python3 -B code/verify_hard24.py checks-addition/hard24_missing7.txt   # = checks-addition/verify_hard24_missing7.log
```

Usage of the others:
- `swtrees n [m r]` and `swtrees_print n [m r]` (shard r of m; `swtrees_print` also prints the trees that needed random search); `swtrees_witness n target`.
- `swtrees_A.py NMAX`; `swtrees_A_shard.py N m r`; `swtrees_A_nx.py n m r`; `swtrees_A_tiers.py NMAX [full|fast]`; `verify_hard24.py FILE [m r]` (reads the `HARD` lines of FILE); `crosscheck_galois.py VERIFY_LOG index kmax`.
- `verify_diam4.py NMIN NMAX m r [--check-d]`; `test_bounds.py N0 N1 m r`; `test_refined_rows.py N0 N1 [m r]`; `noneven_census.py N0 N1 m r`; `final_region_witness.py m r`; `final_region.py`, `final_region_indep.py` and `five_refined.py` take no arguments.
- The referee's commands are in §7 of `review/REVIEW-diam4.md`; run them from `review/`. `rv_region.py` writes `rv_region_list.txt` into the folder given as its argument.
- `code/run_swtrees.sh` and `code/launch_A22_after_B.sh` (zsh) write into `logs/` of this folder and would overwrite the shipped logs; `diam4/code/run_indep_after_NT5.sh` writes into `diam4/s3/`. The two Lean scripts `code/lean_clean_replay*.sh` need the project's working layout (`work/research-lean`, `work/toolchains`), which is not part of this repository; they stop at once unless `P` is set to the project root.

## Smoke tests of this package

Run on 27 September 2026 from 01:42 to 01:52 UTC, after staging. Tools: Python 3.12.4 with SymPy 1.13.1, NumPy 1.26.4 and NetworkX 3.4.2; Apple clang 21.0.0; macOS 26.6.2 on arm64. A Lean build of another agent was running on the machine at the same time (load average about 40 on 18 cores), so the times are only indicative. Python ran with `-B`, binaries were built outside the package, and the runs were made one at a time, with one thread each.

1. **Required: `diam4/code/final_region.py`**, run in place: 0.70 s (0.55 s user). Its output is byte-identical to `diam4/s3/final_region.log`: 13,376 trees, 10 survivors of the cheap test, and the 3 trees T(2,2), T(2,0,0) = D(2,2) and T(3) = K₁,₄.
2. **Required: a tree-verification program at small n.** `code/swtrees.c` (implementation B) compiles with `cc -O2 -Wall` with two warnings (an unused function `addm` and an unused variable `order_`). `./swtrees n` for n = 3, …, 18 took 12.4 s in all; the output is byte-identical to `logs/swtrees_B_n3-18.out` (for example n = 18: 123,867 trees, all certified).
3. **The relativised programs**, run from a byte-identical copy of this folder in a scratch directory, started from another directory:
   - `diam4/code/verify_diam4.py 3 16 1 0 --check-d` (0.6 s): identical to `diam4/logs/verify_diam4_3-16.log`;
   - `code/three_flips_needed.py`: identical to `logs/three_flips_needed.log`;
   - `diam4/code/five_refined.py`: identical to `diam4/s3/five_refined.log`;
   - `diam4/code/test_refined_rows.py 5 16` (2.5 s): identical to `diam4/s3/test_refined_rows_5-16.log`;
   - `diam4/code/region_search.py 2 1 0` and `diam4/code/region_indep.py 2 1 0`: identical to `diam4/s3/region_NT2.log` and `diam4/s3/indep_NT2.log`;
   - `diam4/code/test_bounds.py 4 20 4 0`: its 17 lines for n ≤ 20 are identical to the first 17 lines of `diam4/s3/test_bounds_4-32_s0.log`; its last line is the end-of-run `DONE` line;
   - `diam4/code/noneven_census.py 3 20 3 0`: identical to the first 21 lines of `diam4/s3/census_3-40_s0.log`;
   - `code/swtrees_A_tiers.py 13`: identical to the first 12 lines of `logs/swtrees_A_tiers_fast.log`;
   - `code/swtrees_A_shard.py 12 1 0` and `code/swtrees_A_nx.py 12 1 0`: 551 trees each, all certified exactly (= A000055(12) and the n = 12 line of `logs/swtrees_A.log`);
   - `code/lower_bounds.py`, with `code/swtrees_witness` built in the copy (6.2 s): identical to `logs/lower_bounds.log`;
   - `code/verify_hard24.py logs/hard24_first8.txt 8 0` (tree 0 only, 1.8 s): identical to line 1 of `logs/verify_hard24_first8_s0.log`;
   - the zsh idiom `${0:A:h:h}` of the three run scripts resolves to this folder (for `diam4/code/run_indep_after_NT5.sh`, to `diam4/`), and `P=${P:?…}` stops the Lean scripts when `P` is not set. The run scripts themselves were not run.
4. **The referee's `review/code/rv_exceptional.py`**: identical to `review/logs/rv_exceptional.log`.
5. **The referee's set comparison** (REVIEW-diam4.md §4 and §7, 00:33): `final_region.region()` gives exactly the 13,376 trees of `review/logs/rv_region_list.txt` (equal as sets, none on either side only; largest n = 124).
6. **C sources.** `swtrees.c`, `swtrees_print.c` and `swtrees_witness.c` compile with `cc -O2 -Wall`, each with the same two warnings.
7. **Numbers in the logs** agree with the paper: implementation B's per-n counts sum to 63,242,254 trees with 0 failures and 0 gcd failures, its tree counts are those of A000055, and its largest category per n (one, two or three flips, and random search for 39 trees at n = 24) matches a(3), …, a(24) of Remark 8.1; A′ at n = 22 checked 5,623,756 trees; `verify_diam4` 376,324 multisets with 0 failures and `d_mismatch=0` for n ≤ 30; the census 373,837 / 2,442 / 44 / 1; `test_bounds` 375,820 multisets (105,970 with b* ≥ 13, 0 violations); `test_refined_rows` 11,535 multisets, 31,925 + 9,114 = 41,039 rows, 282,968 + 97,552 = 380,520 switchings, 0 violations; `final_region_witness` 6,686 + 6,687 = 13,373 trees, 0 violations. Every declaration of Table 1 has a line in a replay `build.log` whose axioms are only `propext`, `Classical.choice` and `Quot.sound`, and the SHA-256 of each `build.log` equals the one recorded in its `replay.log`.
8. **No machine paths.** `/usr/bin/grep -r` (binary files included) for the home-directory prefix, the temporary-directory prefix and the user name finds nothing in this folder or in `papers/switching-diam4/`. Neither do the 150 decompressed streams of `note.pdf`. The PDF metadata has the title and the author. The only e-mail address is the author's, in `note.tex`.

The checksum files are shipped as they were written when the runs were made:
- `review/SHA256SUMS` (run `shasum -a 256 -c SHA256SUMS` in `review/`): 23 OK; `querylog.tsv` and `src/e2609.27046` are not shipped.
- `diam4/s3/SHA256SUMS` (in `diam4/`): 51 OK. `diam4/logs/SHA256SUMS` (in `diam4/logs/`): 17 OK. `logs/SHA256SUMS` (in `logs/`): 47 OK; 5 logs are not shipped.
- `diam4/code/SHA256SUMS` (in `diam4/`): 20 OK; the 14 relativised programs differ, as listed below. `code/SHA256SUMS` (in this folder): 5 OK; the 9 relativised programs differ; 10 files are not shipped. `code/lean_clean_replay_thmH.sh` is not in that list.
- `lean/SHA256SUMS`: the Lean sources as replayed on 26 September; see the notes for readers.

## Changes made during packaging

1. **Programs made path-relative (24 files).** They had the absolute path of the working folder written in them.
   - Python: `sys.path.insert(0, '<absolute path>/code')` in `code/` became `sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))`; in `diam4/code/`, the path of `diam4/code` became the same expression and the path of `code/` became `os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..', 'code')`. `os` was added to the first import line. In `code/lower_bounds.py`, `CODE = '<absolute path>/code/'` (the folder of the `swtrees_witness` binary) became `CODE = os.path.dirname(os.path.abspath(__file__)) + '/'`.
   - zsh: `W=<absolute path>` became `W=${0:A:h:h}` in `code/run_swtrees.sh`, `code/launch_A22_after_B.sh` and `diam4/code/run_indep_after_NT5.sh`, and `P=<absolute path>` became `P=${P:?set P to the project root}` in `code/lean_clean_replay.sh` and `code/lean_clean_replay_thmH.sh`.
   - Nothing else changed: each file differs from its source in 1 to 3 lines, and the "before" hashes below equal those in `code/SHA256SUMS` and `diam4/code/SHA256SUMS`, so the programs that made the logs were these versions.

| File | SHA-256 before (as run) | after |
|---|---|---|
| `code/lower_bounds.py` | `7e72b3506edc5193…` | `8b723778eff70339…` |
| `code/swtrees_A_nx.py` | `cb8911f43c393af8…` | `77e775789236e27e…` |
| `code/swtrees_A_shard.py` | `e5d798c3199b19dc…` | `0cb4468d06c284df…` |
| `code/swtrees_A_tiers.py` | `7aa047e51c59b680…` | `65bc042f4581df63…` |
| `code/three_flips_needed.py` | `d9ef6ce2e291c271…` | `acea25a2b478df8b…` |
| `code/verify_hard24.py` | `67f0845d9ae91ce4…` | `7da5f41e95eb8da7…` |
| `code/run_swtrees.sh` | `74335519a3f7d40a…` | `ff859a291ccbfd86…` |
| `code/launch_A22_after_B.sh` | `590b76bdf698bca6…` | `597998c52023399c…` |
| `code/lean_clean_replay.sh` | `a44702621454e2da…` | `d170d517faa5ca92…` |
| `code/lean_clean_replay_thmH.sh` | `6731e5f381287210…` (not in `code/SHA256SUMS`) | `ada33ec1b65ab5e7…` |
| `diam4/code/final_region_indep.py` | `7300fba603f7e91c…` | `0ed8be3a79b3ebe7…` |
| `diam4/code/final_region_witness.py` | `26677f97c85765bd…` | `287d33e2ba844574…` |
| `diam4/code/five_refined.py` | `bc0ea179e4a69514…` | `58d7748f7a52d1b3…` |
| `diam4/code/five_residual.py` | `83e67f839816f14c…` | `99d391e252969f31…` |
| `diam4/code/ht2.py` | `f61de5be0b73bbdc…` | `04e480dd38d58124…` |
| `diam4/code/noneven_census.py` | `6870f9f6ec496029…` | `ba4f58252c879a26…` |
| `diam4/code/region_indep.py` | `2bc7a806f37b854f…` | `ce70bec972e98dd3…` |
| `diam4/code/region_search.py` | `252f326098a39bb4…` | `6d3c7990d23c8b1e…` |
| `diam4/code/row_criterion.py` | `aa8974dfa167f372…` | `5ce8f337a14363da…` |
| `diam4/code/row_lemmas.py` | `21673fc79d27f06d…` | `b60677b8ca055d47…` |
| `diam4/code/test_bounds.py` | `806787da644f321a…` | `23c56f8869c25e16…` |
| `diam4/code/test_refined_rows.py` | `3c0fb9ee3b92e237…` | `a40ec9a8ea22e2be…` |
| `diam4/code/verify_diam4.py` | `4aa3d788e7aa3578…` | `e2a7c5ed1547bb12…` |
| `diam4/code/run_indep_after_NT5.sh` | `5cf86829b189fff6…` | `55ab1e2c2cf94e94…` |

2. **Logs.** In three files the absolute path of the project root was replaced by `<project>`: `lean/SHA256SUMS` (2 lines), `lean/replay-20260926T201207Z/replay.log` (3 lines) and `lean/replay-thmH-20260926T235319Z/replay.log` (3 lines). A script checked that replacing `<project>` back gives the original bytes, so no number or hash changed. SHA-256 before → after: `lean/SHA256SUMS` 7fc217de… → 86f34b1e…; `replay-20260926T201207Z/replay.log` 27f31ba7… → 092b7bcc…; `replay-thmH-20260926T235319Z/replay.log` 95b1d61e… → f623df85….
3. `PROOF.md` was renamed `PROOF-working-note.md`; its content is unchanged.
4. **`checks-addition/` (new).** While checking the n = 24 files it turned out that the seven `logs/verify_hard24_*.log` files have 39 entries but only 32 distinct trees: `hard24_s12_part1.txt` and `hard24_s12_part2.txt` overlap in 7 trees, and 7 of the 12 trees of shard 2 have no entry in any of these logs. For those 7 trees the only recorded switchings were the random ones found by implementation B, whose failure to certify at most three flips is one-sided. So the logs did not back, for these 7 trees, the sentence of Remark 8.1 that exact checks show that none has a good switching with at most three switched vertices and that each has one with |U| = 4 (which the upper bound a(24) ≤ 4 needs), nor the working note's statement that the Galois-factor criterion confirmed all 39. The missing checks were run now:
   - `hard24_coverage.py` (log `hard24_coverage.log`) matches the 39 printed trees against the verify logs by their edge lists and writes the 7 unmatched `HARD` lines, all from shard 2, to `hard24_missing7.txt`;
   - `python3 -B code/verify_hard24.py checks-addition/hard24_missing7.txt` (01:50:07–01:50:19 UTC, 11.9 s) wrote `verify_hard24_missing7.log`: for each of the 7 trees the printed switching is good, no switching with min(|U|, n − |U|) ≤ 3 is good, and a good 4-set exists;
   - `crosscheck_hard24.py`, a driver for `code/crosscheck_galois.check`, confirms with the (μ/p)(A)s criterion that none of the 7 has a good U with |U| ≤ 3 (`crosscheck_galois_missing7.log`, 3.7 s);
   - with the addition, all 39 trees are covered (`hard24_coverage.log`, last line). The values a(24) = 4 and the text of the paper are unchanged.

All other files are byte-identical copies of their sources with their timestamps kept: `cmp` found 178 identical files; the 27 files of items 1 and 2 differ only as described.

## Not included, and why

- Raw responses of the literature searches: `g1/` (75 MB), `diam4/g1/` (12 MB) and `review/g1/` (15 MB).
- The query logs `querylog.tsv` and `review/querylog.tsv`, and `qlog.sh`, the helper that wrote them, which contains a machine path.
- Copies of other people's work: `lit/` (papers, their text extractions and arXiv sources, 8.7 MB), `review/src/` (the arXiv e-print of 2609.27046 with its LaTeX and bibliography) and the publication lists and web pages in the `g1/` folders.
- Compiled binaries: `code/swtrees`, `code/swtrees_print` and `code/swtrees_witness`; only their sources are shipped.
- `__pycache__/` in `code/` and `diam4/code/`.
- Lean: the `.lake/` build products of the four replay folders (files up to 8 MB), and the copies of the Lean sources and of the project configuration made for the replays. The configuration files hashed in each `replay.log` (`lakefile.toml`, `lake-manifest.json`, `lean-toolchain`) are byte-identical to those in `lean/` of this repository, and each replay's `Research.lean` was the two lines `import Research.X` and `import Research.XAudit`; the four recorded hashes of these root files were reproduced from that text.
- Programs and logs that the paper does not use: the regular-graph experiments (`code/swgraph.py`, `regfamilies.py`, `regular_no_single_flip.py`, `profile_search.py` and `logs/reg_families.log`, `reg_diamond.log`, `regular_no_single_flip.log`, `profile_search.log`), exploratory scripts (`code/explore1.py`–`explore3.py`, `cubic_gen.py`, `check_lemmaG.py`, `logs/check_lemmaG.log`), `code/after_prints.sh` (none of the files it would write exists; the n = 24 checks were run as the logs show) and the empty `logs/run_swtrees.nohup`. The working note mentions some of them.
- Size: nothing was left out for size. The largest file here is `review/logs/rv_region_list.txt` (399,349 bytes). No list of the 63,242,254 trees exists: implementation B generates the trees as it goes and logs only counts, so there is no large data file to summarise.

## Notes for readers

- `PROOF-working-note.md` is the working note of the agent that did the research; where it differs from the paper, the paper is authoritative. Its numbering differs: Theorem 9.22 is Theorem 1; Lemma S and Lemma M are Lemmas 3.1 and 3.2; Lemma 9.15.1 is Lemma 4.1; Lemmas 9.15.2 and 9.15.3 with the refined counts of Lemma 9.22.1 are Lemmas 4.2, 4.3 and Corollary 4.4; Theorem 9.22.2 is Proposition 5.3 (with Lemma 5.2); Lemma 9.22.3 is Lemma 5.4; the finite search and the three trees are Propositions 5.5 and 5.6; the cases with all a_i ≤ 1 (§9.7, class D1 and the Main Theorem) are Proposition 5.1; §3.7 is Remark 8.1 and Theorem R is Remark 8.3. Where it calls two of its programs "independent", it means written separately by the same agent.
- **Lean.** `lean/SHA256SUMS` and the four `replay.log` files record the Lean sources as replayed on 26 September. When this package was staged, seven of the eight files in `lean/Research/` had exactly these hashes. `lean/Research/SwitchingThmH.lean` did not: it has SHA-256 f4796e4f… instead of the replayed e3d403c5…, because line 16 of its module docstring was reworded afterwards (finding 2 of the review; the Lean code itself is unchanged). So the logs here do not cover the current `SwitchingThmH.lean`; a replay of it was being run separately and is not part of this package.
- `review/REVIEW-diam4.md` says the referee imported `final_region.region()` once, read-only, to compare the two sets. That comparison was a separate command, not kept; `review/code/rv_region.py` itself imports nothing of ours. Smoke test 5 repeats the comparison. The referee's report also cites files that are not shipped (`querylog.tsv`, `g1/`, the e-print).
- `logs/crosscheck_galois_all.log` was written by a driver that called `crosscheck_galois.check`; the driver was not kept. (The `__main__` block of `crosscheck_galois.py` prints in the format of `logs/crosscheck_galois_n24_tree0.log`.) Its n = 24 part takes the trees from the verify logs, so it covers the same 32 distinct trees; `checks-addition/crosscheck_galois_missing7.log` covers the other 7.
- `logs/hard24_*.txt`: `hard24_first8.txt` and `hard24_s0_rest5.txt` are the 13 trees of shard 0 in order; `hard24_s12_all.txt` has the 26 trees of shards 1 and 2 (shard 2 first); `hard24_s12_part1.txt` (14 lines, written at 20:37 UTC on 26 September, before the print runs of shards 1 and 2 ended at 20:44 UTC, by the file times) and `hard24_s12_part2.txt` (12 lines, all from shard 1) overlap in 7 trees, as described in item 4 above.
- The replays `replay-cubic-…` and `replay-rowcount-…` were made with a variant of `code/lean_clean_replay.sh` that was not kept; their `replay.log` has no `cwd`, `lean` or `shasum -c` lines. The single numbers 8 and 6 in the other two `replay.log` files are the numbers of `depends on axioms` lines in `build.log`.
- `diam4/s3/region_NT5_s*.log` are empty: that search was stopped (`region_NT5_STOPPED.txt`); it is superseded by the final search and not used.
- `review/logs/rv_hard13.log` comes from a time-limited random search (`rv_hard13.py SEED SECONDS`) and cannot be reproduced line by line.
- `code/swtrees_print.c` differs from `code/swtrees.c` only in printing the trees that needed random search and keeping the switching it found; `code/swtrees_witness.c` prints the first tree of a given category and stops.
- Some wrapper lines in `review/logs/` show `$R`, a variable of the referee's shell, not a path.

## File list

This list gives the size in bytes and the SHA-256 of each file. It covers every file in this folder except this one; the two paper files follow.

In this folder (`certificates/switching/`):

```
    bytes  sha256                                                            path
    13619  c677bdda3e51df292815af9f3ec5fab3fc101a4d48466d7651cea79194c388c8  CONTRACT.md
    77002  4a4017afbf858cdc748cf72d638d684d6ed532ea7f57382d505ef0dc5db9088a  PROOF-working-note.md
      602  890e538f5c6770bf5217b159fea84e0491ad95eee2c70cdbd7ced47875213b52  checks-addition/crosscheck_galois_missing7.log
     1172  49b705eb9a8e2b803c432a56ba41ab082b2e624490526a0262632dfa1ac8c5c6  checks-addition/crosscheck_hard24.py
      359  358308747423c57846cebed46097b28516646202d408d4894f85e317aa3a0150  checks-addition/hard24_coverage.log
     2729  4ef3dcd88da05a1b82b98e2d76239b6609fa7a4c45195de3e4eea08805d8b34c  checks-addition/hard24_coverage.py
      910  c8f9a38f66819ba2b2fa78f1a3b107eee6530f1e293b3aa051724d2b8c5149a1  checks-addition/hard24_missing7.txt
     3582  78948083477489b607c2de2f8d6b6a1a9c0fc9e989807822b702375e5940e7f9  checks-addition/verify_hard24_missing7.log
     2100  71f93ad02d6a5edf38b56789e485f78acfd1cfcd403f07c3874f75723436a3e1  code/SHA256SUMS
     2054  e632da1ee1ed764abf034bfde731ab1d8c0d68bb31188892fc8dda3476a55607  code/crosscheck_galois.py
      576  597998c52023399cf218873ce696ee70c48aaf05928e3f50e4df240c8efd90e1  code/launch_A22_after_B.sh
     1822  d170d517faa5ca921712653fae85229e685cc49c06bfce27b3c68f3af465662f  code/lean_clean_replay.sh
     1778  ada33ec1b65ab5e7eb8e66def8f980cd69a56dcd76f6ef88000db7a27eb212b4  code/lean_clean_replay_thmH.sh
     2073  8b723778eff703392c293b2af872f119cb40994735d9761a0d08af6f48a9811c  code/lower_bounds.py
      453  ff859a291ccbfd866188a9cbcb0c2b8b1405685cdc65667ff5efaf7abded372c  code/run_swtrees.sh
    11056  d93fb4e82551ac1165b19c8d631724302ba96ae1e5584dc8abc987e1149afdfc  code/swtrees.c
     6339  136f1072168bb9264c0eb516183c926c4465083d055b474d3ae92312bb432398  code/swtrees_A.py
     1678  77e775789236e27e5f4506ba7d3f00f0c193b2490918f067d20825ff9847a4aa  code/swtrees_A_nx.py
      892  0cb4468d06c284df07a694b29f713b3b27a0e0cebae8ed681d303e5e9b8b28fe  code/swtrees_A_shard.py
     2402  65bc042f4581df6357f2e7ac2f7921abcc6e8910519e525caf127582720ed1d0  code/swtrees_A_tiers.py
    11388  6c9e9c0a263abe954b11e4889354777c1a529d4f70dfdc145ea1679207a84554  code/swtrees_print.c
    11394  019faff0dccd859d3ae58b156f59dccd150ec338a48c5410b5207bda6b4f534a  code/swtrees_witness.c
     1061  acea25a2b478df8bf642eea902542a0dd2d4144b0f87849fa17067411425e30c  code/three_flips_needed.py
     2340  7da5f41e95eb8da7f389eb8b994911ab6b8b28821984a3e65641bd89f44b805d  code/verify_hard24.py
     2973  67239bc2ca61224f8fce958b42bc4464cadc6619a271f9e7f11abfe97de0de73  diam4/code/SHA256SUMS
     4442  9454274e0d251a607566c540692a587719066d159cc7b1a49e497421b5fceca8  diam4/code/constructions.py
     1064  657881f8ad2ec7b099a17845cfae3e731c14e91504c78b1dbfd3149b07bf1386  diam4/code/count_noneven.py
     1644  65d3cac36984787c099e3b40f675e8d4df821234d0747ac650dab594e6b39dcd  diam4/code/coverage.py
     2245  b46029266015d75b37d997b9bf3a76ae6f1f5884a3b9128cc3614b36c0140273  diam4/code/coverage2.py
     1317  488ecebe93e0d0d4a4f23e65e60201405ef01c9bc2f97d95be25e40708df4637  diam4/code/diagnose.py
     1958  fb0c14e603a078fe5d53f99dffe3194ee22120311ff07b3bf6c8574ae5a959db  diam4/code/familyA.py
     1564  dd33728bc230279de4b482a6a294a14b388dc7f38431af0c63ec2c161909c5c0  diam4/code/familyA_search.py
      993  efc0b56daccf7db00820de00164ff5c93395c0e7bff08f1233f624bf49d04897  diam4/code/family_small.py
     4623  1e0ca4e5569c2415bf653d6312170f336839ad83aee4806fef1baa0a793a660e  diam4/code/final_region.py
     4047  0ed8be3a79b3ebe7f1e671027c0850414cc2d321c1570c8965a76b4ebfe4ebcd  diam4/code/final_region_indep.py
     2958  287d33e2ba844574a6c43cd70d780b3ee7ec0331bc3d36856dd43eab3308c172  diam4/code/final_region_witness.py
     3886  58d7748f7a52d1b3977e73f358120ee8ecb32f1e0b213f7781f0787c58f0e71c  diam4/code/five_refined.py
     3246  99d391e252969f31ade29f54763c52f6b6ab7b3e5aaa451e17ba9161da6af6d0  diam4/code/five_residual.py
     2089  04e480dd38d581249f572f58693ac1eedcc9cdd52e7f9534fb7ca816b3d26e90  diam4/code/ht2.py
     4035  3ba6fd16597c4bbc03ac9cf47f769daeb133abf97dd3e678bdb86fb4c3a4f4f0  diam4/code/main_theorem_check.py
     1431  5c71c5f0eb30a7b1760958ddf0e4d46b8d5fbb1b3d18c4cdaaea27ab88f671b4  diam4/code/mod2_test.py
     1892  ba4f58252c879a2685d927f7e280a953d64e1c881c79156c30db5f99d00ef91e  diam4/code/noneven_census.py
     6650  ce70bec972e98dd3002ffc233dc8a0e70318120cef40da15c906a2e64e249653  diam4/code/region_indep.py
     2014  6d3c7990d23c8b1e9ecb80baba46e240915f366e0adbbb1b817706b67897cdbc  diam4/code/region_search.py
     2346  5ce8f337a14363da13ab0c11bba8001adc27e0be9d293f4d2a72bec6a2986872  diam4/code/row_criterion.py
     3384  b60677b8ca055d4764a58bd5c3d3e6df1153c703e1241036dbbc9aa0ede73bde  diam4/code/row_lemmas.py
     2359  e843a075c8f3d26dac9a5401792398810e05a9e4218fb8251a0cf80443843a6f  diam4/code/rules.py
      554  55ab1e2c2cf94e943d0bc35e6c96d3702e2470174d8b4d513cffeaf4b839e95d  diam4/code/run_indep_after_NT5.sh
     1991  ab2f3201db13ece34a8dddcef29ea8a1961a2152e0cf35671b937b96d3f97101  diam4/code/search_sigma1.py
     1920  7b3db3560733a8d619c80d3c55131938b558442801f259f494547087b807b7ed  diam4/code/secular_factors.py
     2184  23c56f8869c25e16e4be7f1f323d0c3bcfaef12b1822b3b47680bdaa1833ef71  diam4/code/test_bounds.py
      981  f8e831ee6652e872206de8846f8779cde68234e46caa3467c4db04411dc4bb88  diam4/code/test_constructions.py
      839  0c6fbca87a60bf5bfc2bb17ff61c574b24d6a20235caef19f0e0ed6f23abc481  diam4/code/test_mixed.py
     2787  a40ec9a8ea22e2bed26d988f5f0b2bb8ff291f24737e60d674364a3a53d340f6  diam4/code/test_refined_rows.py
     1850  d4dafa0d5bf235e1e68a01a59942cd4c42327e2096bcaac82ed05d14c44a6b67  diam4/code/test_row_lemmas.py
     2180  a5b8600ae44df19d6da2d870d582acd77a2468ec87e45b9bba8a37e061a363ca  diam4/code/theorems_check.py
      874  7cbfcd3aadc4326ab83c82f5a010e289fe4ac71a3b67e0f3d9970cf2b05cda96  diam4/code/two_options.py
     1717  802b4b6e9d1073d0131b418567696669f8cb1ac3c03eb9a206031dc3526a0a8a  diam4/code/twoadic_test.py
     3952  e2a7c5ed1547bb1238eb85f28a6adbe0772bc476fa5e06bc9a78a4145d8a061a  diam4/code/verify_diam4.py
     1526  1f98e96dd89bb679308a61778b309315628b3b35f8e7225c1a9c6f32c2513665  diam4/logs/SHA256SUMS
     3286  39041b4c05ab79843bde6e5df05e8c3755d07752cf7ea044413605aabbb790d1  diam4/logs/coverage2_3-30.log
     4582  f26fdafc229026d7ce29027580e5616f2c1c38fb4662265a443bfd07ec752288  diam4/logs/coverage_15-26.log
     1486  fe7ad1204c62ef685a67d400c7c06b1458cef8a53d8f57364e12c295800ab9eb  diam4/logs/coverage_3-14.log
      873  03178b945bfc37d0dfb9c49183d8a2b2c4160a692a158b0fd34e520834d743bf  diam4/logs/familyA.log
      289  5d857f8e8c8005ef6bb0f954e78f0f29b21484617b1f3e6a49b72afcf0201a58  diam4/logs/family_small.log
     1698  41663754632049f7f53a9a81fcfbbf4a8ec4c51fe50d1742c915110fcabce2cf  diam4/logs/lake_build_SwitchingDiam4Cubic.log
    16903  adf3666c62bb5f97c211bb6c45f9a271c380c3a5305bff552e931777f69e40c6  diam4/logs/main_theorem_check_3-30.log
     1205  728b7e3bdf27b9c3e7bada27f5c5e9f9852fd4a2b2f68fdb5f8d688fe2a16e4c  diam4/logs/verify_diam4_17-30_s0.log
     1205  3182cdaa877dc6854ce95f63d50d917dcc4d1b54bdf184f7e451b00b89137a57  diam4/logs/verify_diam4_17-30_s1.log
     1205  4df94b18f05a53944944d306e3abfcf1502ce56b332c91bb5a27bd9831f52ac5  diam4/logs/verify_diam4_17-30_s2.log
     1150  9631ceffe49a1342c2699336ce50dee85c88fcf3855fb044427151883e12ad09  diam4/logs/verify_diam4_3-16.log
      764  97b08f71b92e431bb75bc195f5786b8ec9ab331e6885871e0109b299521b2c96  diam4/logs/verify_diam4_31-38_s0.log
      764  afe3bab2bad35eb9787703e73d98cda8f96af2e8bcd6457505b1da27e8700ebe  diam4/logs/verify_diam4_31-38_s1.log
      754  59ba3ab0388786cb4888b3678c2c3289309b366121c7200618becdf0f31a52e3  diam4/logs/verify_diam4_31-38_s2.log
      583  b5bc14fee2c0ba8a2fdc2ffe4967c3b47f7a71a4c47ec069cc6662c265cdc2e5  diam4/logs/verify_diam4_39-44_s0.log
      603  708e789096394d626dd8d43fc92007d264a83e4b0b7a9d2ee86776a94f8a9865  diam4/logs/verify_diam4_39-44_s1.log
      603  f6f97bee55c4be6b6c108e96f4ef9ce2dbf46c60c6b6e94320edc8fadc1b409a  diam4/logs/verify_diam4_39-44_s2.log
     4633  bc781c07ca8dcd241cf8c0c6d6e6885cafd0e0351e47f245de0865b8cb32acdb  diam4/s3/SHA256SUMS
     2177  b05f0ed761b1236bbbbab49cb2c5f1cf0318b0fd6e5658a41feb803b17956808  diam4/s3/census_3-40_s0.log
     1943  354e9703b9594da302b8f58b782f94925c0224e8be6fa084cbae0237434f2417  diam4/s3/census_3-40_s1.log
     2020  cb5a7205b9a00dc28b3d8805d9d081934f7e0095b601a99b0f93a3f3c6ff056a  diam4/s3/census_3-40_s2.log
      362  4fb11c32e8f3d77e7649e84b2cde26fce639e66929106aa59b2bd1981f23c46e  diam4/s3/census_41-44_s0.log
      723  ecab7fee827bd9cd8ee30d08c24d569215c1b8674af230322e996a6fe6afcb60  diam4/s3/census_41-44_s1.log
      226  d1d5f480f1e868de4f124a4cdd6468159540abceee2f4441818ea07deab8f4d7  diam4/s3/census_41-44_s2.log
      979  dbd1bd388a5b3a6ba15478f01796d42512c44309649d7ab52eb4262c42585677  diam4/s3/final_region.log
     1182  706381a38e2850f73c6e24069910ca8c1ad2759843fccf54f8766d093914d718  diam4/s3/final_region_indep.log
      192  3bf933c242456e2cc156b774e83f6aeb90ac9ffce18dfa848ad32d7655ce8800  diam4/s3/final_region_witness_s0.log
      171  37f528670a8c4440f9c8afccd16e9264d797bb8e1c7887fb59ce984babd5054b  diam4/s3/final_region_witness_s1.log
     2225  e9fe2b02980704909cc8651332d6e7190b6b00803aaee4088987fcf795b7c88c  diam4/s3/five_refined.log
     1194  3845ad07d40815e75e9da1328712113c4ea1ef5162cfa3022a646eed272e2196  diam4/s3/five_residual.log
      200  b7078e6018de5a94c08f8c5e43450f96cab2d5d1ec50ba8e60429a8877d0b0b7  diam4/s3/indep_NT2.log
       47  7316fa74ea95b9619656a2dbf2bacd41b76e7b1e1b766b42ab96b9ecc0251c2c  diam4/s3/indep_NT3.log
       47  7aab5fdfa8c1c363fbe720e6465173f5fa0b66ea42a4d4f643922140ec9459db  diam4/s3/indep_NT4_s0.log
       47  e8a16837851a2c69e2b996d30fc5086cbd6b5a480f507fe6b815ac9e0aab8a20  diam4/s3/indep_NT4_s1.log
       47  e2d76666e9316a19bc7635760c5dab665477fee5b21fdd49488e789def6c24f0  diam4/s3/indep_NT4_s2.log
       47  da4db4dbb98be04679d10b378289f36f703f9cf0597f3cea069900ae7b9cd380  diam4/s3/indep_NT4_s3.log
       42  5373df9ea74b21f960858b0fab7c17a5fbe8c43ff585de16bfecf921b06dc2ae  diam4/s3/indep_run.log
     1518  ce77dc2d35988488aa355636dcba7825c40bba073873719d0cc4692838d5603a  diam4/s3/lake_build_SwitchingRowCount.log
      949  dd595e8592decf66d9507fbcaab09eff326185c793700da19fd082db160fc54b  diam4/s3/lake_build_SwitchingThmH.log
     3267  74945ecd12ab8b82ec5ef1a2d9beb24edd9f1ad2cced498c288aab32d058de94  diam4/s3/multi_pair_criteria.log
     2893  7bca344ef1a2b86c426360d9260a6f26deaa409022a9ce901b5132d1d23c03c8  diam4/s3/nontrivial_N2_table.md
      135  72bef6acd58227b26d4a44215db4cd98c5af4f142ad04e13b3bca64686502190  diam4/s3/region_NT2.log
       57  246ef8d1a228f77648151c77d64f59760b4bbf86a033bd6529e6a6a82883065e  diam4/s3/region_NT3_s0.log
       57  579a9a35e0b8a00f5fb270ed7653500a2368eb6b4c33d4005e305cd47214231f  diam4/s3/region_NT3_s1.log
       57  bb23ed71f8d83c11e9e491c9ce5406f3ce973e945f638ca21b5db61d22d417d1  diam4/s3/region_NT3_s2.log
       58  4ca5b3e3fd70217b04e019adcb58cceb4552e7fe825feb02d716712f5fa75ced  diam4/s3/region_NT4_s0.log
       58  ec897b8471ef210ec7bb7db9ecb67b174d51ebfdfc26a93c0f0149ae2a6bbc1f  diam4/s3/region_NT4_s1.log
       58  a5d6f8d7df9360b97fff44fec3d1a6879ebf9cb757a2f660a91e227e7a8f06eb  diam4/s3/region_NT4_s2.log
      136  09cba41e49458c59925fb828d88ab565ca1d5a352c4d3c6715659a7433f9360c  diam4/s3/region_NT5_STOPPED.txt
        0  e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855  diam4/s3/region_NT5_s0.log
        0  e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855  diam4/s3/region_NT5_s1.log
        0  e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855  diam4/s3/region_NT5_s2.log
        0  e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855  diam4/s3/region_NT5_s3.log
     1077  6aa7f99a107e218e0337a05190ada32d278d1a0f057993bb163216ec8455b01c  diam4/s3/test_bounds_33-44_s0.log
     1077  444262cbfb7f9d5f4d7c247c29effedd32076b6f7611b13f2fe0fefb51e4bf44  diam4/s3/test_bounds_33-44_s1.log
     1077  3379ac7c281bddc5327a8f7783fc0bbf7a2df4acdf11470e1b0857153b9b241b  diam4/s3/test_bounds_33-44_s2.log
     1080  29334d6f2d966a3010f3eacff9bdca60968cbca1b4b5ce0aa955654717842ac6  diam4/s3/test_bounds_33-44_s3.log
     2193  b859d657825bad3e81f96bcda22aab100dece5cbcb3bf7dfb849d1b1c48958ad  diam4/s3/test_bounds_4-32_s0.log
     2283  8ccb423665f863b075c71976f59ffe8eaa14b73fab0fdd1b392421852527c127  diam4/s3/test_bounds_4-32_s1.log
     2712  dd7f61e78a179ab5b0d3c64127950f7365c01277047dfa1041a6976aa3c81342  diam4/s3/test_bounds_4-32_s2.log
     2670  6c369852079f87842f0b50c4f2b667ec97ba5becb565cf71bec41ab059f4af37  diam4/s3/test_bounds_4-32_s3.log
      781  d2f5dd62cd9502ee2b4cb99f386355bf108b7dd79871587178bea7ff17b70dbf  diam4/s3/test_refined_rows_17-20.log
      789  0e90fb8b99da3fe84818d3eba6640453f6be557a80f577ab6f6ef229bc419050  diam4/s3/test_refined_rows_21-24.log
      594  7cb79f1e762f8f135ffd60895bc66b3f7cf4451cd01592c904a33d0002984169  diam4/s3/test_refined_rows_25-27_s0.log
      596  62e844a7121362f7f3bc278eae9ec9c1a037e5cf8544df77e4d39a6c1b0ccd0a  diam4/s3/test_refined_rows_25-27_s1.log
      594  a31a125404495320e1061194412df3215c881f7f06a36e06e08bf9b4d7601d72  diam4/s3/test_refined_rows_25-27_s2.log
      595  65856a77c654d9ba19de55b5be30fb8aa2202941f6c30978d6afee2e32c0f0f2  diam4/s3/test_refined_rows_25-27_s3.log
     2190  422be103cbd60099e9f1b53befb5b1e93bab6e938e082cdac85f63a9f2a6c12f  diam4/s3/test_refined_rows_5-16.log
      498  81d99ee4bd36e65d916d54674776d91a68d655d76c21a49bf73981a6a4481a45  diam4/s3/test_row_lemmas_17-24.log
      808  86f34b1e91eb7a48790a07c75cd5483667f918c97deae870afe78e5b522177cb  lean/SHA256SUMS
     5387  3be2db32b851bde3b474b98a410d67618e415efca682643a4c1672b04ef4c8cb  lean/replay-20260926T201207Z/build.log
     1509  092b7bcc831f8d016ca38c38cb7a97b013e916e9f362a5fded4545eca5ceb119  lean/replay-20260926T201207Z/replay.log
     1577  b89d5ba5de2db3753be9843d16e5f64ea4ea2ce791febb75051325ed8bd3e8dc  lean/replay-cubic-20260926T223154Z/build.log
      725  810b45a288f5b295c2f5c8f23558f4d7464832e593eb3095c1138051ee2bc6b7  lean/replay-cubic-20260926T223154Z/replay.log
     1401  51333acbc91b8f3e5976dce48ec12bee2d007466b3022f7244e101012f750e0a  lean/replay-rowcount-20260926T232846Z/build.log
      721  e5f6032a6083ad7f0000f98e58aebdb74a3bfc484235ead941a8239f7af3c63e  lean/replay-rowcount-20260926T232846Z/replay.log
      949  fad18a1b7357a797354f8d3fe5cf21131289938c372acddd1c4f3bccd0ef3aa3  lean/replay-thmH-20260926T235319Z/build.log
     1221  f623df859525563ca209e9e6d1bbc6ead2e0739e4b6a682333370a462672f6b5  lean/replay-thmH-20260926T235319Z/replay.log
     4596  66699033ed9f6b0ca3e72c5bd0cf8fe39b014e1f30ac6f3f2da63824de79dad9  logs/SHA256SUMS
     4755  d772a5b88b7b48ab7e50f4509d11abb063bd081d7772bd4cdb9a7ef033fd5fb0  logs/crosscheck_galois_all.log
      394  14460186bb002415f1d9fbf6702dca4f082611e2646df74098006ccf8cef4104  logs/crosscheck_galois_n24_tree0.log
     1040  6aae464b757de696382032db34c72ffd5aa414daa132bed74a47a319efd4d7b1  logs/hard24_first8.txt
      650  f373b0dd19e0b183fc0faaed628ae8d202d0b65fe55170d81465fe37b631677d  logs/hard24_s0_rest5.txt
     3380  a4091ada61aebe0d1398ee234f5819080f1e2f5ebd3218e3bb67548fa34eb91a  logs/hard24_s12_all.txt
     1820  609e7490c79ec62c451affeb672c9623162fdc3ed6c077302fe4080ed8c0e1d1  logs/hard24_s12_part1.txt
     1560  5f162b24c647d67a47d21d976ab3351edbe22bba32dc6a113bdd296d822fd517  logs/hard24_s12_part2.txt
     5511  da9cc57de401e9fe19ea843e4b78b7065133e3365a4800d5469cc6b8a2d07206  logs/lake_build_SwitchingWalkProfile.log
      100  6a3f48448ffe8571c9de69ced0c4ba9bf59b33fd063d90943c25661e58f124c3  logs/launch_A22.log
     5213  318270fed454cb898776ecc42e3094e7ffcc39f8100171b82f437153ddcb69b0  logs/lower_bounds.log
      946  d4b6bab925790138db87ad7d6b2942b8eead13160ca878970b2bda823bca26a8  logs/swtrees_A.log
       95  abc6a7bbf42f6e7927a4ecf73bbb1873340016bfa6ece5ffb79d7c4fda65630b  logs/swtrees_A_n21.log
     1228  c8c6355e8e93eac8d9d37cc6868dfb0711c0fb81da08851ec1b6f8a146dba30b  logs/swtrees_A_tiers_fast.log
       99  fad1d93cd9a2f701c59060203f0918fb5cb3329a48714d9198744d420a471687  logs/swtrees_Anx_n22_s0.log
       99  c0710f9ac300f99bf62a7bab2942b1ceba37ff4441b42de74101673b07b7cc84  logs/swtrees_Anx_n22_s1.log
       99  453f0e030a199d43ea8c868bbdf1e311847958976972ccbe1feef94694d55450  logs/swtrees_Anx_n22_s2.log
     5272  547d902ecf9b15bc8eedbfeee48d6787bb8d7f35d711b20196748faffc777684  logs/swtrees_B.log
      225  6ae88a76933338db3bcdaf040eade34d5e052c7a511b67527e1118b046e063a3  logs/swtrees_B_n19_s0.out
      220  181c5b29697ba17367a12beb00037f6877a32736175f6d0fc96316bce66cd70d  logs/swtrees_B_n19_s1.out
      221  9c53c37769fc387eb4c6f71a9857b2c0324e40979f78718b26003af95d47c85d  logs/swtrees_B_n19_s2.out
      278  9a1c8f7d27e3dcdb110184dfae0d9bf148724316dd2a8d2641dd8e9f148875f6  logs/swtrees_B_n20_s0.out
      271  dd4991c073a7db45270f5e98fa2bcc42d67cf0792e3572919ecf9391791878e8  logs/swtrees_B_n20_s1.out
      266  530b1b550f03bd2f46198cadb8cebb248a2afb3ab5e275d34bfba86872353761  logs/swtrees_B_n20_s2.out
      244  7b1d4161dea7a0faf44b66cded2ecc6a533c7c07e458af1fafb839dd4a29e984  logs/swtrees_B_n21_s0.out
      240  859e0d1cc0cc11435db41acdf5f59d0b3eb4b4848b3a94f4bf10c192a0b4af8f  logs/swtrees_B_n21_s1.out
      240  fee2c07ed464c70e4d6c790914722cd184b70bd0c7febd5c89623889a489ccd7  logs/swtrees_B_n21_s2.out
      303  416b37502df2e3d1ead6e32ddd0b522fa4dc3d23113bf365d1efd5eb03128b3e  logs/swtrees_B_n22_s0.out
      303  faf1900e65299fa8878c7a8db12b029d183895cf646840fc8629b03821eba5cb  logs/swtrees_B_n22_s1.out
      298  5512ec76a42b96b5a1b9af62bc7a168aa6d8e833acf25784ed6ba96213d4dd11  logs/swtrees_B_n22_s2.out
      261  2f5fc6e179aafdb73add6d61ea7b6cd0a0b8df717a88b1d9f802be69cfdcaf02  logs/swtrees_B_n23_s0.out
      265  cce6e68abaa166978e222a50dcfad2333000beba7476c2151b64578000230914  logs/swtrees_B_n23_s1.out
      261  749bc8cfcac22be189c77bcaa26f438f9b16369f20c7502fd3e32ea76f74a3b7  logs/swtrees_B_n23_s2.out
      336  ba81f2e047c62d7b4ad841ef19889a56b1ee009dac473ab0d9e659cec698240f  logs/swtrees_B_n24_s0.out
      329  07929b0527c53888745b52067d26847d3e0ea96d200110234491f250c8526bac  logs/swtrees_B_n24_s1.out
      339  a3997c5da7fd68c0be393f1b3143dcdcdc8f95d57b5ae063211bcd244152bd15  logs/swtrees_B_n24_s2.out
     2865  148694cee5e90d2afc199f8b9495a2da32667fd3d2cdc57c5c7227e5fd425a37  logs/swtrees_B_n3-18.out
     2026  35bb6fd935bf23b62303a6a690078bb7e3beef03d9a6352d7e02657e3c10efcb  logs/swtrees_print_n24_s0.out
     2149  4426b968805a5cdccf3e1c21ee46eb31a0dd7b9abbcab6b3d0355df4f7fcece4  logs/swtrees_print_n24_s1.out
     1899  c4784d395a838dd413fadff61350b24cf2993438d1427d530965780ea148c7dd  logs/swtrees_print_n24_s2.out
      259  e982572b7aca9afd9f6e11dfa9a6918add76ff6a0e5b6d271c2e3f2c9b49fe52  logs/three_flips_needed.log
     2043  1a61593d65fb9dff0a2eb0a64d926bfbcbc7684995749cff4b6c7a5b6777610e  logs/verify_hard24_first8_s0.log
     2051  68f93e5dfef56e2ad7323246971906aeebbe8336291b698b83230978d769f5f1  logs/verify_hard24_first8_s1.log
     2552  8fd8efae9a16f553082cdabe2500f9b5aef81cf62c8e5d8c4fd992f557f0bd04  logs/verify_hard24_s0_rest5.log
     3586  998d4a0fc2c4f119dd6b16e75c95e7174d464d0c92ea582533d4347db772f689  logs/verify_hard24_s12_part1_r0.log
     3582  dd134624dd59a70f2a657bf600c0b4c048f5a783f5479dd57ecab707b1f3553e  logs/verify_hard24_s12_part1_r1.log
     3070  6a5758932e72ef50ad3e270183a8a1f6216b49adb06d43e5ae7ad45ffd570e96  logs/verify_hard24_s12_part2_r0.log
     3070  fcd7cb0865b47dc2dc3a0cd1c2e185dd49fbcf5bfbfe37e0e299b12e0d8c6bc6  logs/verify_hard24_s12_part2_r1.log
    20480  de72cdbe4c3b569bc546d6bc204c1175edb176e74d7d8e3dcddc275c1c2e3011  review/REVIEW-diam4.md
     2196  d2d0031ae2085f10904623b784c0e93e798bc9ed49e9a5ea41034a8e30b12143  review/SHA256SUMS
     4119  6d56963a5e58ab761b9247b739173464efc8518fffcdb140b154a10717b81aad  review/code/rv_certify.py
     5842  d14270b79e6e73a18e69f724c8ef689db7411cd926119e058994cbd548041564  review/code/rv_common.py
     2374  6572b43b88c8ebafccd80bf9c654c4d4635aa84f7dae60bfec19301021095111  review/code/rv_endtoend.py
     1479  8a0f3bfba7fb962e42098ebca30fe8435aedbc1fbeb2255b34dafbfc645dad0f  review/code/rv_exceptional.py
     4668  440519a4bbece61c1d1ea8e61e75af0b15e60b2289934af20dda37991c7ad7dc  review/code/rv_families.py
     1419  5213f0ab9b58a0f2d78b58dc92baa73f231ee2e61c7fc234f2d3b5ebc2c0eb67  review/code/rv_hard13.py
     9686  8fd131210ac7e52af63318770b18378a7a2e23061646fcb284a6fefb4a9e5cf3  review/code/rv_region.py
     6609  5a9c857eab7d0817ee74e4e3deac88f4d06a868eb14ca7eaf85432d618d8a1f5  review/code/rv_rows.py
     6753  85fc46c6fa56cda7d39cb62601a437ff716a9f73b0483c83076bfb9c8a043306  review/code/rv_spectrum.py
      289  b47b67574be902336c4e231ad65e9b0ab4dc3f0c28d8d20ac57ba025005c71cd  review/logs/rv_certify_region.log
      263  cb2f7962985ce225f745aab7372e4c9985f8ee37d42bd94316b63a449ef36880  review/logs/rv_certify_upto30.log
      272  6cc47cee10ab49986381dce5cd432d8629b586d68745dd171ad0df85995a0eb6  review/logs/rv_endtoend_23-26.log
      271  3995e732feb582beb1ce95034464f1650775e63bd1b985302b6d1eca62f35d25  review/logs/rv_endtoend_3-22.log
      251  d9c04d8cf149c0f642b6e7be6e1ab49930c59a7f59e48e26faa3d382b1fd8cc5  review/logs/rv_endtoend_big34.log
      583  3d060f7f1014f707bd5ccefbb6d64b4bd14061e401a14fe0538e93002b55e7a9  review/logs/rv_exceptional.log
      676  f45f95d515503863d0c279c969a9f80859eb4448186b74335e2a3572ca197994  review/logs/rv_families.log
     3422  0a3eca2edad1eba5610ad7db12682300ed9c799c22a83bf2a573ee7b014d87a7  review/logs/rv_hard13.log
       52  79257fe2a968914f0bf5ace1fbf757cdbe71a98f79bae8ce4397cf07954496bc  review/logs/rv_realizability.log
      469  a228150b6c0857cc764b6603bf80d98906920a05acb93e1dfe088d4acc3db96a  review/logs/rv_region.log
   399349  8b52ccd885baccef6751828e8b967868366ee5311462ec3be96692a64fa8df96  review/logs/rv_region_list.txt
     1793  716681bd7c4e561c1d11483c46305e985c7896f567882bc8e114eed731509d5b  review/logs/rv_rows_b13-40.log
     5275  795b4f1a94d2653983a2c4830ce33591f2b75fd4d9e3a834327f232230361142  review/logs/rv_rows_b2-12.log
    24570  879c16c8ccf36243e9cb46025c35dc9ba3099c1aa2e0b56c44c3143609a213ae  review/logs/rv_spectrum_seed7_400.log
```

The folder holds 211 files (920769 bytes), plus this file. By folder: `code/` 16 files, 59406 bytes; `logs/` 48 files, 70909 bytes; `diam4/code/` 35 files, 84989 bytes; `diam4/logs/` 18 files, 39479 bytes; `diam4/s3/` 52 files, 48553 bytes; `review/code/` 9 files, 42949 bytes; `review/logs/` 14 files, 437535 bytes; `lean/` 9 files, 14298 bytes; `checks-addition/` 6 files, 9354 bytes; the top level and `review/` itself (`CONTRACT.md`, `PROOF-working-note.md`, `review/REVIEW-diam4.md`, `review/SHA256SUMS`) 4 files, 113297 bytes.

The paper (`papers/switching-diam4/`):

```
    bytes  sha256                                                            path
   559253  ca7fbc78fef698e8feb95a6b24c20c0e1684168d008e41a3f8b21b5a660763de  papers/switching-diam4/note.pdf
    60552  20e6afc809b6af646b835423b9c4e17816c74c920b8510b6ac8e15271002aaa1  papers/switching-diam4/note.tex
```

## Note by the lead agent (2026-09-27)

The Lean replay and build logs in this folder come from the research agent's runs. They predate a change to a single docstring line of `lean/Research/SwitchingThmH.lean`: its comment on the refined count was reworded, and no Lean code changed. The released file (SHA-256 f4796e4f…) is covered by the repository-level clean replay `logs/clean-replay-v1.7.0-*`, whose source manifest `logs/lean-sources-sha256.txt` lists this hash.


Final paper files (after the second review and the final novelty check, 2026-09-27): `papers/switching-diam4/note.tex` SHA-256 c724709599100771ec5044b25fba469e91d92345847799dcd9ed0cdd6a704819, `note.pdf` SHA-256 6ff4f4a056f52ecf1809d48b35f7e6a23ebcb938a0ab061a9dffd6d3890a3f88. Earlier hashes listed above refer to superseded drafts.

Final paper files for version 1.7.0 (the line `The author has read the paper.` added in the disclosure, PDF rebuilt, still 15 pages; nothing else changed): `papers/switching-diam4/note.tex` SHA-256 24c68a9c99a0c3b53db6a7c7b7182262ac6c33851abdda8ede5870fab8033cd8, `note.pdf` SHA-256 103c671e3ad534aa1fe88f3ec29d818537484a37f4f0b352eeb3e1dee6f6f639. The hashes in the previous paragraph refer to the version before that line was added.

## Version 2 of the paper (release v1.11.0)

Version 2 of Paper 8 replaces the paper files: `papers/switching-diam4/note.tex` SHA-256 810f26d18f05bcbfca7951b31de676524af5c9f6b9860898e440f48dc7bcef35, `note.pdf` SHA-256 6b003a00644ff96ac729c28eaf9898e319c942572e668226e5a9939599c91b87 (17 pages). Every result of version 2 is formally verified in Lean (`lean/Research/Backfill/Paper8/`; acceptance receipt in `certificates/switching/lean-package-v2/`). Version 2 deletes the computational claims of version 1 that are not formally verified, among them the counts listed in item 7 above for the trees with up to 24 vertices, for the multisets with up to 44 vertices, the census of non-even pairs and the values of Remark 8.1. The programs and logs in this folder are those of version 1; they remain in the repository as independent cross-checks, and version 2 does not rely on them.

## Codex disclosure update, 2026-09-29T21:28:34Z

Only the version 2 disclosure was updated to record Codex's source and evidence review after Claude's usage credits ran out. The mathematical text and all Lean sources are unchanged. The updated source passed the desktop editor's compiler and three pdflatex runs; the final 17-page PDF was inspected on the affected pages. The old compilation adapter selected TeX Live 2022 and failed on a missing xurl package; export then succeeded with the already installed TeX Live 2026. No new package was installed.

- `papers/switching-diam4/note.tex`: `cd399b6b2344d297e2be6d42715f889a54d4bad374dc848eadee31319f154650`
- `papers/switching-diam4/note.pdf`: `376072720e813cbb0ada3d9e20c9a6e5910a4de72049f77403f879b8774c2a54`
