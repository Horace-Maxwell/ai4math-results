# Packaging notes: certificates for the RM(7,14) weights paper

Staged on 2026-09-26 (UTC) for release v1.4.0 by an AI agent (Claude Code) doing the release packaging.

- Paper: `papers/rm714-weights/note.tex` and `note.pdf` (11 pages), *The weight spectrum of the Reed–Muller code RM(7,14) up to four weights*.
- Lean: `lean/Research/RM714Weights.lean` and `lean/Research/RM714WeightsAudit.lean`. They are not in this folder. Their SHA-256 values (58232392…, f2b2c62c…) equal the input hashes in `logs/lean_clean_replay.log`.
- Everything in this folder comes from the project's working folders:
  - `code/`, `data/` and `logs/` come from `<project>/work/round6/rm714/`;
  - `code/closure_replay.c` and `logs/closure_replay.log` come from `<project>/outputs/RM714-weights/certificates-addition/`;
  - `code/RM714Timing.lean` comes from `<project>/work/round6/rm714/lean/`. It is a timing probe, not part of the formal proof.

## What backs what

| Claim (paper) | Programs (`code/`) | Data (`data/`) | Logs (`logs/`) |
|---|---|---|---|
| Theorems A and B: witnesses, degrees and weights (§3, §6.1) | `verify_witnesses.c` + `rmcore.h` (Möbius transform); `verify_bitset.py` + `verify_all_py.py` (big-integer tables) | `rm714_all_witnesses.json` (SHA-256 784bca3b…); `rm714_all_witnesses.txt` (the same table in the input format of `verify_witnesses.c`); `M_status.json` (the Table 1 witnesses and the status of the 22 weights of M) | `verify_all_witnesses_C.log`, `verify_all_witnesses_py.log` |
| A second set of witnesses (up to 4954 monomials) for the 16 weights of Theorem A other than 16030 (working note §11, item 3) | the same two checkers | `scout_rm714_witnesses.json`, `scout_witnesses.txt` | `verify_scout_witnesses_C.log`, `verify_scout_witnesses_py.log` |
| Lemma 4.1 and Propositions C′, D, F (§6.1) | `cert_arith.py`, `cert_arith.c` | – | `cert_arith_py.log`, `cert_arith_c.log`, `cert_arith_diff.log` |
| Proposition E (§6.1) | `venn_enum.c`, `venn_enum_fast.c`, `venn_enum_indep.c` | `venn_indep/k*.txt` (outputs of `venn_enum_indep.c`) | `venn_enum_k1to4.log`, `venn_enum_k5.log`, `venn_enum_indep.log` |
| Searches and Table 2 (§6.2; heuristic) | `closure_search.c` (three builds: default, `-DGEN_FLATS`, `-DZHIST`), `check_closure_hits.py`, `closure_replay.c` | – | `closure_search_rm714_seed11`–`15.log`, `closure_search_flats_rm714_seed41`–`45.log`, `closure_zhist_rm714_seed51.log`, `closure_search_rm612_calibration_seed21.log`, `closure_zhist_rm612_seed52.log`, `closure_replay.log`, `background_jobs.txt` |
| Earlier searches (§6.2; heuristic) | `sparsefind.c`, `flatsearch.c` (+ `rmcore.h`). Working note §9.2 only: `sparsefind12.c` (+ `rmcore12.h`), `lightsearch.c`, `supportwalk.c`, `cosetsearch.c` | `sparse_table_s7.txt`, `sparse_table_rm612.txt` (tables output by the sampler) | `flatsearch_A_101.log`, `flatsearch_B_202.log`, `sparsefind12.err`, `sparsefind12_calibration.log`, `lightsearch_303.log`, `supportwalk_404.log`, `cosetsearch_505.log` |
| Formal verification (§7) | `lean/Research/` of this repository | – | `lake_build_RM714.log`, `leanchecker_RM714.log`, `lean_clean_replay.log` (the clean rebuild of §7, 13:49–13:55 UTC), `forbidden_grep_session2.log`; timing probe: `code/RM714Timing.lean` and `lean_timing_354.log` |
| Remark on 8174–8210 (a remark only) | inline Python (not kept) | – | `closed_form_checks.log` |
| Code hashes at run time | – | – | `sha256_code_session2.txt`, `sha256_artifacts.txt` |

The paper names these programs and data files, and all of them are here:

- `verify_witnesses.c`, `verify_bitset.py` and `verify_all_py.py`;
- `rm714_all_witnesses.json`;
- `cert_arith.py` and `cert_arith.c`;
- `venn_enum.c`, `venn_enum_fast.c` and `venn_enum_indep.c`;
- `closure_search.c`, `check_closure_hits.py` and `closure_replay.c`;
- `sparsefind.c` and `flatsearch.c`.

The Lean files it names are in `lean/Research/`.

## How to run (from this folder)

Build the C programs anywhere with `cc -O2 -o NAME code/NAME.c`. The headers `rmcore.h` and `rmcore12.h` sit next to the sources. The usage of each program is given in the header comment of its source.

```
python3 code/cert_arith.py > py.out
cc -O2 -o cert_arith code/cert_arith.c && ./cert_arith > c.out
diff py.out c.out                                    # expect no output (38 identical lines)

cc -O2 -o verify_witnesses code/verify_witnesses.c
./verify_witnesses < data/rm714_all_witnesses.txt   # stderr: checked 7901 witnesses, 0 failures
python3 code/verify_all_py.py                        # 7901 witnesses, 0 failures; covers S0 exactly
python3 code/verify_bitset.py data/scout_rm714_witnesses.json

python3 code/check_closure_hits.py 14 7 logs/closure_search_rm714_seed1*.log logs/closure_search_flats_rm714_seed4*.log logs/closure_zhist_rm714_seed51.log
                                                     # 99 printed codewords (18 distinct), 0 failures
python3 code/check_closure_hits.py 12 6 logs/closure_search_rm612_calibration_seed21.log logs/closure_zhist_rm612_seed52.log
                                                     # 36 printed codewords (18 distinct), 0 failures

cc -O2 -o closure_replay code/closure_replay.c
./closure_replay 13 6 312 340 D:11:2137344 D:12:2140416 D:13:2135552 D:14:2136064 D:15:2140416 D:51:437760 \
                 F:41:7865856 F:42:7868928 F:43:7900416 F:44:7865856 F:45:7888640
./closure_replay 11 5 150 180 D:21:1927424 D:52:993792
```

The iteration counts for `closure_replay` are those in the `DONE` lines of the search logs, and the two commands match the two parts of `logs/closure_replay.log`. The run of Proposition E with k = 5 took about 23 minutes on one core with `venn_enum_fast` (`logs/venn_enum_k5.log`). `venn_enum_indep K NPROC ME OUTFILE` splits the work into parts.

## Smoke tests of this package

These were run on 2026-09-26 from 15:33 to 15:39 UTC, from this folder after staging. The tools were Apple clang 21.0.0 and Python 3.12.4 on macOS arm64.

- Each test used one core, and at most two ran at the same time.
- Items 1–5 took a few seconds in total. The longest test was the `closure_replay` run of item 8, at 111 s.
- The binaries were built outside the package, and Python was run with `-B`, so no bytecode was written.

1. **Python arithmetic certificate.** `python3 code/cert_arith.py` exits with 0 and prints 38 lines. They are identical to `logs/cert_arith_py.log`.
2. **C arithmetic certificate.** `cc -O2 -Wall code/cert_arith.c` compiles with no warnings. The program exits with 0 and prints 38 lines. Its output is identical, line by line, to the Python output and to `logs/cert_arith_c.log`. Both outputs have SHA-256 0d7a690b….
3. **Witness weights.** The test used three of the 14 new weights: 354, 8174 and 16030.
   - `verify_witnesses.c` (compiled with `-Wall`, no warnings) on their lines of `data/rm714_all_witnesses.txt`: all three are `OK`. Each has the claimed weight, maximum degree 7, a passing involution check and no repeated monomial. The program reports 0 failures and exits with 0.
   - `verify_bitset.check` on the same entries of `data/rm714_all_witnesses.json` gives the weights 354, 8174 and 16030, each with maximum degree 7.
   - Also checked:
     - `data/rm714_all_witnesses.json` has SHA-256 784bca3b…, as stated in the paper.
     - The `.txt` and `.json` tables are identical: 7901 entries with the same monomials.
     - The witness of 354 in `M_status.json`, the one in Table 1, has weight 354.
4. **Extra: the relativised `code/verify_all_py.py`.** It checks all 7901 witnesses in 0.3 s and finds 0 failures and exact coverage of S0. Its first three output lines are identical to `logs/verify_all_witnesses_py.log`. It gives the same result when started from another directory.
5. **Extra: compile-only check.** All other C sources were compiled with `cc -O2`, 13 builds in all, including the `-DGEN_FLATS` and `-DZHIST` builds of `closure_search.c`. Every build exits with 0 and prints no diagnostics. Apart from `closure_replay` (item 8), these programs were not run.
6. **Extra: full witness runs.**
   - `./verify_witnesses < data/rm714_all_witnesses.txt` gives 7901 `OK` lines and 0 failures, and exits with 0. Its output is identical to `logs/verify_all_witnesses_C.log`, apart from the interleaved line described below.
   - For the scout witnesses, both checkers reproduce `logs/verify_scout_witnesses_C.log` and `logs/verify_scout_witnesses_py.log` exactly: 16 witnesses, 0 failures.
7. **Extra: `check_closure_hits.py` with the two commands above.**
   - RM(7,14): 99 printed codewords (18 distinct), 0 failures.
   - RM(6,12): 36 printed codewords (18 distinct), 0 failures.
8. **Extra: `closure_replay` with the two commands above.** Its output is identical to `logs/closure_replay.log`: lines 3–103 for RM(7,14) and lines 105–124 for RM(6,12). The union line gives 26,956 distinct h of weights 312–340, of which 13,681 have weights 316–332, as in Table 2.

## Changes made during packaging

1. `code/verify_all_py.py`: the absolute project path in `W=` was replaced by the parent folder of the script, `os.path.join(os.path.dirname(os.path.abspath(__file__)), "..")`, and `os` was added to the imports. Nothing else changed. The SHA-256 was 511eefaa… before, as recorded in `logs/sha256_*.txt`, and is f2456be1… after.
2. Four logs had absolute prefixes replaced by `<project>` (the project root) or `<scratchpad>` (a temporary directory):
   - `logs/lean_clean_replay.log`: 1 line;
   - `logs/sha256_code_session2.txt`: 18 lines;
   - `logs/sha256_artifacts.txt`: 14 lines;
   - `logs/verify_all_witnesses_py.log`: 1 line.

   No number and no hash changed. A script confirmed that the digit sequences and the 64-hex hashes are the same before and after.
3. `CONTRACT.md`, line 4: `$P = <absolute path>` became `$P = <project>`.
4. `PROOF.md` was renamed to `PROOF-working-note.md`. Its content is unchanged.

All other files are byte-identical copies, with their timestamps preserved. This was checked with `cmp` against the sources for 73 files, and `PROOF-working-note.md` was also compared with `PROOF.md`.

Apart from `verify_all_py.py`, each source file's SHA-256 matches the most recent entry for it in `logs/sha256_code_session2.txt` or `logs/sha256_artifacts.txt`. `closure_replay.c` matches the hash printed in `logs/closure_replay.log`.

## Not included, and why

- `refs/`: copies of other people's papers, which must not be redistributed.
- `g1/` (65 MB) and `g2/raw/`: raw dumps of the literature searches.
- `querylog.tsv`: the literature query log. Earlier packages in this repository do not ship theirs either.
- `archive/PROOF-session1-0958Z.md`: a superseded version of the working note.
- `code/__pycache__/` and the compiled binaries: `cert_arith`, `closure_search`, `closure_search_flats`, `closure_search_zhist`, `cosetsearch`, `flatsearch`, `lightsearch`, `sparsefind`, `sparsefind12`, `supportwalk`, `venn_enum`, `venn_enum_fast`, `venn_enum_indep` and `verify_witnesses`. Only their sources are shipped.
- `code/lean_clean_replay.sh`: a shell helper that contains machine paths. The replay it ran is described in §10 of the working note, and its output is `logs/lean_clean_replay.log`.
- Three logs:
  - `logs/lean_clean_replay.stdout`, which is empty;
  - `logs/propD_arith_check.log` and `logs/louwang_conj2_m6_check.log`, checks from the first session made with inline code that was not kept. The `cert_arith` logs supersede them.
- `work/round6/rm714/lean/RM714Weights*.lean`: identical to the copies in `lean/Research/` (same SHA-256).
- Size: no file here is near 50 MB. The largest is `data/scout_rm714_witnesses.json`, at 368 KB.

## Notes for readers

- `PROOF-working-note.md` is the working note of the agent that did the research, kept as it was. Where it differs from the paper, the paper is authoritative.
  - §9.1 speaks of about 1.4·10^5 distinct h, 70,266 of them with weights 316–332, and its table gives counts for each weight. These counts add up the samples of all runs. But the runs within each group sampled the same sequence of h, so most h were counted several times. The counts without duplicates are those of the paper's Table 2 and `logs/closure_replay.log`: 26,956 distinct h of weights 312–340, of which 13,681 have weights 316–332.
  - The "99 codewords re-checked" for RM(7,14) (§9.1, §11) are 18 distinct codewords, each printed several times. The RM(6,12) logs print 36 codewords, which are also 18 distinct ones. The paper (§6.2) gives these distinct counts.
  - It refers to files that are not shipped here: `archive/`, `g2/raw/`, `querylog.tsv`, `code/lean_clean_replay.sh` and `lean/`. The Lean sources are in `lean/Research/` of this repository.
- Some logs are identical, as expected:
  - `closure_search_rm714_seed12.log` = `closure_search_rm714_seed15.log`;
  - `closure_search_flats_rm714_seed41.log` = `closure_search_flats_rm714_seed44.log`.

  Each pair had the same iteration count, and consecutive seeds give shifted copies of one random stream (paper §6.2).
- In `logs/verify_all_witnesses_C.log`, lines 7891–7892 look broken: the original capture wrote the program's stderr summary ("checked 7901 witnesses, 0 failures") into the middle of the stdout line for 16096. The file was left as it was.
- The `sparsefind` run on RM(7,14) (249,320,000 samples; working note §4 and §9.2) has no separate log. Its output table (format `w k m1 … mk`) is `data/sparse_table_s7.txt`, and no weight of U occurs in it.
  - Every entry of `rm714_all_witnesses.json` with weight at most 8192, except 0 and 362, is taken from this table verbatim.
  - The entries above 8192 are complements (f + 1). `data/sparse_table_rm612.txt` is the output of the calibration run of `sparsefind12` on RM(6,12).
- The scout witnesses (`data/scout_*`) were produced by an earlier program that is not included. The two checkers here verify them (`logs/verify_scout_witnesses_*.log`).

## File list

This list gives the size in bytes and the SHA-256 of each file. It covers every file in this folder except this one, and the two paper files.

In this folder (`certificates/rm714/`):

```
   bytes  sha256                                                            path
    9455  d7f70cb48949e56aa61615bb8071ac1e4451da222d373260dd0d6d7f15d3949c  CONTRACT.md
   40413  a871a2a59a97a2c489fdffbbe25947d4daaf4567cef52fa0d6093112270818fb  PROOF-working-note.md
     456  b033ef3b69f4dccc86a14350a244e756d63d8adf46ed3f30fe0583933b00ff03  code/RM714Timing.lean
    5608  9fcdc373891b069ad8e97782a3b08de2b1b561d9c26dffa6184748ed582e8bb3  code/cert_arith.c
    4523  2f66ab8f7a34445513e986419c2d307020ff76c96644b0ea580194805e35cc84  code/cert_arith.py
    1352  a7c1f402d0e9b70490c31ceccf47b1f3743a26ac92ca862b2c451eb599cae70b  code/check_closure_hits.py
    9494  05114c339d8cdbb5fda02a8d530fd1dfb2556bd7b8d07592f57bdc0264d0f4a8  code/closure_replay.c
   15171  d586036889ad77da8d2d177e0911bfed813dcf0236411d378d2ff3e9bb02d4f0  code/closure_search.c
    4517  4539e81f9b8d42251e7e73f0cc09bba8b9f6c67c791db98562bc66aaf29b633c  code/cosetsearch.c
    5689  c2e0c30407f57d56774c6c6b0f62d4dd5f9a3ffd4f9ce87991a06c12b46a4649  code/flatsearch.c
    4288  fd9364e1eec3b8f58d093752adb00e2e8f496694b86cb2dc7f1ef9bee9ec66f5  code/lightsearch.c
    1338  c62dc61a5405c02942ef21ba6e1cabd7dd08b496acc50fb3d7d628e26d7ccc49  code/rmcore.h
    1338  21125cbafeb50d73b9f0f6475649852e510067c56665299aae41454c10543d8b  code/rmcore12.h
    1740  320d40078d8f1606c1671dace0ce2563b251c0c3c2e3ab0f29d55ac0ae696142  code/sparsefind.c
    1733  73ac8c9747ca650e224c2f51dc528e96f454dcfbe533cf6338f9524e5456dccf  code/sparsefind12.c
    3459  76db4a7e54589bdd0e86cb790eb8f966195cdf8d60708cbebeedeb5f44bb96e4  code/supportwalk.c
    2087  e48a6c8a9079c60eb680f2addaf97775aea2918ba4bc927439db9d19b20df223  code/venn_enum.c
    1746  00bd47ce111994158ac54d0450aab7b66132c2458330e7ee2bdbe8dee6dd99e6  code/venn_enum_fast.c
    3152  ba6cf4be544ae103ddaad8affa633158673988663dd05306e2070a49ab956196  code/venn_enum_indep.c
     826  f2456be19e27ab235cff82cb41f3c430b9302b1ab0c1f155e6dc1d4be0b2282b  code/verify_all_py.py
    1195  d1881fafeb40d22b75e60e4b481299fbb3e5f4f3a44c5f6f1560e0441df1cd18  code/verify_bitset.py
    1265  369af3bdb5caf2e8609e4b7a4c214a9d7da52245f93d2acb174abcbd38139686  code/verify_witnesses.c
    5531  559a2b5f6cab5717eb5315ca733f1abf42541d55459c3602dc22c4062a2f65d7  data/M_status.json
  299625  784bca3ba1e3012078d29156811132a726641d51f75e3d04c125f2efa085939b  data/rm714_all_witnesses.json
  236964  2c162b31e21f5781d7d29ff5ade62cf97ed6f22cb78f8a29107d23eecfba431a  data/rm714_all_witnesses.txt
  367823  5ca1e1a8ebdc536787a44d2e4429492a96ad7425e1fe40e44901ce3a4078f810  data/scout_rm714_witnesses.json
  308204  39437b5e861245b85b1015e7172ca001217aa5103f0c81cc547716142b66a3a7  data/scout_witnesses.txt
   37731  0faef6d01bb5647ea9ab3bd5e3779bcbb19f396121184bbf4275e0c5b09d1b96  data/sparse_table_rm612.txt
  188082  f2aa5caf736d72102a81f7934c533c1ef861b2e0eb47f7f07939c367635f45f9  data/sparse_table_s7.txt
      46  7b75328ebc67f215a306993598b8b59adc3029a08931e2e4418677c5e4634729  data/venn_indep/k1.txt
     362  16ee6e694de73f72d97f1732358fb48faadf81658744d3d5eb02a7716c485009  data/venn_indep/k2.txt
    3093  e1671508de3ae478512bc321c5f949de1126aa5c5643d7de2625371012042e4c  data/venn_indep/k3.txt
   13266  1b6e9c70e1a574c9d042d216298a2656b46a33cf13aad75167a7092a07edbcfc  data/venn_indep/k4.txt
   13254  92ffc1d696c42f8f2e507b76287bf0aed3c38fd720b3314a4f9e700fa05d2791  data/venn_indep/k4p0.txt
   13260  219d8ff37ef7bb889b8fdb99a7b5fe134cafe5582ea3af2c869553c43fda224f  data/venn_indep/k4p1.txt
   13266  ce81b93c37d539e22d376cc9d9fd567e3bc116f860a0ab979a17792ee7c465a3  data/venn_indep/k4p2.txt
   29734  e073db37b7de01b839ce0ba7d5b8b7830141861e38af0632a453f15d7ecbfe78  data/venn_indep/k5p0.txt
   29734  7eaacf08bb8847262b6a58744b2b3b6b1722cf2f2b1775e0eb0d49eb964f4895  data/venn_indep/k5p1.txt
   29734  a71791a386e229526bb54644dd70eef776e9fc312940882f0bb5855f77819403  data/venn_indep/k5p2.txt
   29734  d3d7bf547dac3a9053180dde522cc8d09c76afceb7846531723f2d965b749862  data/venn_indep/k5p3.txt
    1691  c6d04c6df140e16f8dcd98fbe4d7bd7e04d415f7f1562d00978d88d56a226504  logs/background_jobs.txt
    2015  0d7a690bd079fde837f192f1de0ef78faf1e98d436ba2642de5b35e30874ca9c  logs/cert_arith_c.log
     120  4e799d204240ae32005d88e33d07e3c5a432c17ffdd82214399f34c3315e464f  logs/cert_arith_diff.log
    2015  0d7a690bd079fde837f192f1de0ef78faf1e98d436ba2642de5b35e30874ca9c  logs/cert_arith_py.log
     367  dfaa08aa070cef96dec62d525f2b1c3b4b0947b66d11001d3f0dea4476b4f171  logs/closed_form_checks.log
   11640  0d2b297e26d81e7bfc291a0bf7c7f2eec63e6c251c8907d2debf30c38bdd9dff  logs/closure_replay.log
   40933  0b2f413473451780142af19e7a69c99454630197d935d0e5dc86eab8142070a0  logs/closure_search_flats_rm714_seed41.log
   40933  faa5d8d4dddfb81547f0a11e347b982e80247b15fb7af708db8acdf162a0bcc4  logs/closure_search_flats_rm714_seed42.log
   40933  02dedfc0a500415a008afdd0366b1c4df4a0cac6c3be0daf6f0c120e2172c77c  logs/closure_search_flats_rm714_seed43.log
   40933  0b2f413473451780142af19e7a69c99454630197d935d0e5dc86eab8142070a0  logs/closure_search_flats_rm714_seed44.log
   40933  26f2c4768844d4556d0b2d90c06453572aa29b8dd6572ba8effce90beafe6495  logs/closure_search_flats_rm714_seed45.log
   22189  5dc526138aad80cc525536db040b5576b9be5129eedba06d346fb2530d0658e1  logs/closure_search_rm612_calibration_seed21.log
   40938  5ce69185830cde968aede42faacf231f8d814b819153f141e8ef9538b5e541ba  logs/closure_search_rm714_seed11.log
   40938  e4de0cc4f495755ed4f9439dec2a319596ee4f39d7867957085b9392a9974ef2  logs/closure_search_rm714_seed12.log
   40938  dd037e0c53231288550a56b4aec8662c6f7d8aab3a413990ca6332f7c833d70a  logs/closure_search_rm714_seed13.log
   40938  b41316afc1ee0e990312b72eca238640207a85ef88187629fec12082db15cfba  logs/closure_search_rm714_seed14.log
   40938  e4de0cc4f495755ed4f9439dec2a319596ee4f39d7867957085b9392a9974ef2  logs/closure_search_rm714_seed15.log
   22609  7ede9905811f8d59ee16bb4251328dba1b8dba608e56b53375da8d1e79daaab2  logs/closure_zhist_rm612_seed52.log
   41336  4b42a3896000c00ed3eca17c2ead90dc06a47f39699bb6e9c705aa7f41a8a6b5  logs/closure_zhist_rm714_seed51.log
    2111  bc809ceb9c28603d5cfe9a03ef7f68d7d1e3215ba53e8b7cae4b111938615cef  logs/cosetsearch_505.log
    1784  2c98a67b76f8669b9715ac16db7233387abe09c68bf51d1786dd5f9f639394b6  logs/flatsearch_A_101.log
    2071  461260b3b8e407bc72c3ae15cf29a612c6269777f7ee610d612a03aa315c9dc6  logs/flatsearch_B_202.log
     164  e665601af623138e040b26be73581ab4e0442310a48f9cd1ee56f5bd8a6c903a  logs/forbidden_grep_session2.log
    2733  20eb6284c5452e205b070ebb7b72413f9e8ccac12e4e62ab8fefabf7986d7753  logs/lake_build_RM714.log
    3880  b409799e1910c25c97a8e3f069a68990bdf04fa34ee1b147d9fea6b1a00e8521  logs/lean_clean_replay.log
     930  e35b7e2a528ea21efa820596ba218574bd06af258a35a7da146d5c3f2fcc9543  logs/lean_timing_354.log
      72  dcfa96ec7928b135d3ce78a7b770d2ac711d62cc385816b398618cf8258755eb  logs/leanchecker_RM714.log
     588  8eb5c479786dbf8c6bbb7bb6a2f049cf53e1a66a9c3124901c56d6218aef9159  logs/lightsearch_303.log
    1627  89ab0d0df73ae723fd9b61ba9e09804c3b6b5d18db482f3ca8a72805148885b5  logs/sha256_artifacts.txt
    2380  be425275270772c213d16215ff212e319490131e70f4e3281f01f73e67190a21  logs/sha256_code_session2.txt
      44  f384be2c0abef9b5da8814bafdb6d91feff0b96c4f1b852261c705ea69796d83  logs/sparsefind12.err
     183  5c5f051e9d159f766c806f498933b0c16ec6d9ee5def9095ac717a5dc36fb805  logs/sparsefind12_calibration.log
    1313  863e21e0ae25889e35ea0d9dbd5137e713cab97e7cca4c485f218912048b6ba1  logs/supportwalk_404.log
    1073  2d3289e59870190265029f2ae60d91dfa546ab63b9f3cad0a651be67935f9a6c  logs/venn_enum_indep.log
    1308  d16410ed1fe57d7f11d2c492afc1d04d58fb78f4e68175a5b9933af5cd0a5d4b  logs/venn_enum_k1to4.log
     337  9d40ff74eee853788aec220f711c7a1e0368fd70a99d032113260b3e901e3481  logs/venn_enum_k5.log
  360962  35e8a281992aad8d1ec1db23be177ac3555c81bb586c67521ae5003ae821750f  logs/verify_all_witnesses_C.log
     283  a1c763fc8c1fad66da445e6c613f8072d464a74b9a08eb7454ad108a6262daef  logs/verify_all_witnesses_py.log
     757  530a76988b45ea8b6e213feba4c9dca136bb951dbe10aa040e876a1f46bbfa41  logs/verify_scout_witnesses_C.log
     465  a80a82c60b465e1f33e22339ba1b8a863320b3ef6a762787dc8f9724e460d917  logs/verify_scout_witnesses_py.log
```

The folder holds 80 files (2638690 bytes), plus this file. By folder:

- `code/`: 20 files, 70977 bytes;
- `data/`: 18 files, 1619443 bytes;
- `logs/`: 40 files, 898402 bytes;
- the top level: `CONTRACT.md` and `PROOF-working-note.md`.

The paper (`papers/rm714-weights/`):

```
   bytes  sha256                                                            path
  628603  2ffcdb59572de8829c8b373e0a962ade4cdc218220e8928f9efc29e39f0bcbbb  papers/rm714-weights/note.pdf
   42009  44b95cb4e745ad62702f1e583751ee11ecf090852fe1ef8cd5a46e7d12d47648  papers/rm714-weights/note.tex
```

Final paper files of version 1.4.0: `papers/rm714-weights/note.tex` SHA-256 507bed354e1a387e00e759f6512cc49554ac59e18595e7a19c7b8a58b6326705, `note.pdf` SHA-256 4a9588b87d2e2102dbe173ebcf2ba85bb8a70190d4eae676e9d75ff815a079d6 (11 pages). The two paper hashes in the table above are those of an earlier draft, recorded when this folder was staged; the paper was edited after that, last by adding the author's sentence to the disclosure. This paragraph was added in version 1.7.0.
