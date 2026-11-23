# Lean package of Paper 30

The files of `lean/Research/TaskV/FEI/` (Paper 30: two classes of Boolean functions with non-flat Fourier spectra
for which the Fourier entropy–influence conjecture of Friedgut and Kalai holds with an explicit constant, and the
signed product of the nonzero Fourier coefficients; Potapov, arXiv:2609.21563v1, proved the case of equal nonzero
magnitudes), 8 files in one package for both statement files: the statement files `Challenge.lean` and
`UpperChallenge.lean`, the proof modules `Walsh.lean`, `Determinant.lean`, `Analysis.lean`, `Layer.lean` and
`UpperAnalysis.lean`, and the check file `Check.lean`.

- `package-manifest.json`: the SHA-256 and the imports of the 8 modules, the Lean toolchain, the Mathlib commit, the
  entry point imported by `lean/Research.lean` (`Research.TaskV.FEI.Check`), the six theorems it checks
  (`Fei.check_signedProduct`, `Fei.check_supportEntropy`, `Fei.check_lowerMassFEI`, `Fei.check_boundedRatioFEI`,
  `Fei.check_upperProduct` and `Fei.check_comparableMassFEI`), and the two statement files with their SHA-256 and
  freeze times. For each file it also gives the SHA-256 of the file Codex accepted. The files in the repository have
  module names under `Research.TaskV.FEI`, keep the namespace `Fei` (so the checked names are unchanged), and differ
  from the accepted files only in their `import` lines; `Challenge.lean`, the only file that imports only Mathlib, is
  byte for byte the accepted and frozen one. `UpperChallenge.lean` imports `Challenge.lean`, so its repository copy
  differs from its frozen version (SHA-256 `0731c4d4…03ab`) only in that `import` line (repository SHA-256
  `60c4e633…dd80`). Codex's package also had a root module `Fei` (`formal/Fei.lean`, the single line
  `import Fei.Check`); it is in the archive below but not in the repository.
- Statement files, written by Codex agents: `Challenge.lean` (SHA-256 `b277a582…53c6`; the cube as finite sets of
  coordinates, `value`, `character`, `coeff`, `support`, `mass`, `entropy`, `influence`, `weightSum`,
  `nonemptyCount`, and the targets `SignedProduct`, `SupportEntropy`, `LowerMassFEI` and `BoundedRatioFEI`) and
  `UpperChallenge.lean` (frozen SHA-256 `0731c4d4…03ab`; the targets `UpperProduct` and `ComparableMassFEI`, using
  the definitions of `Challenge.lean`). Each was compiled without diagnostics (03:58:30–03:58:38 and
  04:02:10–04:02:15 UTC on 21 November 2026, `development/20261121T035828Z-Challenge-56022` and
  `development/20261121T040040Z-UpperChallenge-88975`), compared with the written proof by a Codex agent that had
  not written the statement or the proof (`review/STATEMENT.md`, APPROVE_STATEMENT at 03:58:15 UTC, after it had
  flagged an ambiguous natural-number expression in an earlier draft of `LowerMassFEI`;
  `review/UPPER-STATEMENT.md`, APPROVE_STATEMENT at 04:00:58 UTC), and frozen by recording its SHA-256:
  `Challenge.lean` at 03:58:46 UTC (`review/FROZEN.json`) and `UpperChallenge.lean` at 04:02:30 UTC
  (`review/FROZEN-UPPER.json`, which also records the SHA-256 of `review/FROZEN.json`). According to the development
  receipts, no proof file was compiled before 03:58:46 UTC (the earliest proof compilation started at 04:01:22 UTC);
  `Walsh.lean` and `Analysis.lean` were compiled at 04:01 UTC, after the approval of `UpperChallenge.lean`
  but before its freeze. The examples and remarks of Section 5 of the paper (the address function, the AND
  function, the selector examples), the identity between the spectral and the flip form of the total influence, and
  the general conjecture are not stated in these files.
- `Check.lean` does not have the form `theorem check_X : Challenge.X := Proof.X`: there is no `Proof` module. Each
  of its six theorems has a frozen proposition as its type and composes proof lemmas in its body:
  `check_upperProduct : UpperProduct := upperProduct_of (fun _ => tail_integral)`;
  `check_signedProduct : SignedProduct := signedProduct_of_upper check_upperProduct`;
  `check_supportEntropy : SupportEntropy := supportEntropy_of check_signedProduct (fun _ => parseval)`;
  `check_lowerMassFEI : LowerMassFEI := lowerMassFEI_of check_supportEntropy (fun _ => parseval)`;
  `check_boundedRatioFEI : BoundedRatioFEI := boundedRatioFEI_of check_lowerMassFEI (fun _ => parseval)`; and
  `check_comparableMassFEI : ComparableMassFEI := comparableMassFEI_core (fun _ => upper_layer_sum) (fun _ => parseval)
  (fun n f V hs hu => upper_log f V hs (check_upperProduct n f V hs hu))`. The file also has three `example` lines
  that evaluate `character` and `coeff` on tiny cases and six `#print axioms` commands. Since every module is in the
  namespace `Fei` and imports the statement files, a proof module cannot redeclare a frozen name; the final reviewer
  confirmed with an audit file of its own that `example : Fei.X := Fei.check_X` compiles for all six.
- `codex-acceptance-logs.tar.gz`: Codex's acceptance run on the author's Mac with Lean 4.34.1 and the pinned
  Mathlib, which was taken from a prebuilt cache and not rebuilt, on 21 November 2026
  (`acceptance/2026-11-21T050526Z`, by `validate.py`, whose SHA-256 `f7a6a0c1…`, recorded in `ROOT-AUDIT.json`, is
  that of the copy in the archive). In each of two new empty directories, one after the other (05:05:26–05:08:38 and
  05:08:38–05:11:43 UTC), with the frozen Lake configuration, it ran 23 commands: the version probe, the Lean path
  and a check that the pinned Mathlib was present without building it; every one of the 9 modules (the 8 files and
  the root module `Fei`) built with `lake --old --no-cache --wfail build +M:olean` (warnings fail); one build of the
  whole package with `lake --old --no-cache --wfail build`; every module replayed with `lake env leanchecker M`; and
  the axioms printed with `lake env lean -j1 -DwarningAsError=true Fei/Check.lean`. All 46 commands ended with exit
  code 0; the 18 `leanchecker` logs are empty; the build logs contain only Lake's progress and completion lines and
  the axiom lines; the `.olean` files have the same SHA-256 in the two directories, and the axiom lists agree: all
  six check theorems depend exactly on `propext`, `Classical.choice` and `Quot.sound`. The largest memory use of a
  single command was 6.0 GB (5,997,772,800 bytes). The archive also keeps an attempt started ten seconds earlier
  (`acceptance/2026-11-21T050516Z`, 05:05:16 UTC): its version probe ended with exit code 1 because the timing tool
  was not allowed to read a system clock setting, and no module was built. The archive further holds the
  records of the accepted run (`PASS.json`, `ROOT-AUDIT.json`, `sources.json`, `banned.json`, `toolchain.json`, the
  `result.json` of each directory and all its logs), the freeze records and the statement reviews named above, the
  reviews of the written proofs by Codex agents that had not written them (`review/WRITTEN.md`, APPROVE_WRITTEN at
  03:57:25 UTC; `review/UPPER-WRITTEN.md`, APPROVE_WRITTEN at 04:00:58 UTC) and the reviewer's exact check of all
  functions with `n ≤ 3` (`review/verify_upper.py`, `review/verify_upper.json`), the development compilation
  receipts (`development/`, with `development/serial-0503/development-verified.json`, the record of the compilations
  of 05:03–05:05 UTC), the frozen Lake configuration and the root module (`formal/lakefile.toml`,
  `formal/lake-manifest.json`, `formal/lean-toolchain`, `formal/Fei.lean`), Codex's list of the frozen statements
  (`STATEMENTS.md`) and handoff (`FINAL-HANDOFF.md`), the final review (`FINAL-CLAUDE-REVIEW-01.md`), Codex's
  record of its receipt (`FINAL-RECEIPT.json`) and its response to the review's minor remarks (`FINAL-ADDENDUM.md`),
  and the task description `task-CONTINUE-FEI-BRAUER-MOORE.md` (the
  continuation on this problem and two others). It does not hold the written proofs. The brief of the search for problems is not included; the requests of the author that it quotes are given in the repository README. `<workspace>` replaces the
  local project directory and `<claude-scratch>` the reviewers' scratch directory; nothing else is changed. The
  build directories themselves are not included.
- `receipt.json` and `repository-recheck-logs.tar.gz`: the 8 repository files compiled with `lean` and replayed with
  `leanchecker` again, module by module, in two new empty directories on the author's Mac (22 November 2026,
  21:36–21:37 and 21:37–21:39 UTC): all 8 compiled and passed `leanchecker` in each directory, with no warning and no
  error, identical `.olean` files, and the six axiom lists of the check theorems, each exactly `propext`,
  `Classical.choice` and `Quot.sound`. The archive holds the logs, the recheck script (`mac_compile_generic.py`), the
  script that moved the files into the repository (`integrate_generic.py`) and its record (`fei-integration.json`).
- The whole project, with these files, was rebuilt for version 1.26.0 (`logs/clean-replay-v1.26.0-receipt.json`).

The statement files, the proofs and the acceptance script were written by OpenAI Codex (model GPT-6.2-Astra). The
final review was done by a Claude Code agent (model Claude Opus 5.5) that had written none of the files (21 November
2026, from 17:03:50 UTC); it compiled the 9 modules again with plain `lean` in a new directory, together with an audit
file of its own, and replayed every module with `leanchecker` (all with exit code 0, no warnings, empty output); its
decision was APPROVE_FORMAL, with no blocking or major remarks and six minor remarks on the written account and the
form of `Check.lean`, which Codex answered in `FINAL-ADDENDUM.md`. Claude Code moved the files into the repository,
changed their `import` lines and ran the recheck above. The package is not checked with comparator or nanoda. No
human mathematician has read the proofs.
