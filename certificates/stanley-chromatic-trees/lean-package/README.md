# Lean package of Paper 32

The files of `lean/Research/TaskV/Stanley/` (Paper 32: two sufficient conditions, the anchor family of Theorem A and
the peeling family of Theorem B, under which a finite tree is determined up to isomorphism by its chromatic symmetric
function among all finite trees; partial results on Stanley's tree isomorphism conjecture, which remains open), 38
files: the statement files `ChallengeA.lean` and `ChallengePeel.lean`, 34 proof modules and the check files
`CheckAnchor.lean` and `CheckPeel.lean`. They are the union of the source files of two acceptance runs of Codex, one
for each theorem; the import closure of Theorem A has 26 of the files, that of Theorem B 30, and 18 are shared.

- `package-manifest.json`: the SHA-256 and the imports of the 38 modules, the Lean toolchain, the Mathlib commit, the
  two entry points imported by `lean/Research.lean` (`Research.TaskV.Stanley.CheckAnchor` and
  `Research.TaskV.Stanley.CheckPeel`), the two theorems they check (`StanleyContinuation.check_anchorReconstruction`
  and `StanleyContinuation.check_peelingReconstruction`) with their axioms, and the two statement files with their
  SHA-256 and freeze times. For each file it also gives the SHA-256 of the file Codex accepted. The files in the
  repository have module names under `Research.TaskV.Stanley`, keep the namespace `StanleyContinuation` (so the checked
  names are unchanged), and differ from the accepted files only in their `import` lines; `ChallengeA.lean` and
  `Isolation.lean`, which import only Mathlib, are byte for byte the accepted files (for these two the manifest field
  `differs_from_codex_source_only_in_import_lines` is `false` because they do not differ at all). `ChallengePeel.lean`
  imports `ChallengeA.lean`, so its repository copy differs from its frozen version (SHA-256 `dcc0d30a…c8a3`) only in
  that `import` line (repository SHA-256 `5f91fa54…c9d7`). Codex's packages also had a root module `Stanley`
  (`Stanley.lean`, which imports the check file; it differs between the two runs and is in the archive below, but not
  in the repository) and modules of a third route (`ChallengeHub.lean` and the `Hub*` files), whose Lean proof was not
  completed; these are neither in the repository nor in the acceptance runs below.
- Statement files, written by Codex agents: `ChallengeA.lean` (SHA-256 `683c4463…6591`; `colorCoefficient` (the number
  of proper colourings with prescribed numbers of vertices of each colour), `SameCSF`, `neighbors`, `core`,
  `coreWeight`, `DecodableLeafAnchors`, and the target `AnchorReconstruction`) and `ChallengePeel.lean` (frozen SHA-256
  `dcc0d30a…c8a3`; `untaggedCoreLeaf`, `PeelingWeights` and the target `PeelingReconstruction`, using the definitions
  of `ChallengeA.lean`). On 21 November 2026 the written proofs (`positive-a/ANCHOR-SPLITS.md` and
  `positive-a/LEAF-PEELING.md`) were approved by Codex agents that had not derived them (`positive-b/REVIEW-A.md` at
  03:47:13 UTC and `positive-b/REVIEW-PEEL.md` at 03:49:18 UTC), and the statement files were compared with them by
  Codex agents that had not written them (`positive-b/REVIEW-CHALLENGEA.md`, APPROVE_STATEMENT_A at 03:47:45 UTC;
  `positive-b/REVIEW-CHALLENGEPEEL.md`, APPROVE_STATEMENT_PEEL at 03:51:20 UTC; the times are those written in the
  files). Each was compiled without diagnostics (`formal/runs/20261121T034826Z-45008`, 03:53:27–03:53:30 UTC, and
  `formal/runs/20261121T035338Z-55599`, 03:53:38–03:53:47 UTC; the directory names do not match these start times)
  and frozen by recording its SHA-256 together with those of the written proof, the two reviews and the compilation
  receipt: `ChallengeA.lean` at 03:53:48 UTC (`formal/FREEZE-A.json`) and `ChallengePeel.lean` at 03:53:59 UTC
  (`formal/FREEZE-Peel.json`). According to the file times, all proof files were created after the freezes (the earliest, `StarBasics.lean`, at 03:54:26 UTC), except `ProfileDefs.lean`, an 18-line file of two definitions (counts of ordered
  partitions into connected blocks), which was created at 03:48:33 UTC and not changed afterwards; the statement files
  do not import it. The statement files were not changed after the freezes. The examples and estimates of Section 5 of
  the paper (the bounds on the number of leaves of the core, the constructions of the two families, the small members
  and the incomparability examples) and the general question are not stated in these files.
- `codex-acceptance-logs.tar.gz`: Codex's two acceptance runs on the author's Mac with Lean 4.34.1 and the pinned
  Mathlib, which was taken from a shared prebuilt cache and not rebuilt, on 27 November 2026, each by its own
  `verify.py`, `serial.sh` and `seal.py`, whose SHA-256 are recorded in the run's `PAIR-PASS.json`:
  - Theorem A (`formal/acceptance/anchor-20261127T030127Z`): in each of two new empty directories, one after the other
    (03:01:56–03:09:56 and 03:09:56–03:17:37 UTC), 57 commands: a check that the pinned Mathlib modules were present
    without building them (`lake --no-cache --no-build --wfail build`); every one of the 27 modules (the 26 files of
    the import closure and the root module `Stanley`) built with `lake --no-cache --wfail build +M` (warnings fail);
    one build of the whole package; every module replayed with `lake env leanchecker M`; and the axioms of 86 public theorems and lemmas printed with `lake env lean -j1 Axioms.lean`. All 114 commands ended with exit code 0; the 54
    `leanchecker` logs are empty; the `.olean` files have the same SHA-256 in the two directories, and the axiom lists
    agree. `ACCEPTED.json` (04:11:35 UTC) records the acceptance after the final review.
  - Theorem B (`formal/acceptance/peel-20261127T051155Z`): the same procedure (05:11:58–05:20:33 and
    05:20:33–05:27:37 UTC), 65 commands per directory for its 31 modules (the 30 files of the import closure and the
    root module `package/Stanley.lean`) and the axioms of 92 public theorems and lemmas; all 130 commands ended with exit
    code 0, the 62 `leanchecker` logs are empty, and the `.olean` files and the axiom lists agree. There is no
    `ACCEPTED.json` for this run; its record is `PAIR-PASS.json` and the final review below.

  In both runs every audited theorem depends only on `propext`, `Classical.choice` and `Quot.sound`, the two check
  theorems on exactly these three, and two lemmas of the run of Theorem B (`bag_card`, `bag_singleton`) only on
  `propext` and `Quot.sound`. The largest memory use of the commands of a directory was about 3.1 GB. No file uses
  `sorry`, `native_decide`, `bv_decide`, `decide`, an `axiom` declaration or `set_option`. The archive also holds the
  records of the two runs (`PAIR-PASS.json`, the `receipt.json` and `release.log` of each directory, the Lake
  configuration, the root module and the axiom file of each directory, and all logs), the frozen statement files, the
  freeze records and the compilation receipts named above, the written proofs and the four reviews named above,
  Codex's statement maps (`formal/ANCHOR-STATEMENT-MAP.md`, `formal/PEEL-STATEMENT-MAP.md`) and handoffs
  (`ANCHOR-FINAL-HANDOFF.md`, `PEEL-FINAL-HANDOFF.md`), the frozen Lake configuration (`formal/lakefile.toml`,
  `formal/lake-manifest.json`, `formal/lean-toolchain`), Codex's checks of the example families
  (`positive-a/check_families.py`, `positive-a/family-receipt.json`, `positive-a/peeling-witness.py`,
  `positive-a/peeling-witness.json`), Codex's notes of its short attempt during the search for problems
  (`MATHEMATICS.md`, which records no result), the two final reviews (`FINAL-CLAUDE-REVIEW-ANCHOR-01.md`,
  `FINAL-CLAUDE-REVIEW-PEEL-01.md`) and the search for prior work on Theorem A (`PRIOR-CLAUDE-ANCHOR-01.md`). The
  development receipts of the earlier rounds are not included; nor is the brief of the search for problems (the
  request of the author that started this work is given in the repository README). `<workspace>` replaces the local
  project directory and `<claude-scratch>` the reviewers' scratch directory; nothing else is changed. The build
  directories themselves are not included.
- `receipt.json` and `repository-recheck-logs.tar.gz`: the 38 repository files compiled with `lean` and replayed with
  `leanchecker` again, module by module, in two new empty directories on the author's Mac (27 November 2026,
  18:11–18:15 and 18:15–18:18 UTC): all 38 compiled and passed `leanchecker` in each directory, with no warning and no
  error, and identical `.olean` files. The check files print no axioms (so the axiom lists in `receipt.json` are
  empty); a separate file, `AxiomsStanley.lean`, which imports both check files, printed exactly `propext`,
  `Classical.choice` and `Quot.sound` for each check theorem against the compiled files of one of the two directories (`axioms-stanley.log`). The
  archive holds the logs, the recheck script (`mac_compile_generic.py`), the script that moved the files into the
  repository (`integrate_generic.py`) and its record (`stanley-integration.json`), the record of the union of the
  source files of the two runs (`stanley-union-receipt.json`), and the axiom file and its log.
- The whole project, with these files, was rebuilt for version 1.27.0 (`logs/clean-replay-v1.27.0-receipt.json`).

The statement files, the proofs and the acceptance scripts were written by OpenAI Codex (model GPT-6.2-Astra). The
final reviews were done by Claude Code agents (model Claude Opus 5.5) that had written none of the files, on 27
November 2026: for Theorem A a final review (report 04:07:51 UTC) and a separate search for prior work (03:56:14–04:05:04
UTC), for Theorem B one agent for both (05:46:43–06:01:22 UTC). The reviewers recomputed the hashes, checked the
receipts, read the statements line by line, the written proofs and the proof files, and checked with plain `lean`,
against the compiled files of one directory of each run (`root1`) and without writing to the project, that the check
theorem has exactly the frozen type and the three standard axioms and that the definitions are unchanged; they did not
rebuild the formalization. Both decisions were PASS, with no blocking remarks and with recommended corrections of the
written account, which the paper takes into account. Claude Code moved the files into the repository, changed their
`import` lines and ran the recheck above. The package is not checked with comparator or nanoda. No human mathematician
has read the proofs.
