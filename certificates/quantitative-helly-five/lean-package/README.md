# Lean package of Paper 28

The files of `lean/Research/TaskT/HellyFive/` (Paper 28: the discrete quantitative Helly number `c(Z^n, 5)` of
Averkov, González Merino, Paschke, Schymura and Weltge, Adv. Appl. Math. 89 (2017), arXiv:1602.07839v1, and the
largest number `g(Z^n, 5)` of vertices of a lattice polytope with exactly five non-vertex lattice points), 35 files:
the 31 modules in the import closure of `Check.lean`, that is, the statement file `Challenge.lean`, 29 proof modules
(among them `Proof.lean` and the two table modules `PlanarTable.lean` and `UpperThreeTable.lean`) and the check file
`Check.lean`; and four auxiliary audit modules (`BridgeAudit.lean`, `FiniteAudit.lean`, `FiniteHellyLower.lean`,
`UpperTransferAudit.lean`) that print axioms and restate intermediate results (among them the two lower bounds 18
and 37). Nothing in the proof depends on the auxiliary modules, and `lean/Research.lean` does not import them.

- `package-manifest.json`: the SHA-256 and the imports of the 35 modules, the Lean toolchain, the Mathlib commit,
  the entry point imported by `lean/Research.lean` (`Research.TaskT.HellyFive.Check`), the theorems it checks
  (`TaskT.HellyFive.check_ExactHellyFive` and `TaskT.HellyFive.check_ExactVertexFive`), and the statement file with
  its SHA-256 and freeze time. For each file it also gives the SHA-256 of the file Codex wrote and whether the file is
  one of the 31 modules of Codex's acceptance run (`in_codex_acceptance_receipt`; false for the four auxiliary
  modules). The files in the repository have module names under `Research.TaskT.HellyFive` (the namespace
  `TaskT.HellyFive` is kept) and differ from Codex's files only in their `import` lines; `Challenge.lean`, which
  imports only Mathlib, is byte for byte the frozen file (SHA-256 `faf32ea5…6d26`).
- Statement file, written by a Codex agent: `Challenge.lean` (`Grid`, `embed`, `commonGrid`, `PreservesFive`,
  `attainableCounts`, `value` and the targets `ExactHellyFive` and `ExactVertexFive`). It was compared with the source
  (`SOURCE-CHECK.md`), compiled without diagnostics (21 November 2026, 01:10:41–01:11:05 UTC, receipt
  `receipts/20261121T011041Z-Challenge-17618.*`), approved by a Codex agent that had written neither the statement nor
  the proofs (`FREEZE-REVIEW.md`, APPROVE_STATEMENT_FREEZE at 01:11:14 UTC), and frozen at 01:11:55 UTC
  (`FREEZE.json`, which also pins the written proof, the review of the written proof `prior-REVIEW-HELLY.md`,
  APPROVE_WRITTEN at 01:09:48 UTC, and the compile receipt). The development receipts record no compilation of a
  proof file before the freeze (the earliest is at 01:12:45 UTC).
- `codex-acceptance-logs.tar.gz`: Codex's acceptance run on the author's Mac with Lean 4.34.1 and the pinned Mathlib,
  which was taken from a prebuilt cache and not rebuilt (`acceptance/2026-11-21T013611Z-43897`, 21 November 2026,
  01:36:18–02:13:44 UTC; the two directories one after the other, 01:36:18–01:58:30 and 01:58:30–02:13:44). In each
  of two new empty directories, each of the 31 modules was built with `lake --no-cache --wfail build +M:olean`
  (warnings fail) and replayed with `lake env leanchecker M`, and the whole package was built once with
  `lake --no-cache --wfail build`. All 126 commands (63 per directory) ended with exit code 0; the 62 `leanchecker`
  logs are empty; the build logs contain only Lake's progress and completion lines and the four axiom lines printed
  by `Check.lean`; the 31 `.olean` files have the same SHA-256 in the two directories (receipt); the largest memory
  use of a single command was 14.01 GB (the build of `UpperThreeTable`; the commands of the two table modules held
  both of the Mac's Lean slots). The theorems
  `Proof.ExactHellyFive`, `Proof.ExactVertexFive` and the two check theorems depend exactly on `propext`,
  `Classical.choice` and `Quot.sound`. The archive holds, for this run, the receipt, Codex's post-check
  (`postcheck.json`) and technical review (`TECHNICAL-REVIEW.json`), its recheck script (`recheck.py`), the lock
  record (`locks.log`) and the logs of both directories; further the freeze record and review (`FREEZE.json`,
  `FREEZE-REVIEW.md`, `SOURCE-CHECK.md`, the compile receipt of the statement file and the frozen `Challenge.lean`),
  the review of the written proof (`prior-REVIEW-HELLY.md`), the review of the source files by a Codex agent that had
  not written the proofs (`continuation/INDEPENDENT-CODE-REVIEW.md`, 01:34:57 UTC), the receipt checker
  (`continuation/verify_receipt.py`), the record of the release of two locks held by processes that stopped when the
  Codex session reached its usage limit (`continuation/interruption-cleanup.json`), Codex's status and handoff
  records (`STATUS.md`, `FINAL-HANDOFF.md`, `DONE`), the acceptance script (`accept.py`) and the six helper files it
  uses (`runner-dependencies/`; their SHA-256 are the ones recorded in the receipt) and the two final reviews
  (`FINAL-CLAUDE-REVIEW-01.md`, `FINAL-CLAUDE-REVIEW-02.md`). It does not hold the written proofs, the source paper
  that Codex consulted or the brief of the search for problems. `<workspace>` replaces the local project directory
  and `<claude-scratch>` the reviewers' scratch directory; nothing else is changed. The build directories themselves
  are not included. The four auxiliary modules are not part of this run.
- `receipt.json` and `repository-recheck-logs.tar.gz`: the 35 repository files, the four auxiliary modules included,
  compiled with `lean` and replayed with `leanchecker` again, module by module, in two new empty directories on the
  author's Mac (22 November 2026, 21:08–21:20 and 21:20–21:33 UTC): all 35 compiled and passed `leanchecker` in each
  directory, with no warning and no error, and identical `.olean` files. The 23 axiom lists printed (by `Check.lean`
  and the audit modules) are the same in both directories; all are `propext`, `Classical.choice` and `Quot.sound`
  except `TaskT.HellyFive.recover_vertex` (in `BridgeAudit.lean`), which depends on `propext` and `Quot.sound` only.
  The archive holds the logs, the recheck script (`mac_compile_generic.py`), the script that moved the files into
  the repository (`integrate_generic.py`) and its record (`helly-integration.json`).
- The whole project, with these files, was rebuilt for version 1.26.0 (`logs/clean-replay-v1.26.0-receipt.json`).

The statement file, the proofs and the acceptance scripts were written by OpenAI Codex (model GPT-6.2-Astra). The
final reviews were done by two Claude Code agents (model Claude Opus 5.5) that had written none of the files and did
not read each other's report (21 November 2026, from 03:20:49 UTC; reports after 03:34:12 and 04:27:56 UTC). Each
compiled all 35 files again with plain `lean` in a new directory, together with an audit file of its own, and
replayed every module with `leanchecker`: 36 of 36 modules compiled with exit code 0 and no warning, and every
`leanchecker` run ended with exit code 0 and empty output. The decisions were APPROVE_FORMAL and
APPROVE_WITH_CHANGES, with no blocking or major remark; the minor remarks (6, two of them optional, and 7) concern the
written account and the attribution, among them that the four auxiliary modules should be described as such. Claude
Code moved the files into the repository, changed their `import` lines and ran the recheck above. The package is not
checked with comparator or nanoda. No human mathematician has read the proofs.
