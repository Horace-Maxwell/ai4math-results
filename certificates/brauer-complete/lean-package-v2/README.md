# Lean package of Paper 5, version 2

The files of `lean/Research/Backfill/Paper5/` as they were accepted before they were copied into the
release tree (70 modules, copied unchanged).

- `Challenge.lean` is the frozen statement file of 27 September 2026 (SHA-256
  `ca2ff711b3ed008112d3633551a0703da79167805815d0cbe04599728a9bc373`, 33 statements). Its header
  mentions internal working notes (`STATEMENTS.md`) that are not part of this repository; the
  statements themselves are complete as written.
- `Supplement/` holds the three supplementary statement files of 1 October 2026 (12 statements, two of
  them auxiliary): `AssociativityStatement.lean`, `FullPaperStatement.lean` and
  `AlgebraStatementV2.lean`. Each was reviewed independently and frozen by its SHA-256 hash before its
  proofs were accepted; the copies here are byte-identical to the frozen files (`626da68a…`,
  `7c624d7c…`, `6d864b91…`, the hashes recorded in Section 9 of the paper).
- `Check.lean` proves the 45 statements: for each statement `X` a theorem `check_X` whose type is the
  statement written out in full. `ChallengeTests.lean` holds the 68 known-answer tests of the
  statement file, as theorems `test_001` … `test_068`; their types and proofs are those of the
  `example`s of the original test file, which is kept here as
  `provenance/ChallengeTests.lean.original` (SHA-256 `22862c0e…`, as in `package-manifest.json`).
- `Proof/` holds the 64 proof modules, written by OpenAI Codex from 29 September to 1 October 2026;
  `Proof/ReesCoreCompat.lean` is a copy of `lean/Research/BrauerCMCore.lean` of version 1 (written by
  Claude Code), changed only in its namespace and in four uses of two library lemmas whose names have
  changed. Packaging changed only module names in `import` lines; `package-manifest.json` records the
  SHA-256 of every file, the import graph, the toolchain (Lean 4.34.1) and the Mathlib revision
  (`d13f23b723b8a846827a245b89c10fc7d3f11612`). It is the snapshot taken before the acceptance run,
  so its own status fields still say that acceptance is pending.
- Comments in `Check.lean` that name the original per-group check files, and the reference to an
  addendum in the header of `ChallengeTests.lean`, point to internal working files that are not part
  of this repository.
- `receipt.json`: the acceptance run (OpenAI Codex, 6 October 2026, 16:28–16:44 UTC). In two new empty
  directories, side by side, every module was compiled with the pinned toolchain and Mathlib and then
  checked with `leanchecker`: 280 commands, all with exit code 0 and no warning or error (the
  `diagnostics` of every step, and `summary`); all 1568 printed axiom lists are subsets of `propext`,
  `Classical.choice` and `Quot.sound`; the 68 tests were compiled and checked in both directories. A
  Codex agent that had written none of the proofs or scripts reviewed the evidence and approved it
  (16:53 UTC). The file is a summary of the original receipt, whose SHA-256 it records; paths in it
  are relative to the project in which the package was built; they are records, not inputs of the
  build here.
