# Lean package of Paper 1, version 2

The files of `lean/Research/Backfill/Paper1/` and of the modules `lean/Research/ICG*.lean`, and the record of
their builds. The programs and computations of version 1.5 remain in `certificates/icg-q3-general/`; version 2
withdraws the results that rested on them, and the proofs here do not use them.

- `package-manifest.json`: the SHA-256 of every one of the 70 modules and its imports within the project (imports of Mathlib are not listed), the Lean toolchain, the
  Mathlib commit, the date of the frozen statement files and the entry point
  `Research.Backfill.Paper1.FinalContractAudit`, which restates the 51 frozen statements (31 main and 20
  supplementary) and prints their axioms.
- The four statement and test files (`Challenge.lean`, `SupplementStatements.lean`, `ChallengeTests.lean`,
  `NarrowContractTests.lean`) are byte for byte the files frozen on 7 November 2026 (03:05 UTC);
  `frozen_files` in `package-manifest.json` gives their hashes. All 70 modules are byte for byte the ones
  Codex accepted.
- `receipt.json`: the builds on the author's Windows computer (63 GB of memory, 16 logical CPUs) with Lean
  4.34.1 and the pinned Mathlib. Builds A and B compiled the 70 modules and replayed them with `leanchecker`
  from two new empty directories, one after the other, on 7 November 2026 (04:50–05:21 UTC); each of the 280
  commands passed at the first attempt, without warnings, and the `.olean` files of the two builds are byte for
  byte identical. Mathlib and the toolchain were not rebuilt.
- `build-A-logs.tar.gz`, `build-B-logs.tar.gz`: the status file and the compile and `leanchecker` log of every
  module of builds A and B.
- The 70 modules were compiled and checked again in the whole-project rebuild of this release
  (`logs/clean-replay-v1.16.0-receipt.json`).

Thirteen modules `Research/ICG*.lean` were written in September 2026 for versions 1.1 to 1.5 of the paper. In
this release they differ from the previous release only in the names of three Mathlib lemmas (`if_pos`, `if_neg`,
`if_true` replaced by `ite_eq_left`, `ite_eq_right`, `ite_true`), which removes deprecation warnings.

Comments inside the proof modules are development notes of Codex and may be out of date: for example
`Prop31.lean` says that compilation and the checks have not yet been run, and `Additional.lean` names the hash of
the statement file frozen in September 2026. They are not statements; the receipts above record what was run.
The modules are published byte for byte as Codex accepted them, so these comments were not edited.

Paper 1 has not been checked with comparator or with the independent kernel nanoda. `leanchecker` replays the
proofs in the Lean kernel, and no other kernel has checked them.

No Lean statement mentions the literature or the withdrawn computations of version 1.5.

In the published logs the local directories are replaced by `<workspace>` and `<worker>`; nothing else is
changed. Paths in these files are relative to the project in which the package was built; they are records, not
inputs of the build here.
