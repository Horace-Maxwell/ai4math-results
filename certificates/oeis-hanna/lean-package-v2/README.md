# Lean package of Paper 2, version 2

The files of `lean/Research/Backfill/Paper2/` and the record of their builds. The numerical checks of the
OEIS entries remain in `certificates/oeis-hanna/`; the proofs here do not use them.

- `package-manifest.json`: the SHA-256 and the imports of every module, the Lean toolchain, the Mathlib
  commit, the date of the frozen statement files and the entry point `Research.Backfill.Paper2.Check`, which
  restates the 84 frozen statements and prints their axioms.
- The four statement and test files (`Challenge.lean`, `ChallengeTests.lean`, `ReviewRegressionTests.lean`,
  `StatementTypeAudit.lean`) are byte for byte the files frozen on 5 November 2026; `frozen_files` in
  `package-manifest.json` gives their hashes. The 55 proof modules are byte for byte the ones Codex
  accepted.
- The comments in the four frozen files were written on 27 September 2026 from version 1.2.1 and are frozen
  with them. Their line numbers refer to version 1.2.1. They are not statements. Remarks there that
  existence and uniqueness are "not formalized so far", and that A240998 has a solution with `a(0) = 0`,
  predate the proofs and are not claimed.
- `receipt.json`: the builds on the author's Windows computer (63 GB of memory, 16 logical CPUs) with
  Lean 4.34.1 and the pinned Mathlib. Builds A and B compiled and replayed these 59 modules from two empty
  directories, one after the other, on 6 November 2026; each module passed at the first attempt, without
  warnings, and their `.olean` files are byte for byte identical. Mathlib and the toolchain were not rebuilt.
- `build-A-logs.tar.gz`, `build-B-logs.tar.gz`: the status file and the compile and `leanchecker` log of
  every module of builds A and B.
- `Check.lean` was written by Claude Code after builds A and B, by a program that reads the list of accepted
  statements. It contains no proofs of its own: each theorem is the frozen statement, proved by a theorem of
  the package. It is not in builds A and B. It was compiled and checked in the whole-project build
  (`logs/clean-replay-v1.15.0-receipt.json`).

Paper 2 has not been checked with comparator or with the independent kernel nanoda. `leanchecker` replays
the proofs in the Lean kernel, and no other kernel has checked them.

No Lean statement mentions the OEIS, the literature or the numerical checks.

In the published logs the two local directories are replaced by `<workspace>` and `<worker>`; nothing else
is changed. Paths in these files are relative to the project in which the package was built; they are records, not
inputs of the build here.
