# Lean package of Paper 1, version 3

Version 3 adds the files of `lean/Research/TaskE/` (45 modules) to the 70 modules of version 2
(`lean-package-v2/`, unchanged). Together they prove Theorem 5 of version 3: the equal-parity formula and its
two maximisers when one of the two primes is 3 and both exponents are at least 3 (`SameParityThree`), in addition
to the case `min(a,b) ≤ 2` of version 2 (`Theorem5MinTwo`).

- `package-manifest.json`: the SHA-256 of every one of the 115 modules (70 of version 2, byte for byte the same,
  and 45 new) and its imports within the project (imports of Mathlib are not listed), the Lean toolchain, the
  Mathlib commit, the time at which the main statement was frozen, and the entry point
  `Research.TaskE.FinalTaskEAudit`, which restates `SameParityThree` and the auxiliary statements, checks two
  instances of the main statement and prints the axioms of the main theorem
  `CodexPaper1.TaskE.check_SameParityThree` and of its main lemmas.
- The statement files `Challenge.lean` (the main statement `SameParityThree`, frozen on 8 November 2026 at
  17:28 UTC after an independent review) and `ChallengeS.lean`, `ChallengeF.lean`, `ChallengeFC.lean`,
  `ChallengeC0.lean`, `ChallengeC1.lean`, `ChallengeC1Alt.lean` (auxiliary statements, frozen between 17:28 and
  19:16 UTC) are byte for byte the frozen files; `frozen_files` in `package-manifest.json` gives their hashes.
  `UniformConditionsBothRegions`, defined in `Challenge.lean`, is not proved and not claimed.
- `receipt.json`: the builds on the author's Windows computer (63 GB of memory, 16 logical CPUs) with Lean
  4.34.1 and the pinned Mathlib. Builds A and B compiled the 115 modules and replayed them with `leanchecker`
  from two new empty directories, one after the other, on 8 November 2026 (20:05–20:49 UTC); each of the 460
  commands passed at the first attempt, without warnings, and the `.olean` files of the two builds are byte for
  byte identical. Mathlib and the toolchain were not rebuilt.
- `build-A-logs.tar.gz`, `build-B-logs.tar.gz`: the status file and the compile and `leanchecker` log of every
  module of builds A and B.
- The 115 modules were compiled and checked again in the whole-project rebuild of this release
  (`logs/clean-replay-v1.17.0-receipt.json`).

`C1High.lean` proves an auxiliary statement that the main theorem does not use; it is kept because it is part of
the accepted package. Comments inside the proof modules are development notes of Codex and may be out of date.

Paper 1 has not been checked with comparator or with the independent kernel nanoda. `leanchecker` replays the
proofs in the Lean kernel, and no other kernel has checked them.

In the published logs the local directories are replaced by `<workspace>` and `<worker>`; nothing else is
changed. Paths in these files are relative to the project in which the package was built; they are records, not
inputs of the build here.
