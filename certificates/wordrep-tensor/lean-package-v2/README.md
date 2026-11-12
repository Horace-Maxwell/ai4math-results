# Lean package of Paper 10, version 2

The files of `lean/Research/WordRepTensor/` after version 2 of Paper 10, which adds Theorem 3 (Problems 5.2
and 5.3 of Alshammari). The 11 modules of version 1 are unchanged (`lean-package/` describes them); version 2
adds the 6 modules of `lean/Research/WordRepTensor/TaskF/`.

- `package-manifest.json`: the SHA-256 and the imports of all 17 modules, the Lean toolchain, the Mathlib
  commit, the hashes of the two frozen files of version 2 (`TaskF/Challenge.lean`, the statements of
  Theorem 3, and `TaskF/RouteContract.lean`, the internal statements of its proof) and the entry point
  `Research.WordRepTensor.TaskF.FinalAudit`. The 17 files are byte for byte the ones OpenAI Codex
  accepted.
- The two files of version 2 were reviewed by a Codex agent that had not written them and frozen on
  9 November 2026 at 23:14 UTC. Only `Problem5_2` and `Problem5_3` are results; the internal statements are
  steps of the proof.
- `receipt.json`: the builds on the author's Windows computer (63 GB of memory, 16 logical CPUs) with
  Lean 4.34.1 and the pinned Mathlib, which were not rebuilt. Builds A and B compiled the 17 modules, each
  module by its own Lean process and up to 16 at a time, each build in a new empty directory, one after the other on 9 November 2026 (23:31–23:42 UTC), and replayed
  every module with `leanchecker`. All 68 commands passed at the first attempt, with no warning, and the 17
  `.olean` files of the two builds are byte for byte identical. The axioms of `check_Problem5_2` and
  `check_Problem5_3` are exactly `propext`, `Classical.choice` and `Quot.sound`.
- `build-A-logs.tar.gz`, `build-B-logs.tar.gz`: the status file, the plan, the driver log and the compile
  and `leanchecker` log of every module of builds A and B.
- The 17 modules were compiled and checked again in the whole-project rebuild of this release
  (`logs/clean-replay-v1.19.0-receipt.json`).

The statement files, the proofs and the build driver of version 2 were written by OpenAI Codex. The finite
check of the seven-vertex windows is proved with `decide +kernel`, which the Lean kernel evaluates; no
`native_decide` is used.

The two theorems of version 2 are not in the comparator check (the 11 statements of version 1 are). Their
proofs are replayed by the Lean kernel with `leanchecker`, and no other kernel has checked them.
