# Lean package of Paper 12

The files of `lean/Research/TaskG/` (Paper 12, an answer to Shpectorov's question on Frobenius forms of axial
algebras) and the two files of `lean/Research/AxialMSZ/` that were built with them: the statement file of
Paper 9, whose definitions (fusion law, axis, primitive axial algebra, ideal, Frobenius form, product from
structure constants) Paper 12 reuses, and its tests. Both files of Paper 9 are unchanged.

- `package-manifest.json`: the SHA-256 and the imports of the 10 modules, the Lean toolchain, the Mathlib
  commit, the hash of the frozen statement file `TaskG/Challenge.lean` and the entry point
  `Research.TaskG.Check`. The 10 files are byte for byte the ones OpenAI Codex accepted.
- The statement file was reviewed by a Codex agent that had not written it and frozen on 12 November 2026 at
  16:27 UTC, before the proof files were written. Lean then needed the facts that 5, 7 and 11 are prime to
  use `ZMod 5`, `ZMod 7` and `ZMod 11` as fields; three lines providing them (each proved by
  `decide +kernel`) and a comment were added, nothing else changed (by then the proof files had been drafted),
  the same reviewer checked the difference, and the file
  was frozen again at 16:41 UTC (SHA-256 `05448636…09bb8`).
- `receipt.json`: the builds on the author's Windows computer (63 GB of memory, 16 logical CPUs) with
  Lean 4.34.1 and the pinned Mathlib, which were not rebuilt. Builds A and B compiled the 10 modules, each
  module by its own Lean process, each build in a new empty directory, one after the other on 12 November
  2026 (17:25–17:32 UTC), and replayed every module with `leanchecker`. All 40 commands passed at the first
  attempt, with no warning, and the 10 `.olean` files of the two builds are byte for byte identical. The
  axioms of `check_ShpectorovAnswer` and `check_StrongShpectorovAnswer` are exactly `propext`,
  `Classical.choice` and `Quot.sound`.
- `build-A-logs.tar.gz`, `build-B-logs.tar.gz`: the status file, the plan, the driver log and the compile
  and `leanchecker` log of every module of builds A and B.
- The modules were compiled and checked again in the whole-project rebuild of this release
  (`logs/clean-replay-v1.20.0-receipt.json`).

The statement file, the proofs and the build driver were written by OpenAI Codex. The finite computations
over `ZMod 11` are proved with `decide +kernel`, which the Lean kernel evaluates, and with `ring`; no
`native_decide` is used.

Paper 12 is not in the comparator check. Its proofs are replayed by the Lean kernel with `leanchecker`, and no
other kernel has checked them.
