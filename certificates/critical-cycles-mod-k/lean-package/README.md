# Lean packages of Paper 13

The files of `lean/Research/TaskH/` (Paper 13: Question 8 of Choi and Sieniawski, arXiv:2611.13580v1, for
`k = 4, 5, 6, 7`). OpenAI Codex built and accepted them as four packages, one for each `k`; the release contains
their union, 447 files. A file that occurs in several packages has the same content in all of them.

- `package-manifest.json`: the SHA-256 and the imports of the 447 modules, the Lean toolchain, the Mathlib commit,
  the five entry points imported by `lean/Research.lean` and the main theorems `TaskH.case_four`, `case_five`,
  `case_six` and `case_seven`. The files are byte for byte the ones of Codex's accepted packages.
- Statement files: `Challenge.lean` (`EqualityCase k`, `CaseFour`, and the full question `Question2`, which is
  defined but not proved; `Question2` is the files' name for Question 8 of the source), `CaseFive.lean`,
  `CaseSix.lean` and `CaseSeven.lean`. Each was reviewed by a Codex agent that had not written it and frozen
  before any proof file specific to that `k` was written: 13 November 2026, 18:42 UTC (`k = 4`) and 21:15 UTC
  (`k = 5`); 14 November 2026, 00:05 UTC (`k = 6`) and 06:32 UTC (`k = 7`).
- `receipt.json`: for each `k`, the formal batch of Codex on the author's Windows computer (63 GB of memory,
  16 logical CPUs) with Lean 4.34.1 and the pinned Mathlib, which were not rebuilt. Builds A and B compiled the
  modules of that case (49, 120, 236 and 240), each module by its own Lean process, each build in a new empty
  directory, one after the other (`k = 4`: 13 November 2026, 20:45–21:02 UTC; `k = 5`: 13–14 November,
  23:51–00:32 UTC; `k = 6`: 14 November, 05:26–06:40 UTC; `k = 7`: 15 November, 07:35–09:01 UTC), and
  replayed every module with `leanchecker`. Every final command passed with no warning, and the `.olean` files
  of builds A and B are byte for byte identical. In the batch for `k = 6`, 13 attempts ended without a Lean
  verdict (11 could not read a file, 2 ran out of memory); the driver ran these modules again and they passed
  (`commands_passing_after_automatic_reruns`: 6 in build A, 3 in build B). The axioms of `case_four`,
  `case_five`, `case_six` and `case_seven` are exactly `propext`, `Classical.choice` and `Quot.sound`.
- `k<k>-build-A-logs.tar.gz`, `k<k>-build-B-logs.tar.gz`: the status file, the plan, the driver log and the
  compile and `leanchecker` log of every module of each build. In these logs `<workspace>` and `<worker>` replace
  local directories; nothing else is changed.
- No batch built all 447 files together; the whole-project rebuild of this release did
  (`logs/clean-replay-v1.21.0-receipt.json`).

The statement files, the proofs and the build driver were written by OpenAI Codex. Codex's final reviews did not
each read every file, and for `k = 7` the records do not identify the authors of 40 of the 240 files; see the
disclosure in the README. No `native_decide` is used.

Paper 13 is not in the comparator check. Its proofs are replayed by the Lean kernel with `leanchecker`, and no
other kernel has checked them.
