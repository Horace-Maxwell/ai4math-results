# Lean package of Paper 11

The files of `lean/Research/CographDist/` (6 modules). They prove Theorem 1 of Paper 11: for every `m ≥ 1`
the graph `G_m = K_1 ∨ (K_1 ∪ mK_2)` is a connected cograph with a distance eigenvalue in
`(−2 − 1/(2m), −2)`, and hence the statement `OpenProblemI_negative` (the answer no to part (i) of the open
problem of arXiv:2611.06981 quoted in the paper). Remark 1 of the paper, which derives the answer from a lemma
of Conde, Dratman and Grippo, is not formalized.

- `package-manifest.json`: the SHA-256 of every module and its imports within the project (imports of Mathlib
  are not listed), the Lean toolchain, the Mathlib commit, the time at which the statement file was frozen, and
  the entry point `Research.CographDist.Audit`, which restates `OpenProblemI_negative`
  (`CographDist.Audit.check_OpenProblemI_negative`) and Theorem 1 for each `G_m`
  (`CographDist.Audit.check_family`), and prints their axioms and those of the five tests.
- The statement file `Challenge.lean` (definitions `HasInducedP4`, `IsCograph`, `distMatrix`,
  `IsDistEigenvalue` and the statement `OpenProblemI_negative`; no proofs) was reviewed by an independent Claude
  Code agent (model Claude Fable 5.1) and frozen on 9 November 2026 at 22:56:29 UTC, SHA-256
  `960a24b9de500d2449a73a83b7385653f63054ab52dab3053d287c4e1270e569`. The proof files were drafted while that
  review ran; the statement file was not changed to fit them. When the files were moved from the working
  directory `CographDist/` to `Research/CographDist/`, `Challenge.lean` stayed byte for byte the same, and
  `ChallengeTests.lean` changed only in its `import` line; the manifest gives both hashes.
- `ChallengeTests.lean`: five tests of the statement file (the path on four vertices is not a cograph; `K_2`
  is connected and a cograph; 1 is and 2 is not a distance eigenvalue of `K_2`).
- `receipt.json`: two builds on the author's Mac (Apple silicon) with Lean 4.34.1 and the pinned Mathlib, which
  were not rebuilt. Builds A and B compiled the 6 modules one at a time, in import order, and replayed each with
  `leanchecker`, from two new empty output directories, one after the other, on 9 November 2026 (A 23:20:09–
  23:21:48 UTC, B 23:21:48–23:23:02 UTC). All 24 commands (12 per build) ended with exit code 0 at the first
  attempt, with no error, no warning and no `sorry`, and the `.olean` files of the two builds are byte for byte
  identical. `Research.CographDist.Audit` prints 7 axiom lists, each exactly `propext`, `Classical.choice` and
  `Quot.sound`. No file uses `sorry`, `native_decide`, `bv_decide` or an `axiom` declaration.
- `build-A-logs.tar.gz`, `build-B-logs.tar.gz`: the status file, the hashes of the `.olean` files and the compile
  and `leanchecker` log of every module of builds A and B. `leanchecker` prints nothing on success, so its logs
  are empty.
- The 6 modules were compiled and checked again, each at the first attempt, in the whole-project rebuild of
  this release on 9 and 10 November 2026 (`logs/clean-replay-v1.18.0-receipt.json`).

The statement file, the proofs and the build script were written by Claude Code (model Claude Opus 5.5); the
script is not published, and the logs record the result of each command. OpenAI Codex was not involved.

Paper 11 has not been checked with comparator or with the independent kernel nanoda. `leanchecker` replays the
proofs in the Lean kernel, and no other kernel has checked them.

In the published logs the local directories are replaced by `<workspace>`, `<project>` and `<home>`; nothing
else is changed. Paths in these files are relative to the project in which the package was built; they are
records, not inputs of the build here.
