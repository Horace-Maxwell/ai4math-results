# Lean package of Paper 10

The files of `lean/Research/WordRepTensor/` as they were accepted before they were copied into the
release tree.

- `package-manifest.json`: the 11 targets, the declaration that proves each of them, and the SHA-256 of
  every module, before and after packaging. Packaging changed only the `import` lines (module names
  under `Research.WordRepTensor.Proof`). The proofs were written by Claude Code.
- `receipt.json`: the acceptance run of the package (Claude Code, 28 September 2026): every module
  compiled one at a time in an empty directory with Lean 4.34.1 and the pinned Mathlib, then replayed
  with `leanchecker`, twice (a normal and a fresh directory); no warnings; every `#print axioms` line
  lists only `propext`, `Classical.choice` and `Quot.sound`. Paths in these files are relative to the
  project in which the package was built; they are records, not inputs of the build here.
- The frozen statement file is `lean/Research/WordRepTensor/Challenge.lean`, SHA-256
  `40c8efd69f8499c9874f07163043c0793c94c8597b7a3902d5aeb0a2ce0c9b58`.
