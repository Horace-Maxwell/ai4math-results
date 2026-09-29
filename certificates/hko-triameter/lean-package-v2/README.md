# Lean package of Paper 4, version 2

The files of `lean/Research/Backfill/Paper4/` as they were accepted before they were copied into the
release tree.

- `package-manifest.json`: the 50 targets, the declaration that proves each of them and its author
  (OpenAI Codex for 46 statements, Claude Code for `TheoremA_unique`, `TheoremB_unique`,
  `Sec4_count_median` and `Sec4_count_labelled`), and the SHA-256 of every module, before and after
  packaging. Packaging changed only the `import` lines (module names under
  `Research.Backfill.Paper4.Proof`); `Check.lean` states one `check_X : Challenge.X` for each target.
- `receipt.json`: the acceptance run of the package (Claude Code, 28 September 2026): every module
  compiled one at a time in an empty directory with Lean 4.34.1 and the pinned Mathlib, then replayed
  with `leanchecker`, twice (a normal and a fresh directory); no warnings; every `#print axioms` line
  lists only `propext`, `Classical.choice` and `Quot.sound`. Paths in these files are relative to the
  project in which the package was built; they are records, not inputs of the build here.
- The frozen statement file is `lean/Research/Backfill/Paper4/Challenge.lean`, SHA-256
  `9f1b0c95f35addf03f54c330ea0cd63324154d17e1cc8e707c8bf830da4a0785`.
