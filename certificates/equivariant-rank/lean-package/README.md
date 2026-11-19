# Lean package of Paper 14

The files of `lean/Research/TaskJ/Rank/` (Paper 14: the rank of the group of `G`-equivariant permutations of a
finite `G`-set, against the bounds and the exactness expectation of Lara-Gómez, Romero-Rosales and Ruiz-Medina,
arXiv:2607.04053v1 and Semigroup Forum, published online 2 November 2026), 15 files: 5 for Theorems 1 and 2
(the two-point and five-point examples) and 10, in `Extension/`, for Theorem 3 (the unbounded family).

- `package-manifest.json`: the SHA-256 and the imports of the 15 modules, the Lean toolchain, the Mathlib commit,
  the two entry points imported by `lean/Research.lean`, the seven theorems `check_*` that restate the frozen
  statements, and the two statement files with their SHA-256 and freeze times. For each file it also gives the
  SHA-256 of the file Codex accepted. The files in the repository have module names under `Research.TaskJ` and
  differ from the accepted files only in their `import` lines (Codex built them as a flat package with module
  names such as `Challenge` and `Proof`); the two statement files have no local imports and are byte for byte
  the frozen ones.
- Statement files: `Challenge.lean` (SHA-256 `5ebdebf7…21e5`; six statements: the parameters, the rank and the
  failure of the printed bounds for the two-point and the five-point example) and `Extension/Challenge.lean`
  (`efa3009d…ad72`; the statement `UnboundedGap`). Each was reviewed by a Codex agent that had not written it and
  frozen on 18 November 2026, 00:07:30 UTC and 00:22:07 UTC; the development logs record no compilation of a proof file before those times.
- `codex-acceptance-logs.tar.gz`: Codex's acceptance runs on the author's Mac with Lean 4.34.1 and the pinned
  Mathlib, which was taken from a prebuilt cache and not rebuilt. Each run compiled every module in two new empty
  directories and replayed every module with `leanchecker`, and each directory also built the whole package. The
  package for Theorems 1 and 2 passed on 18 November 2026, 00:14:57–00:15:59 UTC (22 commands); the package for
  Theorem 3 on 00:29:55–00:32:14 UTC (42 commands). All commands ended with exit code 0, the `leanchecker` runs
  printed nothing, and the `.olean` files of the two directories have the same SHA-256. Two earlier runs of the
  first package are included: at 00:10 UTC the run stopped before compiling because the Mathlib cache was not
  found (`status: INCOMPLETE`), and at 00:11 UTC a run passed. The archive also holds the freeze records and
  reviews and the acceptance scripts. `<workspace>` replaces the local project directory; nothing else is
  changed. The build directories themselves are not included.
- `receipt.json` and `repository-recheck-logs.tar.gz`: the repository versions of the 43 files of Papers 14 and 15
  compiled and replayed with `leanchecker` again, module by module, in two new empty directories on the author's
  Mac (18 November 2026, 19:12–19:21 UTC): all compiled and passed `leanchecker`, with no warning, identical
  `.olean` files, and the same axiom lists as in Codex's runs. The theorems `check_*` depend exactly on
  `propext`, `Classical.choice` and `Quot.sound`.
- The whole project, with these files, was rebuilt for version 1.23.0 (`logs/clean-replay-v1.23.0-receipt.json`).

The statement files, the proofs and the acceptance scripts were written by OpenAI Codex (model GPT-6.2-Astra).
The final review of the formal proof was done by an independent Claude Code agent (model Claude Opus 5.5) that
had written none of the files. Claude Code moved the files into the repository, changed their `import` lines and
ran the recheck above. The package is not checked with comparator or nanoda.
