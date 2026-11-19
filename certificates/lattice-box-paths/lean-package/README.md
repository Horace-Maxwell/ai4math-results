# Lean package of Paper 15

The files of `lean/Research/TaskJ/Grid/` (Paper 15: the maximum Manhattan length of a path through all lattice
points of a box, the first question of §6.3 of Yuan, arXiv:2611.19908v1), 28 files: the statement file
`Challenge.lean`, 25 proof modules, `Proof.lean` and `CheckGrid.lean`.

- `package-manifest.json`: the SHA-256 and the imports of the 28 modules, the Lean toolchain, the Mathlib commit,
  the entry point imported by `lean/Research.lean`, the three theorems `check_LengthUpperBound`,
  `check_LengthAttained` and `check_YuanGapAtLongest` that restate the frozen statements, and the statement file
  with its SHA-256 and freeze time. For each file it also gives the SHA-256 of the file Codex accepted. The files
  in the repository have module names under `Research.TaskJ.Grid` and differ from the accepted files only in
  their `import` lines (Codex built them as a flat package); `Challenge.lean` has no local imports and is byte for
  byte the frozen one.
- Statement file: `Challenge.lean` (SHA-256 `6b0ad9f9…5e07`), reviewed by a Codex agent that had not written it
  and frozen on 18 November 2026, 00:03:17 UTC; the development logs record no compilation of a proof file before that time.
- `codex-acceptance-logs.tar.gz`: Codex's acceptance run on the author's Mac with Lean 4.34.1 and the pinned
  Mathlib, which was taken from a prebuilt cache and not rebuilt, on 18 November 2026, 00:23:27–00:30:06 UTC.
  Every module was compiled in two new empty directories and replayed with `leanchecker`, and each directory also
  built the whole package: 114 commands, all with exit code 0; the `leanchecker` runs printed nothing and the
  builds nothing except the requested axiom lists; the `.olean` files of the two directories have the same
  SHA-256. The archive also holds the freeze record and review and the acceptance scripts. `<workspace>` replaces
  the local project directory; nothing else is changed. The build directories themselves are not included. A
  further file of Codex's development, `GridLowerPrep.lean`, which nothing imports and which was not in the
  acceptance run, is not included.
- `receipt.json` and `repository-recheck-logs.tar.gz`: the repository versions of the 43 files of Papers 14 and 15
  compiled and replayed with `leanchecker` again, module by module, in two new empty directories on the author's
  Mac (18 November 2026, 19:12–19:21 UTC): all compiled and passed `leanchecker`, with no warning, identical
  `.olean` files, and the same axiom lists as in Codex's run. The three theorems `check_*` depend exactly on
  `propext`, `Classical.choice` and `Quot.sound`.
- The whole project, with these files, was rebuilt for version 1.23.0 (`logs/clean-replay-v1.23.0-receipt.json`).

The statement file, the proofs and the acceptance scripts were written by OpenAI Codex (model GPT-6.2-Astra).
The final review of the formal proof was done by an independent Claude Code agent (model Claude Opus 5.5) that
had written none of the files. Claude Code moved the files into the repository, changed their `import` lines and
ran the recheck above. The package is not checked with comparator or nanoda.
