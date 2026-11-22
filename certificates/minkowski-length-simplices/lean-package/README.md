# Lean package of Paper 25

The files of `lean/Research/TaskP/GeomSimplex/` (Paper 25: lattice simplices whose Minkowski length exceeds the
lattice diameter, and dilates whose Minkowski length is not quasi-linear; Problems 2 and 3 of Soprunov and
Soprunova, European J. Combin. 58 (2016), arXiv:1412.4404v2), 16 files: the statement file `Challenge.lean`, 13
proof modules, `Proof.lean` and `CheckSimplex.lean`.

- `package-manifest.json`: the SHA-256 and the imports of the 16 modules, the Lean toolchain, the Mathlib commit,
  the entry point imported by `lean/Research.lean`, the four theorems `check_TetrahedronDiameter`,
  `check_TetrahedronDilations`, `check_EveryDimensionDiameter` and `check_EveryDimensionDilations` that restate the
  frozen statements, and the statement file with its SHA-256 and freeze time. For each file it also gives the
  SHA-256 of the file Codex accepted. The files in the repository have module names under
  `Research.TaskP.GeomSimplex` and differ from the accepted files only in their `import` lines (Codex built them as
  a flat package); `Challenge.lean` has no local imports and is byte for byte the frozen one.
- Statement file: `Challenge.lean` (SHA-256 `98fdde38…80a4`), reviewed by a Codex agent that had written neither
  the statement nor the proofs and frozen on 20 November 2026, 18:06:09 UTC; the development logs record no
  compilation of a proof file before that time. The statements cover dimension `d ≥ 3`.
- `codex-acceptance-logs.tar.gz`: Codex's acceptance run on the author's Mac with Lean 4.34.1 and the pinned
  Mathlib, which was taken from a prebuilt cache and not rebuilt, on 20 November 2026, 18:25:01–18:31:09 UTC.
  In each of two new empty directories every module was built with `lake --no-cache --wfail build` (warnings
  fail) and replayed with `leanchecker`, and the whole package was built once: 66 commands (33 per directory),
  all with exit code 0; the `leanchecker` runs printed nothing and the builds nothing except Lake's status lines
  and the requested axiom lists; the `.olean` files of the 16 modules have the same SHA-256 in the two
  directories. The archive also holds the freeze record and review, the frozen copy of the statement file, the acceptance record, the final review and the acceptance script. `<workspace>` replaces the local project
  directory and `<claude-scratch>` the reviewers' scratch directory; nothing else is changed. The build directories themselves are not included.
- `receipt.json` and `repository-recheck-logs.tar.gz`: the repository versions of the 16 files compiled with
  `lean` and replayed with `leanchecker` again, module by module, in two new empty directories on the author's
  Mac (20 November 2026, 21:04–21:16 UTC), together with the other files of Papers 23 to 25 (48 files in all):
  all compiled and passed `leanchecker`, with no warning, identical `.olean` files, and the same axiom lists as in
  Codex's run. The four theorems `check_*` and the four theorems `Proof.*` depend exactly on `propext`, `Classical.choice` and `Quot.sound`. The archive, which is
  the same in the three folders `domination-root-radius`, `bar-tiling-defect` and `minkowski-length-simplices`,
  holds the logs of all 48 files, the recheck script and the script that moved the files into the repository.
- The whole project, with these files, was rebuilt for version 1.25.0 (`logs/clean-replay-v1.25.0-receipt.json`).

The statement file, the proofs and the acceptance script were written by OpenAI Codex (model GPT-6.2-Astra).
The final review of the formal proof was done by an independent Claude Code agent (model Claude Opus 5.5) that
had written none of the files; it compiled the 16 files again in a new directory, with warnings treated as errors,
and replayed every module with `leanchecker` (20 November 2026, 20:57–21:00 UTC). Claude Code moved the files into
the repository, changed their `import` lines and ran the recheck above. The package is not checked with
comparator or nanoda.
