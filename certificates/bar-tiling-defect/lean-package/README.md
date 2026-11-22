# Lean package of Paper 24

The files of `lean/Research/TaskP/RectangleDefect/` (Paper 24: multisets of bars that do not tile a `2 × n`
rectangle, the question of Remark 5.11 of Gajdzica, Visser and Zakarczemny, Ann. Comb. (2026),
arXiv:2509.20495v2), 18 files: the statement file `Challenge.lean`, 15 proof modules, `Proof.lean` and
`CheckRectangle.lean`.

- `package-manifest.json`: the SHA-256 and the imports of the 18 modules, the Lean toolchain, the Mathlib commit,
  the entry point imported by `lean/Research.lean`, the theorem `check_SharpBound` that restates the frozen
  statement, and the statement file with its SHA-256 and freeze time. For each file it also gives the SHA-256 of
  the file Codex accepted. The files in the repository have module names under `Research.TaskP.RectangleDefect`
  and differ from the accepted files only in their `import` lines (Codex built them as a flat package);
  `Challenge.lean` has no local imports and is byte for byte the frozen one.
- Statement file: `Challenge.lean` (SHA-256 `906da3fa…29d9`), reviewed by a Codex agent that had written neither
  the statement nor the proofs and frozen on 20 November 2026, 18:06:09 UTC; the file times and the development
  logs show no proof file before that time. An earlier draft (`candidate-01`, with natural-number positions) was
  returned by its reviewer before the freeze and is not included. The lower bound of the frozen statement holds
  along subsequences of widths only.
- `codex-acceptance-logs.tar.gz`: Codex's acceptance run on the author's Mac with Lean 4.34.1 and the pinned
  Mathlib, which was taken from a prebuilt cache and not rebuilt, on 20 November 2026, 18:35:24–18:41:35 UTC.
  In each of two new empty directories every module was built with `lake --no-cache --wfail build` (warnings
  fail) and replayed with `leanchecker`, and the whole package was built once: 74 commands (37 per directory),
  all with exit code 0; the `leanchecker` runs printed nothing and the builds nothing except Lake's status lines
  and the requested axiom lists; the `.olean` files of the 18 modules have the same SHA-256 in the two
  directories. The archive also holds the freeze record and review, the frozen copy of the statement file, the acceptance record, the final review, an erratum to the final review (`FINAL-CLAUDE-REVIEW-01-ERRATUM.md`, see below) and the acceptance script. `<workspace>` replaces the local project
  directory and `<claude-scratch>` the reviewers' scratch directory; nothing else is changed. The build directories themselves are not included.
- `receipt.json` and `repository-recheck-logs.tar.gz`: the repository versions of the 18 files compiled with
  `lean` and replayed with `leanchecker` again, module by module, in two new empty directories on the author's
  Mac (20 November 2026, 21:04–21:16 UTC), together with the other files of Papers 23 to 25 (48 files in all):
  all compiled and passed `leanchecker`, with no warning, identical `.olean` files, and the same axiom lists as in
  Codex's run. The theorems `check_SharpBound` and `Proof.SharpBound` depend exactly on `propext`, `Classical.choice` and `Quot.sound`. The archive, which is
  the same in the three folders `domination-root-radius`, `bar-tiling-defect` and `minkowski-length-simplices`,
  holds the logs of all 48 files, the recheck script and the script that moved the files into the repository.
- The whole project, with these files, was rebuilt for version 1.25.0 (`logs/clean-replay-v1.25.0-receipt.json`).

The statement file, the proofs and the acceptance script were written by OpenAI Codex (model GPT-6.2-Astra).
During development, after the freeze, Codex also compiled files of this package on the author's Windows computer
twice (20 November 2026, 18:27:02–18:29:13 UTC, a partial run that stopped at a compile error, and
18:33:52–18:44:09 UTC, all 18 files, reusing development builds of three modules), in its own directory, while the
rebuild of the whole project for version 1.25.0 was running on that computer; these runs are not part of the evidence here. The final review of the
formal proof was done by an independent Claude Code agent (model Claude Opus 5.5) that had written none of the
files; it compiled the 18 files again in a new directory and replayed every module with `leanchecker`, without
warnings (20 November 2026, about 20:55–20:58 UTC, from its file times). The **erratum** (written by the same
reviewer at 21:26:04 UTC) corrects one sentence of its report about the rejected draft `candidate-01`: it is the
revised, real-coordinate definition, not the rejected one, that needs the hypothesis `0 < n`. The error was found
by the independent review of the paper; it does not affect the frozen statement, the Lean proof or the verdict
APPROVE_FORMAL, and the original report is left unchanged. Claude Code moved the files into the repository,
changed their `import` lines and ran the recheck above. The package is not checked with comparator or nanoda.
