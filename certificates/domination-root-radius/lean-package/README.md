# Lean package of Paper 23

The files of `lean/Research/TaskP/RootRadius/` (Paper 23: the largest domination roots of friendship graphs and of
joins with repeated petals, Question 3.2 of Alikhani, Brown and Jahari, Filomat 30 (2016)), 14 files: the
statement file `Challenge.lean`, 11 proof modules, `Proof.lean` and `CheckRootRadius.lean`. The Lean namespace is
`TaskP.GraphRootRadius`.

- `package-manifest.json`: the SHA-256 and the imports of the 14 modules, the Lean toolchain, the Mathlib commit,
  the entry point imported by `lean/Research.lean`, the three theorems `check_Attainment`,
  `check_GeneralAsymptotic` and `check_FriendshipAsymptotic` that restate the frozen statements, and the statement
  file with its SHA-256 and freeze time. For each file it also gives the SHA-256 of the file Codex accepted. The
  files in the repository have module names under `Research.TaskP.RootRadius` and differ from the accepted files
  only in their `import` lines (Codex built them as a flat package); `Challenge.lean` and `DiskZero.lean` have no
  local imports and are byte for byte the accepted ones.
- Statement file: `Challenge.lean` (SHA-256 `d6663c9f…222d`), reviewed by a Codex agent that had taken part
  neither in the proof nor in drafting the statement, and frozen on 20 November 2026, 18:06:37 UTC; the file times
  and the development logs show no proof file before that time. The statements are limits as `m → ∞`; they give
  no explicit bound for a fixed `m`.
- `codex-acceptance-logs.tar.gz`: Codex's acceptance run on the author's Mac with Lean 4.34.1 and the pinned
  Mathlib, which was taken from a prebuilt cache and not rebuilt, on 20 November 2026, 18:24:47–18:29:53 UTC.
  In each of two new empty directories every module was built with `lake --no-cache --wfail build` (warnings
  fail) and replayed with `leanchecker`, and the whole package was built once: 58 commands (29 per directory),
  all with exit code 0; the `leanchecker` runs printed nothing and the builds nothing except Lake's status lines
  and the requested axiom lists; the `.olean` files of the 14 modules have the same SHA-256 in the two
  directories. The archive also holds the freeze record and review, the frozen copy of the statement file, the acceptance record, the final review and the acceptance script. `<workspace>` replaces the local project
  directory and `<claude-scratch>` the reviewers' scratch directory; nothing else is changed. The build directories themselves are not included.
- `receipt.json` and `repository-recheck-logs.tar.gz`: the repository versions of the 14 files compiled with
  `lean` and replayed with `leanchecker` again, module by module, in two new empty directories on the author's
  Mac (20 November 2026, 21:04–21:16 UTC), together with the other files of Papers 23 to 25 (48 files in all):
  all compiled and passed `leanchecker`, with no warning, identical `.olean` files, and the same axiom lists as in
  Codex's run. The three theorems `check_*` and the three theorems `Proof.*` depend exactly on `propext`, `Classical.choice` and `Quot.sound`. The archive, which is
  the same in the three folders `domination-root-radius`, `bar-tiling-defect` and `minkowski-length-simplices`,
  holds the logs of all 48 files, the recheck script and the script that moved the files into the repository.
- The whole project, with these files, was rebuilt for version 1.25.0 (`logs/clean-replay-v1.25.0-receipt.json`).

The statement file, the proofs and the acceptance script were written by OpenAI Codex (model GPT-6.2-Astra).
The final review of the formal proof was done by an independent Claude Code agent (model Claude Opus 5.5) that
had written none of the files; it compiled the 14 files again in a new directory with its own script and replayed
every module with `leanchecker` (20 November 2026, about 20:53–20:56 UTC, from its file times). Claude Code moved
the files into the repository, changed their `import` lines and ran the recheck above. The package is not checked
with comparator or nanoda.
