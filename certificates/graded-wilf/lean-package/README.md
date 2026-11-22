# Lean package of Paper 20

The files of `lean/Research/TaskP/GradedWilf/` (Paper 20: the generalized Wilf conjecture for semigroups graded
by a two-generated numerical semigroup, the class left open in §6 of Cisto and Navarra, An. Ştiinţ. Univ. Ovidius
Constanţa 33 (2025), arXiv:2212.12467v1), 9 files: the statement file `Challenge.lean`, 6 proof modules,
`Proof.lean` and `CheckWilf.lean`.

- `package-manifest.json`: the SHA-256 and the imports of the 9 modules, the Lean toolchain, the Mathlib commit,
  the entry point imported by `lean/Research.lean`, the theorem `check_Wilf` that restates the frozen statement,
  and the statement file with its SHA-256 and freeze time. For each file it also gives the SHA-256 of the file
  Codex accepted. The files in the repository have module names under `Research.TaskP.GradedWilf` and differ
  from the accepted files only in their `import` lines (Codex built them as a flat package); `Challenge.lean` has
  no local imports and is byte for byte the frozen one.
- Statement file: `Challenge.lean` (SHA-256 `b7db38db…83e6`), reviewed by a Codex agent that had not written it
  and frozen on 20 November 2026, 18:04:44 UTC; the file times and the development logs show no proof file
  before that time.
- `codex-acceptance-logs.tar.gz`: Codex's acceptance run on the author's Mac with Lean 4.34.1 and the pinned
  Mathlib, which was taken from a prebuilt cache and not rebuilt, on 20 November 2026, 18:21:29–18:24:32 UTC.
  In each of two new empty directories every module was built with `lake --no-cache --wfail build` (warnings
  fail) and replayed with `leanchecker`, and the whole package was built once: 38 commands (19 per directory),
  all with exit code 0; the `leanchecker` runs printed nothing and the builds nothing except Lake's status lines
  and the requested axiom lists; the `.olean` files of the 9 modules have the same SHA-256 in the two
  directories. The archive also holds the freeze record and review, the frozen copy of the statement file, the acceptance record, the final review and the acceptance script. `<workspace>` replaces the local project
  directory and `<claude-scratch>` the reviewers' scratch directory; nothing else is changed. The build directories themselves are not included.
- `receipt.json` and `repository-recheck-logs.tar.gz`: the repository versions of the 9 files compiled with
  `lean` and replayed with `leanchecker` again, module by module, in two new empty directories on the author's
  Mac (20 November 2026, 19:55–20:07 UTC), together with the other files of Papers 19 to 22 (39 files in all):
  all compiled and passed `leanchecker`, with no warning, identical `.olean` files, and the same axiom lists as in
  Codex's run. The theorems `check_Wilf` and `Proof.Wilf` depend exactly on `propext`, `Classical.choice` and `Quot.sound`. The archive, which is
  the same in the four folders `prime-medial-racks`, `graded-wilf`, `css-covering-equality` and `a7-terrace`,
  holds the logs of all 39 files, the recheck script and the script that moved the files into the repository.
- The whole project, with these files, was rebuilt for version 1.25.0 (`logs/clean-replay-v1.25.0-receipt.json`).

The statement file, the proofs and the acceptance script were written by OpenAI Codex (model GPT-6.2-Astra).
The final review of the formal proof was done by an independent Claude Code agent (model Claude Opus 5.5) that
had written none of the files; it compiled the 9 files again in a new directory, with warnings treated as errors,
and replayed every module with `leanchecker` (20 November 2026, 18:31–18:34 UTC). Claude Code moved the files
into the repository, changed their `import` lines and ran the recheck above. The package is not checked with
comparator or nanoda.
