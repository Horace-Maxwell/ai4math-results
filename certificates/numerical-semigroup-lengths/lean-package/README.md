# Lean package of Paper 16

The files of `lean/Research/TaskL/Semigroup/` (Paper 16: the decomposition lengths of a numerical semigroup
form an interval, Conjectures 1.1 and 3.9 of García-Sánchez and O'Neill, arXiv:2602.00404v1), 12 files: the
statement file `Challenge.lean`, 9 proof modules, `Proof.lean` and `CheckSemigroup.lean`.

- `package-manifest.json`: the SHA-256 and the imports of the 12 modules, the Lean toolchain, the Mathlib commit,
  the entry point imported by `lean/Research.lean`, the four theorems `check_LengthsExist`,
  `check_LengthsInterval`, `check_PositiveLengthsInterval` and `check_EvenMultiplicityDescent` that restate the
  frozen statements, and the statement file with its SHA-256 and freeze time. For each file it also gives the
  SHA-256 of the file Codex accepted. The files in the repository have module names under
  `Research.TaskL.Semigroup` and differ from the accepted files only in their `import` lines (Codex built them as a
  flat package); `Challenge.lean` has no local imports and is byte for byte the frozen one.
- Statement file: `Challenge.lean` (SHA-256 `a0269ad5…6662`), reviewed by a Codex agent that had not written it
  and frozen on 18 November 2026, 23:47:45 UTC, and the session records and file times show no proof file before that time; that agent then wrote some of
  the proof files.
- `codex-acceptance-logs.tar.gz`: Codex's acceptance run on the author's Mac with Lean 4.34.1 and the pinned
  Mathlib, which was taken from a prebuilt cache and not rebuilt, on 18 November 2026, 23:55:17–23:59:31 UTC.
  In each of two new empty directories every module was built with `lake --no-cache --wfail build` (warnings
  fail) and replayed with `leanchecker`, and the whole package was built once: 50 commands, all with exit code 0;
  the `leanchecker` runs printed nothing and the builds nothing except the requested axiom lists; the `.olean`
  files of the 12 modules have the same SHA-256 in the two directories. The archive also holds the freeze record
  and review, the frozen copy of the statement file, the acceptance record and the acceptance script.
  `<workspace>` replaces the local project directory; nothing else is changed. The build directories themselves
  are not included.
- `receipt.json` and `repository-recheck-logs.tar.gz`: the repository versions of the 12 files compiled with
  `lean` and replayed with `leanchecker` again, module by module, in two new empty directories on the author's
  Mac (19 November 2026, 02:11–02:17 UTC): all compiled and passed `leanchecker`, with no warning, identical
  `.olean` files, and the same axiom lists as in Codex's run. The four theorems `check_*` depend exactly on
  `propext`, `Classical.choice` and `Quot.sound`.
- The whole project, with these files, was rebuilt for version 1.24.0 (`logs/clean-replay-v1.24.0-receipt.json`).

The statement file, the proofs and the acceptance script were written by OpenAI Codex (model GPT-6.2-Astra).
The final review of the formal proof was done by an independent Claude Code agent (model Claude Opus 5.5) that
had written none of the files. Claude Code moved the files into the repository, changed their `import` lines and
ran the recheck above. The package is not checked with comparator or nanoda.
