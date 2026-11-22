# Lean package of Paper 22

The files of `lean/Research/TaskR/A7/` (Paper 22: a terrace for the alternating group `A_7`, a case of Bailey's
conjecture as stated in Ollis's survey, Electron. J. Combin. DS10 (2025), Conjecture 33), 8 files: the statement
file `Challenge.lean`, 5 proof modules (among them `Data.lean`, which stores the terrace, and `Cert.lean`, whose
79 block theorems have the kernel evaluate the checks), `Proof.lean` and `CheckA7.lean`.

- `package-manifest.json`: the SHA-256 and the imports of the 8 modules, the Lean toolchain, the Mathlib commit,
  the entry point imported by `lean/Research.lean`, the theorem `check_HasTerrace` that restates the frozen
  statement, and the statement file with its SHA-256 and freeze time. For each file it also gives the SHA-256 of
  the file Codex accepted. The files in the repository have module names under `Research.TaskR.A7` and differ
  from the accepted files only in their `import` lines (Codex built them as a flat package); `Challenge.lean` and
  `Data.lean` have no local imports and are byte for byte the accepted ones.
- Statement file: `Challenge.lean` (SHA-256 `27895ac5…37bb`), reviewed by a Codex agent that had taken no part in
  finding the terrace and had written neither the statement nor the proofs, and frozen on 20 November 2026,
  19:32:16 UTC; the development logs record only a compilation of the statement file itself before that time.
  The terrace had been found before, in the search for problems; the statement does not contain it.
- `codex-acceptance-logs.tar.gz`: Codex's acceptance run on the author's Mac with Lean 4.34.1 and the pinned
  Mathlib, which was taken from a prebuilt cache and not rebuilt, on 20 November 2026, 19:36:16–19:40:35 UTC.
  In each of two new empty directories every module was built with `lake --no-cache --wfail build` (warnings
  fail) and replayed with `leanchecker`, and the whole package was built once: 34 commands (17 per directory),
  all with exit code 0; the `leanchecker` runs printed nothing and the builds nothing except Lake's status lines
  and the requested axiom lists; the `.olean` files of the 8 modules have the same SHA-256 in the two
  directories. The archive also holds the freeze record and review, the frozen copy of the statement file, the acceptance record, the final review the acceptance script and the encoder `generate.py`, which writes `Data.lean` and `Cert.lean` from Codex's witness. `<workspace>` replaces the local project
  directory and `<claude-scratch>` the reviewers' scratch directory; nothing else is changed. The build directories themselves are not included.
- `receipt.json` and `repository-recheck-logs.tar.gz`: the repository versions of the 8 files compiled with
  `lean` and replayed with `leanchecker` again, module by module, in two new empty directories on the author's
  Mac (20 November 2026, 19:55–20:07 UTC), together with the other files of Papers 19 to 22 (39 files in all):
  all compiled and passed `leanchecker`, with no warning, identical `.olean` files, and the same axiom lists as in
  Codex's run. The theorems `check_HasTerrace` and `Proof.HasTerrace` depend exactly on `propext`, `Classical.choice` and `Quot.sound`. The archive, which is
  the same in the four folders `prime-medial-racks`, `graded-wilf`, `css-covering-equality` and `a7-terrace`,
  holds the logs of all 39 files, the recheck script and the script that moved the files into the repository.
- The whole project, with these files, was rebuilt for version 1.25.0 (`logs/clean-replay-v1.25.0-receipt.json`).

The statement file, the proofs, the encoder and the acceptance script were written by OpenAI Codex (model
GPT-6.2-Astra), which also found the terrace with a search program that is not included. The final review of the
formal proof was done by an independent Claude Code agent (model Claude Opus 5.5) that had written none of the
files; it compiled the 8 files again with `lean` in a new directory and replayed every module with `leanchecker`
(20 November 2026, 19:43–19:45 UTC), and checked the terrace in Python from `Data.lean`. Claude Code moved the files
into the repository, changed their `import` lines and ran the recheck above. The package is not checked with
comparator or nanoda.
