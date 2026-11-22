# Lean package of Paper 26

The files of `lean/Research/TaskS/` (Paper 26: covering minima of the standard terminal simplex and a discrete
surface area bound for the covering radius of simplices; Conjecture B of González Merino and Schymura, Discrete
Comput. Geom. 58 (2017), stated as Conjecture B by Codenotti, Santos and Schymura, and Conjecture C of Codenotti,
Santos and Schymura, Discrete Comput. Geom. 67 (2022), arXiv:1903.02866v2), 25 files in one package for both
statements: in `B/` the statement file `Challenge.lean`, 8 proof modules, `Proof.lean` and `CheckB.lean`; in `C/`
the statement file `Challenge.lean`, 9 proof modules, `Proof.lean`, `CheckC.lean` and `MeasureAudit/CheckC.lean`;
and `Shared/Sawtooth.lean`, the averaging lemma used by both.

- `package-manifest.json`: the SHA-256 and the imports of the 25 modules, the Lean toolchain, the Mathlib commit,
  the three entry points imported by `lean/Research.lean` (`Research.TaskS.B.CheckB`, `Research.TaskS.C.CheckC`
  and `Research.TaskS.C.MeasureAudit.CheckC`), the theorems they check (`check_ConjectureB`, `check_conjectureC`,
  and in `MeasureAudit/CheckC.lean` also `measured_conjectureC`, the measured form of Theorem 2′, and the lemmas
  identifying the projected volumes), and the two statement files with their SHA-256 and freeze times. For each
  file it also gives the SHA-256 of the file Codex accepted. The files in the repository have module names under
  `Research.TaskS` and differ from the accepted files only in their `import` lines; the two statement files,
  `B/RationalLine.lean`, `B/Split.lean` and `Shared/Sawtooth.lean` are byte for byte the accepted ones.
- Statement files: `B/Challenge.lean` (SHA-256 `458363b3…58b7`) and `C/Challenge.lean` (SHA-256 `607e2915…1a57e`),
  written by Codex agents. A Codex agent that had written neither statement and had not taken part in the earlier
  search for problems checked the reading of the sources and reviewed both files, after checking that each compiled
  without diagnostics; both were frozen on 20 November 2026, 22:30:34 UTC. According to the development logs no proof
  file was compiled before 22:30:49 UTC. Corollary 3 of the paper, the d/2 bound of Conjecture A, is not stated in
  these files.
- `codex-acceptance-logs.tar.gz`: Codex's three acceptance runs on the author's Mac with Lean 4.34.1 and the pinned
  Mathlib, which was taken from a prebuilt cache and not rebuilt, on 20 November 2026. In each run, in each of two
  new empty directories, every module was built with `lake --no-cache --wfail build` (warnings fail) and replayed
  with `leanchecker`, and the whole package was built once:
  - Theorem 1 (`conj-b/acceptance/2026-11-20T223418Z`, 12 modules: the files of `B/` and `Sawtooth.lean`),
    22:34:18–22:39:44 UTC, 50 commands;
  - Theorem 2 (`conj-c/acceptance/2026-11-20T223322Z`, 9 modules), 22:33:22–22:37:34 UTC, 38 commands;
  - Theorem 2′ (`conj-c/acceptance/2026-11-20T223851Z`, 14 modules, including the 9 unchanged modules of
    Theorem 2), 22:38:51–22:44:28 UTC, 58 commands.

  All 146 commands ended with exit code 0; the `leanchecker` runs printed nothing; in each run the `.olean` files
  have the same SHA-256 in the two directories. The archive also holds, for each conjecture, the freeze record and
  review, the frozen copy of the statement file, the acceptance configuration and the two final reviews
  (`FINAL-CLAUDE-REVIEW-01.md` and `-02.md`), as well as the acceptance and post-check scripts and the task
  description. `<workspace>` replaces the local project directory,
  `<claude-scratch>` the reviewers' scratch directory and `<windows-workspace>` the working directory of Claude Code
  on the author's Windows computer; nothing else is changed. The build directories
  themselves are not included.
- `receipt.json` and `repository-recheck-logs.tar.gz`: the 25 repository files compiled with `lean` and replayed with
  `leanchecker` again, module by module, in two new empty directories on the author's Mac (20 November 2026,
  23:11–23:18 UTC): all compiled and passed `leanchecker`, with no warning, identical `.olean` files, and the same
  axiom lists as in Codex's runs. The theorems `Proof.ConjectureB`, `check_ConjectureB`, `Proof.conjectureC`,
  `check_conjectureC`, `measured_conjectureC` and the audited lemmas depend exactly on `propext`, `Classical.choice`
  and `Quot.sound`. The archive holds the logs, the recheck script and the script that moved the files into the
  repository.
- The whole project, with these files, was rebuilt for version 1.25.0 (`logs/clean-replay-v1.25.0-receipt.json`).

The statement files, the proofs and the acceptance scripts were written by OpenAI Codex (model GPT-6.2-Astra).
Because of the significance of the results, each of the two theorems had two independent final reviews by Claude
Code agents (model Claude Opus 5.5) that had written none of the files, four in all (20 November 2026, 22:43–23:16
UTC); each second reviewer read the first report only after writing its own analysis. Each reviewer compiled the
files again with plain `lean` in a new directory and replayed every module with `leanchecker`; all four decisions
were APPROVE_FORMAL. Claude Code moved the files into the repository, changed their `import` lines and ran the
recheck above. The package is not checked with comparator or nanoda. No human mathematician has read the proofs.
