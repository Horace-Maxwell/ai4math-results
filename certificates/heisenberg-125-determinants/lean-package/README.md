# Lean package of Paper 27

The files of `lean/Research/TaskU/` (Paper 27: the integer group determinants of the Heisenberg group of order 125;
the question of Olga Taussky-Todd for this group, after Mossinghoff and Pinner, Michigan Math. J. 74 (2024),
arXiv:2108.04870v1), 63 files in one package for both statement files: in `H5/` the 37 files of the minimum
(Corollary 1 of the paper), that is, the statement file `Challenge.lean`, 33 proof modules, the audit file `Audit.lean`
and the check files `CheckWitness.lean` and `Check.lean`; in `H5B/` the 26 further files of the classification
(Theorem 1), that is, the statement file `ChallengeB.lean`, 23 proof modules, `ProofB.lean` and `CheckB.lean`.

- `package-manifest.json`: the SHA-256 and the imports of the 63 modules, the Lean toolchain, the Mathlib commit, the
  two entry points imported by `lean/Research.lean` (`Research.TaskU.H5.Check` and `Research.TaskU.H5B.CheckB`), the
  theorems they check (`TaskU.H5.Check.check_witnessValue`, `TaskU.H5.Check.check_leastPositiveMultiple` and
  `TaskU.H5.check_fullSpectrum`), and the two statement files with their SHA-256 and freeze times. For each file it
  also gives the SHA-256 of the file Codex accepted. The files in the repository have module names under
  `Research.TaskU` and differ from the accepted files only in their `import` lines; the four files that import only
  Mathlib (`H5/Challenge.lean`, `H5/Cyc5.lean`, `H5/WitnessRows.lean` and `H5B/PrimeOrbit.lean`) are byte for byte
  the accepted ones. Of the two statement files, `Challenge.lean` is therefore identical to its frozen version, and
  `ChallengeB.lean` differs from its frozen version (SHA-256 `2a5066bf…9ea6`) only in its two `import` lines (repository
  SHA-256 `f49432a2…7263`).
- Statement files, written by Codex agents: `H5/Challenge.lean` (SHA-256 `9a9a0e18…1343`; the group `H` of order 125,
  the witness `1 + x + y + y² + xy²`, `groupDet`, and the targets `witnessValue` and `leastPositiveMultiple`) and
  `H5B/ChallengeB.lean` (frozen SHA-256 `2a5066bf…9ea6`; `congrFive`, `unitImage`, `visible` and the target
  `fullSpectrum`, using `H` and `groupDet` and the definitions `Cyc5.V`, `Cyc5.mul` and `Cyc5.norm` of `H5/Cyc5.lean`).
  Each was compiled without diagnostics, checked against the source by a Codex agent that had not written it
  (`FREEZE-REVIEW.md`, APPROVE_FREEZE at 01:31:57 UTC; `b/FREEZE-REVIEW-B.md`, APPROVE_FREEZE at 03:22:01 UTC), and
  frozen on 21 November 2026: `Challenge.lean` at 01:32:25 UTC (`FREEZE.json`) and `ChallengeB.lean` at 03:22:48 UTC
  (`FREEZE-B.json`, which also records the SHA-256 of the 37 accepted files of the minimum, so that they could not
  change). According to the development logs no proof file was compiled before these times. Corollary 2 of the paper
  (the exponent 33, a two-line deduction from Theorem 1), Remark 1 and Lemma 2 (the choice independence of visibility,
  not needed for Theorem 1) are not stated in these files.
- `codex-acceptance-logs.tar.gz`: Codex's acceptance runs on the author's Mac with Lean 4.34.1 and the pinned Mathlib,
  which was taken from a prebuilt cache and not rebuilt, on 21 November 2026. In each completed run, in each of two new
  empty directories, every module was built with `lake --no-cache --wfail build +M:olean` (warnings fail) and replayed
  with `lake env leanchecker M`, and the whole package was built once with `lake --no-cache --wfail build`:
  - the witness alone (`acceptance/witness/2026-11-21T013430Z`, 6 modules, status `MACHINE_PASS_WITNESS_ONLY`),
    01:34:30–01:36:41 UTC, 26 commands, a preliminary run for `witnessValue`;
  - the minimum (`acceptance/both/2026-11-21T014255Z`, 37 modules, both targets of `Challenge.lean`),
    01:42:55–01:56:09 UTC (the two directories one after the other, 01:42:55–01:50:02 and 01:50:03–01:56:09),
    150 commands;
  - the classification (`acceptance/spectrum/2026-11-21T033317Z`, all 63 modules, the target of `ChallengeB.lean`;
    the 37 files of the minimum with the SHA-256 accepted before), 03:33:17–03:55:22 UTC (the two directories side by
    side), 254 commands.

  All 430 commands ended with exit code 0; the 212 `leanchecker` logs are empty; the build logs contain only the
  axiom lines, Lake's progress and completion lines and, in the opening build of each directory, two informational lines
  of Lake (that no build manifest existed yet and that the toolchain was up to date); in each run the `.olean` files
  have the same SHA-256 in the two directories, and the axiom lists agree. The theorems `Proof.witnessValue`,
  `Proof.leastPositiveMultiple`, `ProofB.fullSpectrum` and the three check theorems depend exactly on `propext`,
  `Classical.choice` and `Quot.sound`; two lemmas of `Audit.lean` depend on fewer. The archive also keeps an attempt
  at the minimum that was started 35 seconds before the accepted run (`acceptance/both/2026-11-21T014220Z`, status
  `INCOMPLETE`, 01:42:20–01:42:21 UTC): its acceptance script stopped after one build command (which itself ended
  with exit code 0) because it did not recognize the two informational lines of Lake described above. According
  to Codex's status record the script was corrected only in this respect before the accepted run; the receipts give
  the SHA-256 of both versions of the script, and the archive holds the corrected one (`accept_h5.py`). The archive
  further holds the freeze records and reviews (`FREEZE.json`, `FREEZE-REVIEW.md`, `FREEZE-B.json`,
  `b/FREEZE-REVIEW-B.md`), the comparisons with the source (`SOURCE-CHECK.md`, `b/FORMAL-SOURCE-B.md`), the
  post-checks of the two main runs (`postcheck.json`, and `POST-REVIEW.md` and `verify_receipt.py` for the minimum),
  the acceptance script of the classification run (`accept_h5b.py`, whose SHA-256 `1dd7387e…` is the one recorded in
  its receipt) and its receipt checker (`verify_h5b_receipt.py`),
  Codex's completion marks (`DONE`, `DONE-B`), the task description (`task-BRIEF.md`) and the three final reviews
  (`FINAL-CLAUDE-REVIEW-01.md` for the minimum, `FINAL-CLAUDE-REVIEW-B-01.md` and `FINAL-CLAUDE-REVIEW-B-02.md` for
  the classification). It does not hold the written proofs. `<workspace>` replaces the local project directory and
  `<claude-scratch>` the reviewers' scratch directory; nothing else is changed. The build directories themselves are
  not included.
- `receipt.json` and `repository-recheck-logs.tar.gz`: the 63 repository files compiled with `lean` and replayed with
  `leanchecker` again, module by module, in two new empty directories on the author's Mac (21 November 2026,
  17:02–17:13 and 17:13–17:22 UTC): all 63 compiled and passed `leanchecker` in each directory, with no warning and no
  error, identical `.olean` files, and the same 16 axiom lists as in Codex's run of the classification. The archive
  holds the logs, the recheck script (`mac_compile_h5.py`) and the script that moved the files into the repository
  (`integrate_h5.py`).
- The whole project, with these files, was rebuilt for version 1.25.0 (`logs/clean-replay-v1.25.0-receipt.json`).

The statement files, the proofs and the acceptance scripts were written by OpenAI Codex (model GPT-6.2-Astra). The
final reviews were done by Claude Code agents (model Claude Opus 5.5) that had written none of the files: one for the
minimum (21 November 2026, 03:20–03:27 UTC) and, because of the significance of the result, two independent ones for
the classification (03:57–04:55 UTC), neither of which read the other's report. Each reviewer compiled the files again
with plain `lean` in a new directory, together with an audit file of its own, and replayed every module with
`leanchecker`; all three decisions were APPROVE_FORMAL. Claude Code moved the files into the repository, changed their
`import` lines and ran the recheck above. The package is not checked with comparator or nanoda. No human
mathematician has read the proofs.
