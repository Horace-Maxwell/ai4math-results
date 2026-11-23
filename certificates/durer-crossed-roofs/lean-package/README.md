# Lean package of Paper 31

The files of `lean/Research/TaskV/Durer/` (Paper 31: an explicit strict edge net for crossed-roof solids, a special
family of convex polyhedra over a parallelogram, in the setting of Dürer's problem, Problem 9 of The Open Problems
Project), 8 files: the statement file `Challenge.lean`, the proof modules `Arc.lean`, `Metric.lean`, `Contacts.lean`,
`Example.lean` and `Proof.lean`, the check file `ExactTests.lean` and the audit file `Audit.lean`, which prints the
definitions of the statement file and the axioms of the two main theorems.

- `package-manifest.json`: the SHA-256 and the imports of the 8 modules, the Lean toolchain, the Mathlib commit, the
  entry point imported by `lean/Research.lean` (`Research.TaskV.Durer.ExactTests`) and the audit module
  `Research.TaskV.Durer.Audit` (which imports `ExactTests` and is not imported by `lean/Research.lean`), the theorems
  whose axioms they print (`DurerDV.checkStrictRoofNet`, `DurerDV.checkObliqueExample`; `DurerDV.strictRoofNet`,
  `DurerDV.obliqueExample`), and the statement file with its SHA-256 and freeze time. For each file it also gives the
  SHA-256 of the file Codex accepted. The files in the repository have module names under `Research.TaskV.Durer`,
  keep the namespace `DurerDV`, and differ from the accepted files only in their `import` lines; `Challenge.lean`,
  which imports only Mathlib, is byte for byte the accepted one and identical to its frozen version.
- Statement file, written by a Codex agent: `Challenge.lean` (SHA-256 `7729aa00…7dfb`; the structures `Profile` and
  `Solid`, the charts and the planar maps `flat`, the relation `welded`, and the targets `StrictRoofNet`, Theorem 1 of
  the paper for every crossed-roof solid with any numbers of roof and floor facets, and `ObliqueExample`, Theorem 2).
  The written proof was approved by a Codex agent that had not developed the construction
  (`crossed-roofs/REVIEW-MATH-01.md`, 03:55:52 UTC); the statement file was compiled without diagnostics
  (03:56:46–03:56:48 UTC), compared with the written proof by a Codex agent that had written neither the statement nor
  the proofs (`crossed-roofs/REVIEW-STATEMENT-01.md`, 03:57:21 UTC; the comparison with the source is
  `crossed-roofs/STATEMENTS.md`), and frozen on 21 November 2026 at 03:57:26 UTC by recording its SHA-256
  (`crossed-roofs/FROZEN-01.sha256`, `crossed-roofs/FROZEN-01.utc`; the record also pins the written proof, the two
  reviews and the compile log of the statement file). According to the development logs no proof file was compiled
  before this time (the earliest proof compilations started at 03:57:57 UTC). What the paper argues in writing only is
  not stated in these files: that the solid is a convex polyhedron with the facets described, that the cut edges form
  a Hamiltonian path, that the cut surface is a disk whose image is a simple polygon (Corollary 1), the reduction to
  `c ≤ 0`, and Section 4 (the rectangular case, the angle check of the oblique example, the comparison with other
  classes).
- `codex-acceptance-logs.tar.gz`: Codex's acceptance runs on the author's Mac with Lean 4.34.1 and the pinned Mathlib,
  which was taken from a prebuilt cache and not rebuilt, on 21 November 2026. In the accepted pair
  (`crossed-roofs/formal/acceptance/coordinate-03-root1` and `coordinate-03-root2`, run by `replay-pair.sh` with
  `replay.py`), in each of two new empty directories, one after the other (04:56:02–04:59:11 and
  04:59:11–05:01:23 UTC), the script printed the Lean version, built every module with `lake build +DV.M:olean`,
  built the whole package once with `lake build`, replayed every module with `leanchecker DV.M`, and ran
  `lean -j1 -R . DV/X.lean` on `ExactTests.lean` and `Audit.lean` to collect the axioms; any nonzero exit code, any
  `warning:` or `error:` in the output, and any output of `leanchecker` counted as a failure. All 40 commands (20 per
  directory) ended with exit code 0; the 16 `leanchecker` logs are empty; the build logs contain only Lake's progress
  and completion lines, in the opening build of each directory two informational lines of Lake (that no build
  manifest existed yet and that the toolchain was up to date), and the output of the `#print` commands of
  `Example.lean`, `ExactTests.lean` and `Audit.lean`; the 8 `.olean` files have the same SHA-256 in the two directories
  (`coordinate-03-pair.json`, `crossed-roofs/COORDINATE-MACHINE.json`). The theorems `strictRoofNet`, `obliqueExample`,
  `checkStrictRoofNet` and `checkObliqueExample` depend exactly on `propext`, `Classical.choice` and `Quot.sound`. The
  archive also keeps two earlier attempts that stopped at the build of the statement file because of setup errors:
  `coordinate-01-root1` (04:55:43–04:55:44 UTC; its Lake configuration listed only `DV.Audit` as a root, and the build
  of `DV.Challenge` ended with exit code 1, "unknown module") and `coordinate-02-root1` (04:55:53–04:55:54 UTC; Mathlib
  was not on the search path, exit code 1). The archive further holds the Lake configurations of the runs, their lock
  and queue records, the development compile logs of the eight files (`crossed-roofs/formal/logs/`, without the logs of
  the two draft statement files described below), Codex's status records (`STATUS.md`, `FINAL-HANDOFF.md`,
  `crossed-roofs/final-response/FINAL-HANDOFF-0501.md`), the final review (`FINAL-CLAUDE-REVIEW-01.md`), Codex's
  record of how it dealt with it (`crossed-roofs/final-response/DISPOSITION.md`, `COORDINATE-FINAL.json`), the
  reviewer's own audit file, compile logs and numerical test program (`crossed-roofs/final-response/audit/`, copied
  there by Codex), and the task description
  `task-CONTINUE-DURER-VIZING.md` (the continuation on Dürer's problem). It does not hold the written proofs. The brief of the search for problems is not included; the requests of the author that it quotes are given in the repository README. Two draft
  statement files of a stronger version (`ShellChallenge.lean`, `ShellChallengeV2.lean`), which were never frozen or
  proved, and their reviews are not part of this package or of the repository. `<workspace>` replaces the local
  project directory and `<claude-scratch>` the reviewers' scratch directory; nothing else is changed. The build
  directories themselves are not included.
- `receipt.json` and `repository-recheck-logs.tar.gz`: the 8 repository files compiled with `lean` and replayed with
  `leanchecker` again, module by module, in two new empty directories on the author's Mac (22 November 2026,
  21:39–21:40 UTC, the two directories one after the other): all 8 compiled and passed `leanchecker` in each
  directory, with no warning and no error, identical `.olean` files, and the same axiom lists as in Codex's runs
  (`propext`, `Classical.choice` and `Quot.sound` for the four theorems above). The archive holds the logs, the
  recheck script (`mac_compile_generic.py`), the script that moved the files into the repository
  (`integrate_generic.py`) and its record (`durer-integration.json`).
- The whole project, with these files, was rebuilt for version 1.26.0 (`logs/clean-replay-v1.26.0-receipt.json`).

The statement file, the proofs and the acceptance scripts were written by OpenAI Codex (model GPT-6.2-Astra). The
final review was done by a Claude Code agent (model Claude Opus 5.5) that had written none of the files (21 November
2026, from 17:03:51 UTC); it compiled the files again with plain `lean` in a new directory, together with an audit file
of its own (which compiled after one corrected import), and replayed every module with `leanchecker`
(17:08:55–17:10:52 UTC). Its decision was APPROVE_WITH_CHANGES, with no blocking remark; its one major remark and six
minor remarks concern the written account (the framing: the rectangular case is covered by O'Rourke's theorem on
Hamiltonian quasigeodesics, the construction is special and elementary, and the search before publication was still
to be done). Claude Code moved the files into the repository, changed their `import` lines and ran the recheck
above. The package is not checked with comparator or nanoda. No human mathematician has read the proofs.
