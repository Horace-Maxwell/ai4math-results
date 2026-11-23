# Lean package of Paper 29

The files of `lean/Research/TaskV/Illumination/` (Paper 29: the illumination numbers of the compact convex bodies
between the triangular prism `P = {x ∈ [0,1]³ : x_1 + x_2 ≤ 1}` and the cube `Q = [0,1]³`), seven files (502 lines):
the statement file `Challenge.lean`, the proof modules `Planar.lean`, `Gaps.lean`, `Upper.lean`, `Lower.lean` and
`Result.lean`, and the check file `Check.lean`.

- `package-manifest.json`: the SHA-256 and the imports of the 7 modules, the Lean toolchain, the Mathlib commit, the
  entry point imported by `lean/Research.lean` (`Research.TaskV.Illumination.Check`), the theorem it checks
  (`PrismIllumination.check_trichotomy`), the statement file with its SHA-256 and freeze time, and the 23 declarations
  of Codex's axiom audit with their axioms. For each file it also gives the SHA-256 of the file Codex accepted. The
  files in the repository have module names under `Research.TaskV.Illumination`, keep the namespace
  `PrismIllumination`, and differ from the accepted files only in their `import` lines; `Challenge.lean`, which
  imports only Mathlib, is byte for byte the accepted and frozen file.
- Statement file, written by a Codex agent: `Challenge.lean` (SHA-256 `2fd9927a…be6d`; `cube`, `prism`, `edge`,
  `Illuminates`, `CanLight`, `Exact` and the target `Trichotomy`). It was read against the written proof by two Codex
  agents that had written neither (`positive-route/INDEPENDENT-SANDWICH-STATEMENT.md`, APPROVE_STATEMENT at
  03:52:34 UTC; `literature-cont/REVIEW-MATH-AND-CHALLENGE.md`, APPROVE_MATHEMATICS and APPROVE_STATEMENT_FOR_FREEZE
  at 03:52:38 UTC), compiled with an empty compiler log (`acceptance/preflight-01`, 03:52:56–03:53:15 UTC), and frozen
  on 21 November 2026 at 03:53:24 UTC by recording its SHA-256 (`acceptance/FROZEN.sha256`, `acceptance/FROZEN.utc`).
  The development compilations of the proof files started at 03:54:10 UTC (`acceptance/dev-runs/`). The three examples
  of the paper, the transfer to affine images and the equivalence of the two forms of the definition are not stated in
  these files.
- `codex-acceptance-logs.tar.gz`: Codex's acceptance on the author's Mac with Lean 4.34.1 and the pinned Mathlib, which
  was taken from a prebuilt cache and not rebuilt, on 21 November 2026. The accepted run is `acceptance/dual-02`
  (status `PASS`), with two new empty directories, `normal` and then `fresh`. In each, the runner `verify.py` checked
  that the cached Mathlib imports were present without building them, built every module with
  `lake -v --no-cache --wfail build +M:olean` (warnings fail) and replayed it with `lake env leanchecker M`, built the
  whole package once with `lake --no-cache --wfail build`, and compiled an axiom audit file (`Axioms.lean`, with
  `-DwarningAsError=true`) that prints the axioms of 23 declarations: 17 commands per directory, 34 in all, each ended
  with exit code 0.
  - `normal` started at 04:02:39 UTC. After five compilations (Challenge, Planar, Gaps, Lower, Upper) and four
    replays, the Codex session reached its usage limit during the replay of Upper (about 04:04 UTC); the controller of
    this run (`acceptance/controller-dual-02`) has no exit record. A probe at 04:19:08 UTC
    (`acceptance/serial-recovery-01`) checked the nine finished commands against their receipts (`prefix.json`,
    `check-prefix.py`) but did not resume, because both Lean slots of the Mac were held by a final review of Paper 28. The run was resumed by `resume-dual-02.py` (`acceptance/controller-dual-02-resume-01`, slot acquired at
    04:46:38 UTC, exit 0) from the replay of Upper at 04:47:16 UTC; the empty log of the interrupted replay is kept
    (`normal/logs/Upper-checker.interrupted-0404.log`), and the receipt records the resumption. `normal` ended at
    04:48:35 UTC; `fresh` ran from 04:48:35 to 04:50:54 UTC.
  - The 14 `leanchecker` logs are empty; the Lake logs, which are verbose, contain no warning and no error; the two
    directories produced byte-identical `.olean` files (receipt), and in both the 23 audited declarations, among them
    `PrismIllumination.prism_trichotomy` and `PrismIllumination.check_trichotomy`, depend exactly on `propext`,
    `Classical.choice` and `Quot.sound` (`normal/logs/axioms.log`, `fresh/logs/axioms.log`). A post-audit by the
    resuming session (`controller-dual-02-resume-01/POST-AUDIT.json`, 04:51:00 UTC, script `audit-resumed.py`)
    rechecked the hashes of the sources, the logs and the `.olean` files against the receipt.
  - An earlier attempt (`acceptance/dual-01`, 03:58:33–04:00:49 UTC, one directory) ran 13 commands; 12 ended with exit
    code 0, and the last, the `leanchecker` replay of Result, ended with exit code 1 ("Could not find any oleans for:
    Illumination.Result"), which stopped its runner (`verifier-original.py`; `controller-dual-01`, exit 1). Codex had
    just recorded (`dual-01/RESOURCE-CORRECTION.md`, 04:00:46 UTC) that the batch would stop and that the Lake
    configuration would get the setting `moreLeanArgs = ["-j1"]` (single-threaded compilation); the attempt's previous
    configuration is kept as `lakefile.before-resource-correction.toml`. It is kept on record and is not part of the
    acceptance.

  The archive further holds the freeze records and the two statement reviews named above, the non-author review of the
  seven source files (`acceptance/INDEPENDENT-FORMAL-REVIEW.md`, 03:58 UTC) and its addendum
  (`INDEPENDENT-FORMAL-REVIEW-ADDENDUM.md`, 05:35 UTC, which records that its open last section is superseded by the
  receipt, the post-audit and the final review), the map from statement to proof (`STATEMENT-MAP.md`), the Lake
  configuration (`formal/lakefile.toml`, `formal/lake-manifest.json`, `formal/lean-toolchain`), the scripts
  (`verify.py`, whose SHA-256 `7a7a64ae…` is the one recorded in the receipt, `resume-dual-02.py`, `run-replay.sh`,
  `locked-dev.sh`, `preflight.sh`), Codex's status and completion records (`STATUS.md`, `FINAL-HANDOFF.md`, `DONE`,
  `ACCEPTED.json`), the final review (`FINAL-CLAUDE-REVIEW-01.md`) with Codex's disposition of its remarks
  (`final-response/DISPOSITION.md`) and the final reviewer's own rebuild files (`final-response/claude-rebuild/`:
  `Audit.lean`, `Extra.lean`, `compile.log`, `illum.py`), and the task description of the continuation
  (`task-CONTINUE-MARKOV-ILLUMINATION.md`). It does not hold the written proofs. The brief of the search for problems is not included; the requests of the author that it quotes are given in the repository README. `<workspace>` replaces the local
  project directory and `<claude-scratch>` the reviewers' scratch directory; in the verbose Lake logs, which replay the
  build traces of the prebuilt ProofWidgets cache, `<proofwidgets-build>` replaces the build directory of that
  upstream package and `<e-mail>` an e-mail address in an npm notice. Nothing else is changed. The build directories
  themselves are not included.
- `receipt.json` and `repository-recheck-logs.tar.gz`: the 7 repository files compiled with `lean` and replayed with
  `leanchecker` again, module by module, in two new empty directories on the author's Mac (22 November 2026,
  21:34–21:35 and 21:35–21:36 UTC): all 7 compiled and passed `leanchecker` in each directory, with no warning and no
  error, and identical `.olean` files. The files contain no `#print axioms` command, so this recheck prints no axiom
  lists; the axioms are those of Codex's audit above and of the final reviewer's audit below. The archive holds the
  logs, the recheck script (`mac_compile_generic.py`), the script that moved the files into the repository
  (`integrate_generic.py`) and its record (`illum-integration.json`).
- The whole project, with these files, was rebuilt for version 1.26.0 (`logs/clean-replay-v1.26.0-receipt.json`).

The statement file, the proofs and the acceptance scripts were written by OpenAI Codex (model GPT-6.2-Astra). The final
review was done by a Claude Code agent (model Claude Opus 5.5) that had written none of the files (21 November 2026,
from 04:51:55 UTC). It compiled the seven files again with plain `lean` (with warnings treated as errors) in a new
directory, together with an audit file of its own, and replayed every module with `leanchecker` (04:52:40–04:54:13 UTC);
all ended with exit code 0 and empty output, and the axioms it printed for `check_trichotomy`, `prism_trichotomy` and
the eight main lemmas are exactly `propext`, `Classical.choice` and `Quot.sound`. It also proved in Lean the
equivalence of the two forms of the definition of illumination (`Extra.lean`). Its decision was APPROVE_FORMAL, with
no blocking or major remarks and six minor remarks on the written account. Claude Code moved the files into the
repository, changed their `import` lines and ran the recheck above. The package is not checked with comparator or
nanoda. No human mathematician has read the proofs.
