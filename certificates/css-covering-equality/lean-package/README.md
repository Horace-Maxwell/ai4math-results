# Lean package of Paper 21

The files of `lean/Research/TaskR/CSS/` (Paper 21: a non-hollow lattice 4-simplex of covering radius 2 outside the
equality list of Conjecture A of Codenotti, Santos and Schymura, Discrete Comput. Geom. 67 (2022),
arXiv:1903.02866v2), 9 files: the statement file `Challenge.lean`, 6 proof modules, `Proof.lean` and
`CheckCSS.lean`.

- `package-manifest.json`: the SHA-256 and the imports of the 9 modules, the Lean toolchain, the Mathlib commit,
  the entry point imported by `lean/Research.lean`, the four theorems `check_NonHollow`, `check_Radius`,
  `check_Volume` and `check_OutsideList` that restate the frozen statements, and the statement file with its
  SHA-256 and freeze time. For each file it also gives the SHA-256 of the file Codex accepted. The files in the
  repository have module names under `Research.TaskR.CSS` and differ from the accepted files only in their
  `import` lines (Codex built them as a flat package); `Challenge.lean` has no local imports and is byte for byte
  the frozen one.
- Statement file: `Challenge.lean`, version 2 (SHA-256 `1dbf0ce8…8161`), frozen on 20 November 2026, 19:33:34 UTC.
  Version 1 (SHA-256 `7fff04f3…b013`) had been approved at 19:31:21 UTC by a Codex agent that had written neither
  the statement nor any proof, before it was compiled; it then failed to compile because the notation scope
  `ENNReal` was not opened. Version 2 differs only in that `open` line (all definitions and the four target
  lines are byte-identical); it compiled without diagnostics and was approved at 19:33:19 UTC by a second Codex
  agent that had not written the statement or the proofs for this problem. Two proof files were created between
  the first approval and the freeze (`Geometry.lean`, revised afterwards, and `Residues.lean`, which uses no
  definition of the statement file and was not changed afterwards); the development logs record no compilation of
  a proof file before 19:33:41 UTC. That the family `Generated` excluded in `OutsideList` contains every polytope
  of the equality list of Conjecture A is Lemma 4 of the paper, a written argument that is not in Lean.
- `codex-acceptance-logs.tar.gz`: Codex's acceptance run on the author's Mac with Lean 4.34.1 and the pinned
  Mathlib, which was taken from a prebuilt cache and not rebuilt, on 20 November 2026, 19:35:47–19:40:41 UTC.
  In each of two new empty directories every module was built with `lake --no-cache --wfail build` (warnings
  fail) and replayed with `leanchecker`, and the whole package was built once: 38 commands (19 per directory),
  all with exit code 0; the `leanchecker` runs printed nothing and the builds nothing except Lake's status lines
  and the requested axiom lists; the `.olean` files of the 9 modules have the same SHA-256 in the two
  directories. The archive also holds the freeze record, the review of version 1 (`FREEZE-REVIEW.md`), the record of the two versions and of the timing of the proof files (`FREEZE-CHRONOLOGY.md`), the frozen copies of both versions of the statement file, the acceptance record, the final review and the acceptance script, and the review of version 2 (`FREEZE-REVIEW-02.md`). `<workspace>` replaces the local project
  directory and `<claude-scratch>` the reviewers' scratch directory; nothing else is changed. The build directories themselves are not included.
- `receipt.json` and `repository-recheck-logs.tar.gz`: the repository versions of the 9 files compiled with
  `lean` and replayed with `leanchecker` again, module by module, in two new empty directories on the author's
  Mac (20 November 2026, 19:55–20:07 UTC), together with the other files of Papers 19 to 22 (39 files in all):
  all compiled and passed `leanchecker`, with no warning, identical `.olean` files, and the same axiom lists as in
  Codex's run. The four theorems `check_*` and the four theorems `Proof.*` depend exactly on `propext`, `Classical.choice` and `Quot.sound`. The archive, which is
  the same in the four folders `prime-medial-racks`, `graded-wilf`, `css-covering-equality` and `a7-terrace`,
  holds the logs of all 39 files, the recheck script and the script that moved the files into the repository.
- The whole project, with these files, was rebuilt for version 1.25.0 (`logs/clean-replay-v1.25.0-receipt.json`).

The statement file, the proofs and the acceptance script were written by OpenAI Codex (model GPT-6.2-Astra).
The final review of the formal proof was done by an independent Claude Code agent (model Claude Opus 5.5) that
had written none of the files; it compiled the 9 files again in a new directory and replayed every module with
`leanchecker`, with no warnings (20 November 2026, between 19:48 and 19:52 UTC), and judged the difference between
the two versions of the statement file immaterial. Claude Code moved the files into the repository, changed their
`import` lines and ran the recheck above. The package is not checked with comparator or nanoda.
