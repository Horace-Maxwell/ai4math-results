# Lean package of Paper 17

The files of `lean/Research/TaskN/Antichain/` (Paper 17: arbitrarily large antichains of trees of equal order in
the independence polynomial order, Question 6 of Beaton and Cameron, Open J. Discrete Appl. Math. 5 (2022),
Question 5.3 of arXiv:2006.05511v2), 11 files: the statement file `Challenge.lean`, 8 proof modules, `Proof.lean`
and `CheckAntichain.lean`.

- `package-manifest.json`: the SHA-256 and the imports of the 11 modules, the Lean toolchain, the Mathlib commit,
  the entry point imported by `lean/Research.lean`, the two theorems `check_WidthLowerBound` and
  `check_ArbitrarilyLarge` that restate the frozen statements, and the statement file with its SHA-256 and freeze
  time. For each file it also gives the SHA-256 of the file Codex accepted. The files in the repository have
  module names under `Research.TaskN.Antichain` and differ from the accepted files only in their `import` lines
  (Codex built them as a flat package); `Challenge.lean` and `Numeric.lean` have no local imports and are byte
  for byte the accepted ones.
- Statement file: `Challenge.lean` (SHA-256 `fb8861ac…5d58`), reviewed by a Codex agent that had written neither
  the statement nor the proofs and frozen on 20 November 2026, 14:25:12 UTC; the file times and the development
  logs show no proof file before that time. The same agent had checked the reading of the source.
- `codex-acceptance-logs.tar.gz`: Codex's acceptance run on the author's Mac with Lean 4.34.1 and the pinned
  Mathlib, which was taken from a prebuilt cache and not rebuilt, on 20 November 2026, 14:33:01–14:39:43 UTC.
  In each of two new empty directories every module was built with `lake --no-cache --wfail build` (warnings
  fail) and replayed with `leanchecker`, and the whole package was built once: 46 commands (23 per directory),
  all with exit code 0; the `leanchecker` runs printed nothing and the builds nothing except Lake's status lines
  and the requested axiom lists; the `.olean` files of the 11 modules have the same SHA-256 in the two
  directories. The archive also holds the freeze record and review, the frozen copy of the statement file, the
  acceptance record, the final review and the acceptance script. `<workspace>` replaces the local project
  directory and `<claude-scratch>` the reviewers' scratch directory; nothing else is changed. The build directories themselves are not included.
- `receipt.json` and `repository-recheck-logs.tar.gz`: the repository versions of the 11 files compiled with
  `lean` and replayed with `leanchecker` again, module by module, in two new empty directories on the author's
  Mac (20 November 2026, 17:42–17:52 UTC), together with the 12 files of Paper 18: all compiled and passed
  `leanchecker`, with no warning, identical `.olean` files, and the same axiom lists as in Codex's run. The two
  theorems `check_*` and the theorems `Proof.WidthLowerBound` and `Proof.ArbitrarilyLarge` depend exactly on
  `propext`, `Classical.choice` and `Quot.sound`. The archive, which is the same as in
  `certificates/variable-length-parking/lean-package/`, holds the logs of both packages, the recheck script and
  the script that moved the files into the repository.
- The whole project, with these files, was rebuilt for version 1.25.0 (`logs/clean-replay-v1.25.0-receipt.json`).

The statement file, the proofs and the acceptance script were written by OpenAI Codex (model GPT-6.2-Astra).
During development Codex also compiled the files on the author's Windows computer; that run is not part of the
evidence here. The final review of the formal proof was done by an independent Claude Code agent (model Claude
Opus 5.5) that had written none of the files; it compiled the 11 files again in a new directory, with warnings
treated as errors, and replayed every module with `leanchecker` (20 November 2026, 17:17–17:27 UTC). Claude Code
moved the files into the repository, changed their `import` lines and ran the recheck above. The package is not
checked with comparator or nanoda.
