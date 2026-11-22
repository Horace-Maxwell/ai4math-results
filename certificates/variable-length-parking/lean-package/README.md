# Lean package of Paper 18

The files of `lean/Research/TaskN/Parking/` (Paper 18: the equality case of Chen's bound for invariant parking with
one special preference, Theorem E(b) of D. M. Chen, arXiv:2311.15699v1, and a count of the first-car lengths that
attain it), 12 files: the statement file `Challenge.lean`, 9 proof modules, `Proof.lean` and `CheckParking.lean`.

- `package-manifest.json`: the SHA-256 and the imports of the 12 modules, the Lean toolchain, the Mathlib commit,
  the entry point imported by `lean/Research.lean`, the two theorems `check_ExtremalClassification` and
  `check_FirstLengthCount` that restate the frozen statements, and the statement file with its SHA-256 and freeze
  time. For each file it also gives the SHA-256 of the file Codex accepted. The files in the repository have
  module names under `Research.TaskN.Parking` and differ from the accepted files only in their `import` lines
  (Codex built them as a flat package); `Challenge.lean` has no local imports and is byte for byte the frozen one.
- Statement file: `Challenge.lean` (SHA-256 `7f0d8043…e46e`), reviewed by a Codex agent that had not written it
  and had not worked on this problem before, and frozen on 20 November 2026, 14:25:56 UTC; the development logs
  record no compilation of a proof file before that time (the first is at 14:26:55 UTC). The same agent had
  checked the reading of the source.
- `codex-acceptance-logs.tar.gz`: Codex's acceptance run on the author's Mac with Lean 4.34.1 and the pinned
  Mathlib, which was taken from a prebuilt cache and not rebuilt, on 20 November 2026, 14:35:13–14:43:32 UTC.
  In each of two new empty directories every module was built with `lake --no-cache --wfail build` (warnings
  fail) and replayed with `leanchecker`, and the whole package was built once: 50 commands (25 per directory),
  all with exit code 0; the `leanchecker` runs printed nothing and the builds nothing except Lake's status lines
  and the requested axiom lists; the `.olean` files of the 12 modules have the same SHA-256 in the two
  directories. The archive also holds the freeze record and review, the frozen copy of the statement file, the
  acceptance record, the final review and the acceptance script. `<workspace>` replaces the local project
  directory and `<claude-scratch>` the reviewers' scratch directory; nothing else is changed. The build directories themselves are not included.
- `receipt.json` and `repository-recheck-logs.tar.gz`: the repository versions of the 12 files compiled with
  `lean` and replayed with `leanchecker` again, module by module, in two new empty directories on the author's
  Mac (20 November 2026, 17:42–17:52 UTC), together with the 11 files of Paper 17: all compiled and passed
  `leanchecker`, with no warning, identical `.olean` files, and the same axiom lists as in Codex's run. The two
  theorems `check_*` and the theorems `Proof.ExtremalClassification` and `Proof.FirstLengthCount` depend exactly
  on `propext`, `Classical.choice` and `Quot.sound`. The archive, which is the same as in
  `certificates/tree-antichains/lean-package/`, holds the logs of both packages, the recheck script and the script
  that moved the files into the repository.
- The whole project, with these files, was rebuilt for version 1.25.0 (`logs/clean-replay-v1.25.0-receipt.json`).

The statement file, the proofs and the acceptance script were written by OpenAI Codex (model GPT-6.2-Astra).
During development Codex also compiled the files on the author's Windows computer; that run is not part of the
evidence here. The final review of the formal proof was done by an independent Claude Code agent (model Claude
Opus 5.5) that had written none of the files; it compiled the 12 files again in a new directory, with warnings
treated as errors, and replayed every module with `leanchecker` (20 November 2026, 17:19–17:26 UTC). Claude Code
moved the files into the repository, changed their `import` lines and ran the recheck above. The package is not
checked with comparator or nanoda.
