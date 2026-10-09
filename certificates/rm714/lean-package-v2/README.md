# Lean package of Paper 6, version 2

The files of `lean/Research/Backfill/Paper6/` as they were accepted before they were copied into the
release tree (374 modules, copied unchanged), together with the published module
`lean/Research/RM714Weights.lean` of version 1, which the package imports and which is unchanged since
version 1.4.0.

- `ChallengeV3.lean` is the frozen statement file (SHA-256
  `83ea2291d96864401f5147d49e3306e2401d592cc7dc7e4ac171ccda954b6d78`): the file of 36 statements frozen on
  6 October 2026 at 17:13 UTC after an independent review (SHA-256 `e14b3378…`), minus one statement
  (`PropE_counts`, the five numbers of the enumeration of version 1 of the paper), deleted by the
  author's decision on 7 October 2026 and frozen again at 19:01 UTC after a second independent review.
  The headers of both statement files still call them candidates ("NOT FROZEN"); the version history is
  in Section 7 of the paper. `ChallengeV3.lean` imports only Mathlib. `BridgeChallenge.lean` holds the statement `Sec7Bridge`, which compares the
  weight predicate of the module of version 1 with the one defined here; it differs from the frozen file
  (SHA-256 `6c5b7d00…`) only in the module name of its first `import` line. The namespace of both files is
  `BackfillPaper6.V3`.
- `CheckPaper6.lean` proves the 35 statements: for each statement `X` a theorem `check_X` of type
  `BackfillPaper6.V3.X` in the namespace `Paper6FinalPackageV4`. `ChallengeV3Tests.lean` holds the 98
  known-answer tests of the definitions of the statement file, as theorems `test_001` … `test_098`.
- The other 370 modules are the proof modules, written by OpenAI Codex from 6 to 8 October 2026. The
  modules were accepted in twelve groups, each after two builds from empty directories and a review of the
  evidence by a Codex agent that had not written it; the last group on 8 October 2026 at 02:11 UTC.
- `package-manifest.json` records the SHA-256 of every file, the import graph, the toolchain (Lean
  4.34.1) and the Mathlib revision (`d13f23b723b8a846827a245b89c10fc7d3f11612`). It was written before the
  acceptance run in this layout, so its own status fields still say that acceptance is pending.
- `receipt.json`: the acceptance run of the package in this layout (OpenAI Codex, 8 October 2026,
  17:10–20:31 UTC). In two new empty directories, side by side, every one of the 375 modules was compiled
  with the pinned toolchain and Mathlib and then checked with `leanchecker`: 1500 commands, all with exit
  code 0; all 48556 printed axiom lists are subsets of `propext`, `Classical.choice` and `Quot.sound`; the
  98 tests were compiled and checked in both directories. The only diagnostics were two deprecation
  warnings per directory in `RM714Weights.lean` (`if_pos` and `if_neg`, lines 93 and 100), the unchanged
  module of version 1; the other 374 modules compiled without any diagnostic (`diagnostic_exceptions`,
  and the `diagnostics` fields of every step). A Codex agent that had written none of the proofs or
  scripts reviewed the evidence and approved it (21:19 UTC). Earlier the same day the same sources, with
  root-level module names and a copy of `RM714Weights.lean` in which the two deprecated lemma names had
  been replaced, had passed the same checks in two other new empty directories (02:13–05:37 UTC, no
  diagnostic at all; `isolated_package_acceptance`). The file is a summary of the original receipt, whose
  SHA-256 it records; paths in it are relative to the project in which the package was built; they are
  records, not inputs of the build here.
