# Lean package of Paper 8, version 2

The files of `lean/Research/Backfill/Paper8/` as they were accepted before they were copied into the
release tree.

- `package-manifest.json`: the 38 targets, the declaration that proves each of them, the frozen
  statements a proof takes as hypotheses (supplied in `Check.lean`), the SHA-256 of every module
  before and after packaging, the Lean toolchain, the Mathlib revision, and the three modules of
  version 1.7.0 that the proofs import (`Research/SwitchingThmH.lean`, `SwitchingRowCount.lean`,
  `SwitchingWalkProfile.lean`, with their SHA-256). Packaging changed only the module names (`P8.…`
  became `Research.Backfill.Paper8.Proof.…`, in `import` lines and comments); `Check.lean` states one
  `check_X : Challenge.X` for each target. The proofs were written by Claude Code agents on
  29 September 2026.
- `receipt.json`: the acceptance run of the package (Claude Code, 29 September 2026, 18:33–19:05 UTC):
  every module compiled one at a time in an empty directory with Lean 4.34.1 and the pinned Mathlib,
  then replayed with `leanchecker`, twice (a normal and a fresh directory); no warnings; every
  `#print axioms` line lists only `propext`, `Classical.choice` and `Quot.sound`. Paths in these files
  are relative to the project in which the package was built; they are records, not inputs of the
  build here.
- `Proof/Tests/`: further known-answer tests of the definitions of the statement file (158 theorems,
  including instances that must come out false), written after the proofs; they use some lemmas of the
  proofs (for `N_I` and `N_II`). `ChallengeTests.lean` holds the tests written with the statement file.
- The finite search of Proposition 5.5 and the enumeration of Lemma 5.4 are the modules
  `Proof/Region/Chunk1.lean` … `Chunk10.lean`, which the Lean kernel evaluates (`decide +kernel`);
  their computable definitions (`Proof/Region/Defs.lean`) import only Batteries.
- The frozen statement file is `lean/Research/Backfill/Paper8/Challenge.lean`, SHA-256
  `69332eca957449e7613a6c95fa6bda906ecb2fbf688e0dc6ae4bba59fedec715`. Its header mentions internal
  working notes (`STATEMENTS.md`, `REVIEW-CHALLENGE.md`) that are not part of this repository; the
  statements themselves are complete as written.
