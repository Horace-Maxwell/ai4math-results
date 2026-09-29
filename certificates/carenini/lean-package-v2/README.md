# Lean package of Paper 3, version 2

The files of `lean/Research/Backfill/Paper3/` as they were accepted before they were copied into the
release tree.

- `package-manifest.json`: the 60 targets, the declaration that proves each of them, the frozen
  statements a proof takes as hypotheses (supplied in `Check.lean`), and the SHA-256 of every module
  and of the two data generators, before and after packaging. Packaging changed only the module names
  (`P3.…` became `Research.Backfill.Paper3.Proof.…`, in `import` lines and comments); `Check.lean`
  states one `check_X : Challenge.X` for each target. The proofs were written by Claude Code agents
  on 29 September 2026.
- `receipt.json`: the acceptance run of the package (Claude Code, 29 September 2026, 03:19–04:16 UTC):
  every module compiled one at a time in an empty directory with Lean 4.34.1 and the pinned Mathlib,
  then replayed with `leanchecker`, twice (a normal and a fresh directory); no warnings; every
  `#print axioms` line lists only `propext`, `Classical.choice` and `Quot.sound`. Paths in these files
  are relative to the project in which the package was built; they are records, not inputs of the
  build here.
- The data generators `Proof/TS/gen/gen_table2.py` (Table 3: representatives, 2-switch certificates,
  profiles) and `Proof/Small/gen/gen_certs6.py` (isomorphism certificates of the 70 labelled cubic
  graphs on six vertices) produce data that the Lean kernel checks; nothing they output is trusted.
- The frozen statement file is `lean/Research/Backfill/Paper3/Challenge.lean`, SHA-256
  `846efb56558f734ba475092854effbe7598549b68e6ea8b7bcad19e9c02d8777`.
- Names: the statement `Table2` (and the data modules `Proof/TS/D*.lean` of its proof) refers to the
  table of Section 8 of the paper, which is Table 3 in both versions of the paper; `Table4Counts` refers
  to Table 4. The statement file mentions internal working notes (`STATEMENTS.md`) that are not part of
  this repository; the statements themselves are complete as written.
