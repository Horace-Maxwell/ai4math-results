# Paper 9: contents of this folder

Paper: `papers/axial-nonannihilation/note.tex` and `note.pdf` (version 1.8.0).

- `papers/axial-nonannihilation/note.tex`: SHA-256 `a1de5dbaf41ac5701a757993e5cfe2a578ab9a999c15311d6b3c969034a10783`
- `papers/axial-nonannihilation/note.pdf`: SHA-256 `6e02d61590ee5b2efe3a3325f0bae35c3a6b5f4c86ec24232028be96a518f304`

The Lean proofs are in `lean/Research/AxialMSZ/`; they are the verification of
record. The programs here are exact-arithmetic checks made while the examples
were found, reviewed and written up. All of them use Python 3 and exact
rational arithmetic (`fractions.Fraction`); `code2/verify_independent.py`
also uses SymPy for cross-checks.

- `CONTRACT.md`: the statement contract written before the mathematics was
  final: the source questions with their exact wording and locations, and the
  readings considered. It is a working record and may refer to files that are
  not included here.
- `STATEMENTS.md`: every statement of the Lean statement file in words, the
  modelling choices, and the definitions the reader must trust.
- `review/REVIEW-CHALLENGE.md`: the independent review of version 1 of the
  statement file, whose corrections were applied in version 2. It lists some
  facts that the paper does not claim; the paper claims only what is proved in
  Lean.
- `code/`: the first set of programs (`verify_simple.py` for `S`,
  `verify_example.py` for `E`, `verify_block.py` for `D`, with the helper
  modules `axial_tools.py`, `simple_variant.py`, `variants.py` and
  `modp_ideals.py`). Their outputs are in `logs/`. Run each from `code/`.
- `code2/`: a second program (`verify_independent.py`, with `qlinalg.py`),
  written separately, by a different agent, from the mathematical
  specification only. Its output is `logs/verify_independent.out`.
- `paper-check/check_paper.py`: checks every structure constant, eigenvector
  and displayed computation of the paper against the tables of the statement
  file (`lean/Research/AxialMSZ/Challenge.lean`); output `check_paper.out`
  (240 checks). The paper states only what the Lean proofs cover; the script
  checks the displayed numbers.
- `lean-package/`: Codex's description of the Lean package
  (`README-AXIAL.md`), its manifest (`package-manifest.json`) and the receipt
  of its acceptance run (`receipt.json`: 25 modules built from an empty
  directory and checked one by one with `leanchecker`, 28 September 2026,
  00:00–00:10 UTC). In these two JSON files the absolute path of the
  working directory is replaced by `<project>`; the logs they refer to are not
  included. The clean rebuild of the whole repository for this release is
  recorded in `logs/` at the top level.

The outputs in `logs/` were reproduced from this folder on 28 September 2026
before release (identical, apart from the run time printed by
`verify_independent.py`).
