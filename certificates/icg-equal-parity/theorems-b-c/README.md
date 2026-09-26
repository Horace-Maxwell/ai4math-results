# Theorems 4 and 5 of Paper 1 (versions 1.4 and 1.5): programs and logs

Paper: `papers/icg-q3-general/note.pdf`, version 1.5 (Theorem 5 was extended from min{a, b} ≤ 4 to min{a, b} ≤ 8).

- **Theorem 4** (n = p²q^b with b even) has a written proof in Sections 10–11 and is formalised in Lean
  (namespace `ICGEqualParityB`). The programs here are cross-checks.
- **Theorem 5** for 3 ≤ min{a, b} ≤ 8 rests on the certificates below (Section 12). It is not formalised.

Requirements: Python 3. `generic_prover.py` and `generic_prover_fast.py` also need SymPy; `generic_fast2.py` and
`review2/c3_certify.py` use only the standard library.

## Certificates for Theorem 5 (Section 12, paragraph "The certificates")

Run the commands from this directory. Each run ends with the summary line shown; the recorded output is in the log named.

| Command | Expected summary line | Recorded log |
|---|---|---|
| `python3 generic_prover_fast.py 3` | `a=3: certified 14196 tasks, failures 0; direct-check failures 0; …` | `logs/generic_fast_a3.log` |
| `python3 generic_prover_fast.py 4` | `a=4: certified 70416 tasks, failures 0; direct-check failures 0; …` | `logs/generic_fast_a4.log` |
| `python3 generic_fast2.py 3` | `a=3 K=4: counts {…, 'FD1': 4056, …, 'CH': 10140, …}; …; failures 0 …` | `logs/generic_fast2_a3.log` |
| `python3 generic_fast2.py 4` | `a=4 K=4: counts {…, 'FD1': 15648, …, 'CH': 54768, …}; …; failures 0 …` | `logs/generic_fast2_a4.log` |
| `cd review2 && python3 c3_certify.py 3` | `a=3 K=4: checks {…}; failures 0; …` | `review2/logs/c3_certify_a3.log` |
| `cd review2 && python3 c3_certify.py 4` | `a=4 K=4: checks {…}; failures 0; …` | `review2/logs/c3_certify_a4.log` |

- `generic_prover_fast.py` is the parallel driver of `generic_prover.py` (12 worker processes by default). The recorded
  runs took 939 s (a = 3) and 2949 s (a = 4). `logs/generic_a3.log` and `logs/generic_a4.log` are empty; the recorded
  runs for a = 3 and 4 are those of the parallel driver.
- `review2/c3_certify.py` (with `review2/r2poly.py`) is the referee agent's independent certifier. It writes its log to
  `review2/logs/`.
- **Negative controls** (these must report failures):
  - `cd review2 && python3 c3_certify.py 3 4 50 5/4` multiplies the term 2δ_a(p) by 5/4 in every condition; for (F_a)
    this multiplies the right-hand side by 5/4. Recorded result: `failures 4` for a = 3 and for a = 4
    (`review2/logs/c3_certify_a{3,4}_nc_5o4_big-p3.log`).
  - `cd review2 && python3 c3_certify.py 3 4 50 1 nc_P2Q2` uses the region p = 3, q ≥ 3, which contains p = q = 3.
    Recorded result: `failures 4` for a = 3 and `failures 2` for a = 4 (`review2/logs/c3_certify_a{3,4}_nc_1_nc_P2Q2.log`).
  - The other `_nc_` logs are runs with another factor (11/10) or other regions; the regions are listed in
    `review2/r2poly.py`.

## Other checks

- `review2/`: the checks of the paragraph "Checks" of Section 12. These are complete enumeration (`t7_brute_numpy.py`),
  the branch-and-bound search `bnb.py`, its validation (`t5_bnb_validate.py`) and its runs (`t6_bnb_runs.py`,
  `t9_bnb_random.py`). The referee's report is `review2/REVIEW_GENERIC.md`.
- `paper-checks/`: exact checks of the proof of Theorem 25 as written in Sections 10–11 (`check_proof.py`,
  `check_polys.py`, `check_cases.py`, `check_tight.py`) and spot checks of Section 12 (`cheap_check.py`,
  `prop_reduction_spot.py`), with logs in `paper-checks/logs/`. The docstrings use the section and lemma numbers of a draft.
- `review/`: the first referee agent's report (`REVIEW_B.md`) and programs, on an earlier write-up of the proof of Theorem 4.
- `lean-generation/`: generation and audit of the 325 Lean lemmas in the modules `ICGEqualParityBCert1` to
  `ICGEqualParityBCert6`. They are the certificates of the first proof of Theorem 25 (137 corners, 325 polynomial
  inequalities; `prove_fd.py`, `logs/certificates.txt`), which the paper does not need.
- `PROOF-working-note.md`: the working note. It predates version 1.4; its first line explains the numbering.
- The remaining top-level scripts (further checks, and the first proof) are described in the working note.

## a = 5, 6, 7 and 8 (Paper 1, version 1.5)

Version 1.5 of Paper 1 extends Theorem 5 to min(a, b) ≤ 8. For a = 5, 6, 7 and 8 the lists of Proposition 31 were certified
with `generic_fast2.py` (`logs/generic_fast2_a5.log` to `logs/generic_fast2_a8.log`) and with the certifier of the second
referee agent (`review2/logs/c3_certify_a5.log` to `review2/logs/c3_certify_a8.log`); the SymPy prover `generic_prover.py`
was run only for a ≤ 4. A third referee agent (`review3/`, report `review3/REVIEW_A5_8.md`) reran both programs in full,
certified the same lists with its own implementation `review3/rv3_certify.py`, ran negative controls
(`review3/logs/rv3_negctl_*.log`) and 208 exact branch-and-bound checks of the theorem on 17 further shapes
(`review3/logs/rv3_bnb_*.log`). Paths of the form `<project>/…` or `<scratchpad>/…` in the logs of `review3/` are logical
names for the directories of the original runs.
