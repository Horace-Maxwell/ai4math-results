# The maximal energy of integral circulant graphs of order p^(2r)·3^(2s+1), and Hanna's OEIS congruence conjectures (eleven proved, three more resolved), with Lean 4 proofs

This repository contains two papers, their Lean 4 formalizations and
computational certificates. It is archived on Zenodo:
[10.5281/zenodo.22970254](https://doi.org/10.5281/zenodo.22970254) (all
versions; version 1.0.0 is
[10.5281/zenodo.22970255](https://doi.org/10.5281/zenodo.22970255)).

**Paper 1: [`papers/icg-q3-general`](papers/icg-q3-general/note.pdf).**
*The maximal energy of integral circulant graphs of order p^(2r)·3^(2s+1).*

- Jiang and Yang (arXiv:2608.29523, Theorem A) determined the maximal energy
  of integral circulant graphs of order `p^(2r) q^(2s+1)` for distinct odd
  primes with `q ≥ 5`. They noted that `q = 3` is not covered by their method.
- We prove the remaining case `q = 3`: for every prime `p ≥ 5` and all
  `r ≥ 1`, `s ≥ 0`, the checkerboard set `{p^i 3^j : i + j even}` is the
  unique energy maximiser, and the maximal energy is given by their formula.
- The key step is a sign-matrix inequality for weighted Ramanujan transforms,
  proved by a path identity and an explicit potential. It also gives a proof
  of Jiang–Yang's theorem without semidefinite certificates.
- **Lean:** `ICGGeneral.jiang_yang_q3`, starting from the adjacency matrix of
  the graph and its eigenvalues, and `ICGGeneral.jiang_yang_thmA`, which
  covers all pairs of distinct odd primes. The paper also states a conjecture
  for exponents of equal parity; it is not proved.

**Paper 2: [`papers/oeis-hanna`](papers/oeis-hanna/note.pdf).** *Proofs of
eleven congruence conjectures of Hanna from the OEIS, and the resolution of
three more.*

**Also included:** a complete Lean formalization of the case q = 3 of
Roldán's Conjecture 1.3 (order `27p²`). This is a known result, proved earlier
by others; see below.


### Formalization of a known result: the case q = 3 of Roldán's Conjecture 1.3 (arXiv:2604.09491)

- For every prime `p ≥ 5`, the divisor set `D* = {1, 9, 3p, 27p, p², 9p²}`
  uniquely maximizes the energy of the integral circulant graph `ICG(27p², D)`.
- **This case was proved before us:**
  - S. Park (PDF posted 2026-08-21 at github.com/coshaman/papers) claims the
    whole conjecture;
  - J. A. Schreib (2026-09-05, github.com/jamesschreib/roldan-universality-conjecture)
    gives a written proof of the case q = 3 with the same bound
    `E(D*) − E(D) ≥ 24(p² − 2p + 2)`;
  - an arithmetic certificate was also announced in trureturing issue #8338
    (2026-09-16).
- **What this repository adds:**
  - a complete Lean 4 formalization, from the adjacency matrix of the graph and
    its eigenvalues, with no additional axioms and no `native_decide`;
  - the observation, also formalized, that the bound is attained at
    `D* ∪ {3p²}`, so the second-largest energy is `242p² − 356p + 154`.

### Paper 2 in detail

**Eleven congruence conjectures of P. D. Hanna from the OEIS**, proved and
formally verified. Each Lean theorem holds for every integer power series
satisfying the defining equation, with only the normalizations forced by the
entry's offset.

| Entry | Defining equation | Theorem |
| --- | --- | --- |
| A389472 | `A(x² + x³) = x²(1 + A(x))` | `3 ∣ a(3n − 1)` for `n > 1` |
| A240998 | `A(x)² = x + A(x + 2x²)` | for `n ≥ 1`, `a(n)` is odd iff `n` is a power of 2 |
| A295762 | `A(x − 2A(x²)) = x + A(x²)` | for `n ≥ 1`, `a(n)` is odd iff `n` is a power of 2 (the entry conjectures one direction) |
| A273958 | `xA + x²A² = C²`, with `C = x + C²` | `a(n)` is odd iff `n = 2·4^k − 1` |
| A301933 | `A = x(1 + 4AA′)/(1 + AA′)` | `a(n)` is odd iff `n` is a power of 2 |
| A377100 | `A(x) = A(x³)/A(x²) + A(x)²` | `a(n) ≡ 1 (mod 3)` for `n ≥ 1` |
| A274479 | `A(x)² = A(x²/(1 − 2x − 4x²))` | `a(n) ≡ 1 (mod 3)` for `n ≥ 1` |
| A388734 | `A = 1 + xA² + x²(1 − x)A³` | every `a(n)` is odd |
| A338633 | `1 = A − x/(A − 2³x/(A − 3³x/(A − …)))` | for `n > 0`, `a(n)` is odd iff `n` is a power of 2 |
| A338634 | `1 = A − x/(A − 2⁴x/(A − 3⁴x/(A − …)))` | for `n > 0`, `a(n)` is odd iff `n` is a power of 2 |
| A120566 | `A(x) = A(A(x)) − x·A(A(A(x)))` | every `a(n)`, `n ≥ 1`, is odd |

**Three further OEIS conjectures, resolved:**

| Entry | Conjecture | What is proved |
| --- | --- | --- |
| A184894 | `a(m) ≡ 0 (mod 3)` except at `m = (3^n + 1)/2` | the statement as written (vanishing outside the exceptions) holds, and `a(m) ≡ C(m, j) (mod 3)` when `2m − 1 = 3^j`; the stronger reading "non-zero at every exception" fails at OEIS index 365 = (3⁶ + 1)/2 |
| A107099 | `[x^n]A ≡ 0 (mod 3)` except at `n = 3^k`, where `A(A(x)) = x + 4x³` | the statement as written holds; the stronger reading fails at `x^729` (OEIS index 364), since `3 ∣ [x^729]A` |
| A361047 | stated with an index slip that the entry's own data contradict | the intended statement, in exponent form: `[x^m]A ≡ 1 (mod 3)` if `m = 3^k`, and `≡ 0` otherwise |

## What is verified, and how

| Claim | Lean 4 declarations | Independent computation |
| --- | --- | --- |
| Paper 1: unique maximiser for `p^(2r)·3^(2s+1)`, `p ≥ 5`; value of the maximum, expressed through the norms `d_k(x) = ‖T_k(x) s_k‖₁` (their closed form is proved in the paper but not formalized); the sign-matrix inequality (all real `p ≥ 5`, `q ≥ 3`, all exponents); energy formula for all `p^a q^b`; Jiang–Yang Theorem A for all distinct odd primes | `ICGGeneral.jiang_yang_q3`, `jiang_yang_q3_value`, `energy_DstarPQ`, `thm5_le`, `thm5_eq`, `energy_icgAdj_pq`, `jiang_yang_thmA`, `checkerboard_unique_max_odd` | exhaustive exact searches over all divisor sets (shapes and primes listed in the paper); sign-matrix enumeration for `(a+1)(b+1) ≤ 25`; floating-point spectra of the actual graphs (`certificates/icg-q3-general/`) |
| Roldán q=3 for the genuine graph energy: unique maximizer, gap, value of `E(D*)`, sharpness | `ICGBridge.roldan_q3`, `roldan_q3_gap`, `energy_Dstar`, `roldan_q3_sharp`, `roldan_q3_gap_attained`, plus `*_graph` versions for mathlib's `SimpleGraph.circulantGraph` | three independent programs for the certificate; direct numerical diagonalization of the adjacency matrices for p = 5, 7 (all 2047 sets) |
| Roldán, whole conjecture (two-variable certificate, all real p, q ≥ 3) | not formalized | two independent programs |
| A389472 | `Oeis389472Mod3.integer_conjecture` | 1000 terms vs. the OEIS b-file |
| A240998 | `HannaA240998.hanna_a240998` | exact recomputation vs. the b-file (311 terms) |
| A295762 | `HannaA295762.hanna_a295762` | b-file (1030 terms), modulo 2^64 and two primes; 260 terms exactly |
| A273958 | `HannaA273958.hanna_a273958` | exact recomputation vs. the b-file (520 terms) |
| A301933, A377100, A274479, A388734 | `HannaA301933.hanna_a301933`, `HannaA377100.hanna_a377100`, `HannaA274479.hanna_a274479`, `HannaA388734.hanna_a388734` | exact recomputation of the full b-files (`certificates/oeis-hanna/batch2/`) |
| A338633, A338634, A120566 | `HannaA338633.hanna_a338633`, `HannaA338633.hanna_a338634`, `HannaA120566.hanna_a120566` | b-files substituted into the defining equation modulo two primes, and the first 60 (A338633, A338634) or 150 (A120566) terms recomputed independently (`batch2/`) |
| A184894, A107099, A361047 (resolved) | `HannaA184894.zero_part`, `value_at_pow`, `counterexample`; `HannaA107099.hanna_a107099`, `hanna_a107099_counterexample`; `HannaA361047.hanna_a361047_pow`, `hanna_a361047_nonpow` | A184894: exact recomputation vs. the b-file; A107099: b-file substituted into the defining equation modulo two primes; A361047: the same, plus the first 60 terms recomputed independently (`batch2/`) |

Each OEIS theorem is stated for every integer power series satisfying the
defining equation. The energy is `∑ |eigenvalues|`, using
`Matrix.IsHermitian.eigenvalues`.

All final theorems depend only on the axioms `propext`, `Classical.choice`
and `Quot.sound`. There is no `sorry`, no custom axiom and no
`native_decide`. The whole project was rebuilt from a clean directory for
this version; see `logs/clean-replay-v1.1.0-*.log` and
`logs/lean-sources-sha256.txt`.

### Reproduce the Lean checks

Requirements: [elan](https://github.com/leanprover/elan), about 20 GB of free
RAM for `CirculantQ3.lean` (its kernel-checked certificate peaks near 18 GB),
and about 10 minutes.

```sh
cd lean
lake exe cache get                         # prebuilt mathlib, pinned in lake-manifest.json
lake build                                 # builds everything imported by Research.lean
lake env lean Research/ICGGeneralAudit.lean # Paper 1: prints the final statements, definitions and axioms
lake env lean Research/ICGBridgeAudit.lean  # Roldán q = 3: the same
```

Toolchain: Lean 4.33.1, mathlib commit `0df444a360eaa60ab8c11dca51a86af692955474`.

### Reproduce the certificates and numerical checks

Requires Python 3 with SymPy and NumPy.

```sh
cd certificates/roldan-q3
python3 circulant_certificate.py      # (i)   integer polynomial arithmetic, all 2048 sets, two variables
python3 independent_q3_certificate.py # (ii)  Möbius formula, gcd enumeration, exact interpolation (q = 3)
python3 bivariate_sympy_check.py      # (iii) SymPy; cross-checks (i), the closed forms and the Lean table
python3 direct_graph_check.py 5 && python3 direct_graph_check.py 7   # diagnostic: eigenvalues of the actual graphs (n = 675, 1323)
cd ../oeis-hanna
python3 verify_389472.py && python3 verify_parity3.py && python3 verify_a295762_mod.py
cd batch2 && for s in verify_*.py; do python3 $s; done
```

`verify_a295762_mod.py` works modulo 2^64 on purpose, so NumPy's overflow
warnings are expected. `batch2/verify_batch2.py` also rechecks A091713 and
A196523. Those two are not claimed here: they were proved earlier by
A. Perez Fontelles (astrafala/Conjectures, 31 August 2026).


### Reproduce the computations of Paper 1

Requires a C compiler and Python 3 with SymPy and NumPy.

```sh
cd certificates/icg-q3-general
cc -O2 -o icg_search icg_search.c              # exhaustive search over all divisor sets
cc -O2 -DSIGNMODE=1 -o icg_sign icg_search.c   # enumeration of sign matrices
python3 run_search.py 4 1 3 5,7,11             # example: n = p^4·3 for p = 5, 7, 11 (compare logs/search_small.log)
```

The logs of all runs cited in the paper are in `certificates/icg-q3-general/logs/`.
The Lean comments and the scripts in `certificates/icg-q3-general/review/`
use the numbering of the first draft. Draft Lemmas 1–4 and Theorem 5 are
Lemmas 4, 5, 7, 8 and Theorem 9 of Paper 1. The "Lemma 3 as stated"
counterexample printed by `review/test_e_misc.py` concerns a superseded
hypothesis (`P > 0`); Lemma 7 of the paper assumes `P ≥ μ`.

## Layout

- `papers/`: LaTeX sources and PDFs of the two papers.
- `lean/`: Lake project with all Lean 4 proofs (`Research.lean` imports all of them).
- `certificates/`: certificate programs, their outputs and the OEIS b-files used.
- `logs/`: build logs, statement audits and source hashes from the clean
  rebuilds. `roldan-q3-lean-build-receipt.json` predates the formalization of
  the spectral bridge, so it still lists Lemma 2.1 as not formalized. The
  `ICGBridge*` files now formalize it (`ICGBridge.energy_icgAdj_eq_exactEnergy`).

## Prior work

- The conjectures and the numerical evidence are due to P. D. Hanna (OEIS)
  and D. G. Roldán (arXiv:2604.09491).
- Paper 1:
  - the case `q ≥ 5` of the opposite-parity family is due to Jiang and Yang
    (arXiv:2608.29523);
  - for the fixed exponents (2,3), i.e. order `p²q³`, Roldán's conjecture
    was treated earlier by Park and by Schreib (see below);
  - we are not aware of any earlier treatment of `q = 3` for general
    `r, s`.
  This reports the coverage of our searches, not a guarantee of priority.
- Roldán's conjecture, case q = 3 (the formalization here is of a known
  result):
  - S. Park, *Exact Energy Maximisation for Integral Circulant Graphs of
    Order p²q³* (github.com/coshaman/papers, 2026-08-21) claims the whole
    conjecture;
  - J. Jiang and C. Yang (arXiv:2608.29523) prove the case `q ≥ 5`;
  - J. A. Schreib (github.com/jamesschreib/roldan-universality-conjecture,
    2026-09-05) gives a written proof of the case q = 3; his Lean file
    assumes the spectral bridge as an axiom and uses `native_decide`;
  - [trureturing issue #8338](https://github.com/the-omega-institute/trureturing/issues/8338)
    (2026-09-16) announces an arithmetic certificate.
  - Our certificate was found independently, before we knew of these works.
- A389472, modulo 2: proved earlier by A. Perez Fontelles
  (astrafala/Conjectures, paper 1042, 2026-08-31) and in the trureturing
  repository. Both leave the modulo-three conjecture open.
- For the OEIS results listed above, we found no earlier proof in the
  following sources (searched 25–26 September 2026):
  - the OEIS entries and their revision histories;
  - the-omega-institute/trureturing (files, issues and pull requests);
  - astrafala/Conjectures and twentyseventhllc-lgtm/OEIS-Settled;
  - other public repositories of OEIS proofs;
  - the literature and the web.
  This reports the coverage of our searches, not a guarantee of priority.

## Tool and computational resource disclosure

This work was carried out on 25–26 September 2026 in a workflow directed by
the author, using two AI coding agents:

- OpenAI Codex (desktop app; models `gpt-6-astra`, `gpt-6-sol`);
- Anthropic Claude Code (model Claude Opus 5.5).

The author chose the research programme and directed the agents. The agents:

- searched the literature and the OEIS;
- found the proofs and the certificates;
- wrote the programs and the Lean code;
- drafted the papers and this README.

Each agent audited the other's work. The author, who is not a professional
mathematician, has read both papers and, using a side-by-side table, compared
the statements of the final Lean theorems with the theorems in the papers. AI
systems are not authors. The author takes full responsibility for the content.

## License

Code (`lean/`, `certificates/`) is licensed under the Apache License 2.0; see
`LICENSE`. The papers in `papers/` are licensed under
[CC BY 4.0](https://creativecommons.org/licenses/by/4.0/). The OEIS b-files in
`certificates/oeis-hanna/bfiles/` and `certificates/oeis-hanna/b389472.txt` are from the OEIS and are licensed under
CC BY-SA 4.0.

## Citation

See `CITATION.cff`. To cite all versions, use the concept DOI
[10.5281/zenodo.22970254](https://doi.org/10.5281/zenodo.22970254). Each
release also has its own version DOI, listed on the Zenodo record.
