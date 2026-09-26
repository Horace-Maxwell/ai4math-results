# Lean 4 proofs of four OEIS congruence conjectures, and a Lean formalization of the case q = 3 of Roldán's energy conjecture

This repository contains Lean 4 formalizations and computational
certificates. A paper with the written proofs of the OEIS results will be
added in a later version.

**Formalization of a known result: the case q = 3 of Roldán's Conjecture 1.3
(arXiv:2604.09491).**

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

**Four congruence conjectures of P. D. Hanna from the OEIS**, proved and
formally verified:

| Entry | Defining equation | Theorem |
| --- | --- | --- |
| A389472 | `A(x² + x³) = x²(1 + A(x))` | `3 ∣ a(3n − 1)` for `n > 1` |
| A240998 | `A(x)² = x + A(x + 2x²)` | for `n ≥ 1`, `a(n)` is odd iff `n` is a power of 2 |
| A295762 | `A(x − 2A(x²)) = x + A(x²)` | for `n ≥ 1`, `a(n)` is odd iff `n` is a power of 2 (the entry conjectures one direction) |
| A273958 | `xA + x²A² = C²`, with `C = x + C²` | `a(n)` is odd iff `n = 2·4^k − 1` |

## What is verified, and how

| Claim | Lean 4 declarations | Independent computation |
| --- | --- | --- |
| Roldán q=3 for the genuine graph energy: unique maximizer, gap, value of `E(D*)`, sharpness | `ICGBridge.roldan_q3`, `roldan_q3_gap`, `energy_Dstar`, `roldan_q3_sharp`, `roldan_q3_gap_attained`, plus `*_graph` versions for mathlib's `SimpleGraph.circulantGraph` | three independent programs for the certificate; direct numerical diagonalization of the adjacency matrices for p = 5, 7 (all 2047 sets) |
| Roldán, whole conjecture (two-variable certificate, all real p, q ≥ 3) | not formalized | two independent programs |
| A389472 | `Oeis389472Mod3.integer_conjecture` | 1000 terms vs. the OEIS b-file |
| A240998 | `HannaA240998.hanna_a240998` | exact recomputation vs. the b-file (311 terms) |
| A295762 | `HannaA295762.hanna_a295762` | b-file (1030 terms), modulo 2^64 and two primes; 260 terms exactly |
| A273958 | `HannaA273958.hanna_a273958` | exact recomputation vs. the b-file (520 terms) |

Each OEIS theorem is stated for every integer power series satisfying the
defining equation. The energy is `∑ |eigenvalues|`, using
`Matrix.IsHermitian.eigenvalues`.

All final theorems depend only on the axioms `propext`, `Classical.choice`
and `Quot.sound`. There is no `sorry`, no custom axiom and no
`native_decide`. The whole project was rebuilt from a clean directory; see
`logs/`.

### Reproduce the Lean checks

Requirements: [elan](https://github.com/leanprover/elan), about 20 GB of free
RAM for `CirculantQ3.lean` (its kernel-checked certificate peaks near 18 GB),
and about 10 minutes.

```sh
cd lean
lake exe cache get                         # prebuilt mathlib, pinned in lake-manifest.json
lake build                                 # builds everything imported by Research.lean
lake env lean Research/ICGBridgeAudit.lean # prints the final statements, definitions and axioms
```

Toolchain: Lean 4.33.1, mathlib commit `0df444a360eaa60ab8c11dca51a86af692955474`.

### Reproduce the certificates and numerical checks

Requires Python 3 with SymPy and NumPy.

```sh
cd certificates/roldan-q3
python3 circulant_certificate.py      # (i)   integer polynomial arithmetic, all 2048 sets, two variables
python3 independent_q3_certificate.py # (ii)  Möbius formula, gcd enumeration, exact interpolation (q = 3)
python3 bivariate_sympy_check.py      # (iii) SymPy; cross-checks (i), the closed forms and the Lean table
python3 direct_graph_check.py 5 7     # diagnostic: eigenvalues of the actual graphs (n = 675, 1323)
cd ../oeis-hanna
python3 verify_389472.py && python3 verify_parity3.py && python3 verify_a295762_mod.py
```

`verify_a295762_mod.py` works modulo 2^64 on purpose, so NumPy's overflow
warnings are expected.

## Layout

- `lean/`: Lake project with all Lean 4 proofs (`Research.lean` imports all of them).
- `certificates/`: certificate programs, their outputs and the OEIS b-files used.
- `logs/`: build logs, the statement audit and source hashes from the clean rebuild.

## Prior work

- The conjectures and the numerical evidence are due to P. D. Hanna (OEIS)
  and D. G. Roldán (arXiv:2604.09491).
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

## Tool and computational resource disclosure

This work was carried out on 25–26 September 2026 in a workflow directed by
the author, using two AI coding agents:

- OpenAI Codex (desktop app; models `gpt-6-astra`, `gpt-6-sol`);
- Anthropic Claude Code (model Claude Opus 5.5).

The author chose the research programme and directed the agents. The agents:

- searched the literature and the OEIS;
- found the proofs and the certificates;
- wrote the programs and the Lean code;
- drafted this README.

Each agent audited the other's work. AI systems are not authors. The author
takes full responsibility for the content.

## License

Code (`lean/`, `certificates/`) is licensed under the Apache License 2.0; see
`LICENSE`. The OEIS b-files in `certificates/oeis-hanna/bfiles/` are from the
OEIS and are licensed under CC BY-SA 4.0.

## Citation

See `CITATION.cff`.
