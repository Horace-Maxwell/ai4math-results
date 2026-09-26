# Lean formalisation of Theorem B — status

Agent: Claude Code subagent (Lean). Dev project `work/research-lean`, Lean 4.33.1 / Mathlib v4.33.1
(lakefile `autoImplicit = false`; every new file also sets `set_option autoImplicit false`).
Lock `work/.lean-lock-A` held 06:23–07:16 UTC (released).

## State (07:16 UTC): COMPLETE
Theorem B, Theorem B′ (real parameters) and the swapped corollary are proved with no `sorry`/axioms; in addition all
325 vertex certificates of `prove_fd.py` are proved in Lean as an independent cross-check.

| file (in `work/research-lean/Research/`) | lines | content |
|---|---|---|
| `ICGEqualParityBCol.lean` | 499 | column algebra `Mc0/1/2`, `Dp`, `Sc` (= q·s), exact cell values, **Lemma S** (`lemS`), `poly_I1..I7`, `poly_I5b` |
| `ICGEqualParityBFD.lean` | 601 | **Lemma FD1** (`fd1`), **FD2(a)** (`fd2a`), p = 3 dominance (`fd2dom`), two-column bound (`two_col`) |
| `ICGEqualParityBMain.lean` | 785 | rows of `T₂(p)Y`, `Gfun`, `Theta`, **Proposition 1** (`prop1`), tail states, cases, **Lemma EQ** (`eq_step`, `eq_all`), `thmB'_main` |
| `ICGEqualParityBGraph.lean` | 626 | `G(Y⁻)=G(Y⁺)=Θ`, **Theorem B′** (`thmB'`), `2E = G + n` (a = 2), **Theorem B** (`theoremB`, `corollaryB`), swap (`theoremB_swap`) |
| `ICGEqualParityBCert1..6.lean` | 3178 | generated: 325 lemmas `ICGEqualParityB.Cert.cert_*` = the note's vertex certificates |
| `ICGEqualParityBAudit.lean`, `ICGEqualParityBCertAudit.lean` | 42, 336 | `#print`/`#check`/`#print axioms` (not imported by `Research.lean`) |

`Research.lean` now imports the four proof modules and the six certificate modules.
Generator: `lean/gen_certs.py` (reads `prove_fd.py`; output also in `lean/gen/`, name list `lean/gen/cert_names.txt`).

### Final statements (namespace `ICGEqualParityB`)
* `theoremB (p q b : ℕ) (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) (hp3 : 3 ≤ p) (hq3 : 3 ≤ q) (hb : Even b) (hb2 : 2 ≤ b)
  (D) (hD : D ⊆ (p^2*q^b).properDivisors) :`
  `E(ICG_n(D)) ≤ (p²q^b + (5p²−8p+4)·L1 q b sgnv)/2 − (p²−2p+2)·Tv q b sgnv b ∧ (E(D) = that ↔ D = DantiPQ p q 2 b ∨ D = DtruncB p q b)`
  with `DtruncB p q b = (DstarPQ p q 2 b).erase (p^2*q^b)`; `d_b(q) = L1 q b sgnv`, `δ_b(q) = Tv q b sgnv b` exactly as in `corollaryA`.
* `corollaryB`: same content in the format of `ICGEqualParity.corollaryA` (both sets admissible, `2E(D⁻) = n + (5p²−8p+4)d − 2(p²−2p+2)δ`,
  `E(D⁺∖{n}) = E(D⁻)`, maximality, uniqueness).
* `theoremB_swap`: `n = p^b q²`: bound `(n + (5q²−8q+4)·L1 p b sgnv)/2 − (q²−2q+2)·Tv p b sgnv b`, equality iff
  `D = DantiPQ p q b 2 ∨ D = (DstarPQ p q b 2).erase (p^b*q^2)`.
* `thmB' {p q : ℝ} (ParamB p q) (Even b) (2 ≤ b) (SignMat b Y) (Y 2 b = −1) : Gfun p q b Y ≤ Theta p q b ∧
  (Gfun p q b Y = Theta p q b ↔ Y = Ym ∨ Y = Yp b on {0,1,2}×{0..b})`, `ParamB p q := (5 ≤ p ∧ 3 ≤ q) ∨ (p = 3 ∧ 5 ≤ q)`.

### Checks (final run 07:13–07:15 UTC)
1. `lake build` (default target `Research`): `Build completed successfully (8731 jobs)`, no errors, no warnings in the new files.
2. Axioms (`lean/audit_output.txt`, full `lake env lean` output of the audit file): `theoremB`, `corollaryB`, `theoremB_swap`,
   `thmB'`, `prop1`, `lemS`, `fd1`, `fd2a`, `fd2dom`, `G_Yp` all depend on `[propext, Classical.choice, Quot.sound]`.
   Certificates (`lean/cert_audit_output.txt`): 325/325 lemmas depend on exactly these three axioms.
3. `grep -n -E "sorry|admit|native_decide|axiom"` over the 4 proof modules + 6 certificate modules: empty.
   (The two audit files contain only `#print axioms` commands.)
4. `lake env leanchecker Research.ICGEqualParityB{Col,FD,Main,Graph,Cert1..Cert6}`: exit 0, no output, all ten.

## Proof route of the Lean proof (differs from PROOF.md §3–§4)
Follows §1, §2, §5 (Proposition 1, Lemma S, first deviation J, cases J < b / J = b ∈ {C, −E, B}, Lemma EQ), but uses
simpler bounds instead of the regime-by-regime vertex certificates:
* **FD1**: crude box `μ, m ∈ [μ₀, 1]`, `ρ ≤ μ₁` for A same (`(Q−1)²d₂(p) > δ₂(p)(Q²+1)` = `poly_I1`), B same (`poly_I2`, bilinear
  [0,1]² check `poly_I3`), B opp (`poly_I4`, `poly_I5`, `poly_I5b`), E same/opp (Lemma-S bound + `poly_I7`); C same/opp via
  the Lemma-S bound `Sc ≥ 2(P²+1)Q(1+μ) − 4μpPm` and the exact regimes J = 0 (`qρ = Q − m`), J = b−1 (`qρ = Q − μ`),
  else `m ≤ μ₁` (`poly_I6`). All polynomial inequalities have nonnegative coefficients after `P = 4+u², Q = 2+v²`
  (resp. `P = 2, Q = 4+v²`) and close by `ring_nf; positivity`.
* **FD2(a)** (state exactly `α(B)`, `qρ = Q − μ`): all 8 columns by direct bounds.
* **FD2(b)** (p = 3, `c_{b−1} = −B`): two-column argument replacing the J′/k analysis: `s_{b−1} = 2ĉ_{b−1}` (chain),
  `s_{b−2} ≥ 2ĉ_{b−2}` for every column at the exact state `−μ₀α(B)` (`fd2dom`), and `2ĉ_{b−1} + 2ĉ_{b−2} > 8ρ`
  since `μ_{b−3} > L` (`two_col`; tight at b = 2, q → ∞, as in the note).
* **Lemma EQ**: row 2 alone forces `c_j = (−1)^j s₂` (the sign of `z_j(r₂)` alternates).
The note's own route is additionally cross-checked: all 325 vertex values of `prove_fd.py` (closed forms at the vertices,
both regions, all min/max branches) are proved positive in Lean (`Cert1..6`). The closed forms and the concavity/vertex
reduction of §3–§4 themselves are not formalised (the main proof does not need them).

## Mathematical remarks
* PROOF.md §0, "for A ≠ 0: h(A,B) = 0 ⇔ −Q|A| ≤ B·sgn A ≤ 0" is **false as stated**: e.g. A > 0, 0 < μ ≤ 1, B = QA/μ gives
  h = 2(μB − QA) = 0; for μ = 0 every B < −QA gives h = 0. Only "⇐" holds in general; "⇒" holds under `|B| < Q|A|` and
  `0 ≤ μ ≤ 1 < Q` (Lean `hc_zero_imp`). Lemma EQ uses "⇒" only at type-A columns, where `|B_i| ≤ (2pP, 2pP, p²) < Q|A_i|`,
  so the proof is unaffected. Suggest qualifying the sentence.
* No false lemma or gap found. The simpler FD1/FD2(b) arguments above could shorten §3–§4 of the write-up.
