import Mathlib

/-!
# Paper 2 back-fill: challenge file (definitions and statements only)

Paper: H. Dong, "Proofs of eleven congruence conjectures of Hanna from the OEIS, and the
resolution of three more", `papers/oeis-hanna/note.tex` of the repository (version 1.2.1,
8 pages).

This file contains **only definitions and statements** (`def … : Prop`). It imports Mathlib and
nothing else. No statement is proved here. Each `def` quotes (or points to, with `note.tex`
line numbers `l.`) the paper item it formalizes. These statements were written **after** the
paper, its proofs and its Lean modules existed (back-fill), by an AI agent (2026-09-27 UTC).

## Numbering of the paper (one shared counter)

Lemma 1 (Frobenius), Lemma 2 (fixed series), Lemma 3 (dyadic recursion), Theorem 4 (A389472),
Theorem 5 (parity: A240998, A295762, A301933, A338633/A338634, A273958), Theorem 6 (A388734),
Theorem 7 (A377100), Theorem 8 (A274479), Theorem 9 (A120566), Theorem 10 (A361047),
Remark 11, Theorem 12 (A184894), Theorem 13 (A107099); four unnumbered remarks.

## Conventions (paper §1, l. 78–91)

* `A = ∑ a(n) xⁿ ∈ ℤ[[x]]` is `A : PowerSeries ℤ`, `a(n) = coeff n A` (Mathlib).
* `A(h)`, `A ∘ h` (composition, `h(0) = 0`) is Mathlib's `A.subst h` (`PowerSeries.subst`).
  Direction checked by the first two tests of `ChallengeTests.lean`.
* `A'` is Mathlib's `PowerSeries.derivative (R := ℤ) A`.
* Reduction mod `p` of a series is `PowerSeries.map (Int.castRingHom (ZMod p))`; `𝔽_p = ZMod p`.
* "odd", "≡ r (mod m)", "m ∣" are Mathlib's `Odd`, `Int.ModEq`, `Dvd` on `ℤ`.
* A quotient `P/Q` with `Q(0)` a unit is written with Mathlib's `PowerSeries.invOfUnit Q 1`;
  the one quotient with non-unit denominator (A377100) is written with an exact quotient `U`.
* Every theorem is stated, as in the paper, "for every integer power series satisfying the
  defining equation" (with the paper's normalizations). Existence and uniqueness of these
  series, which the paper asserts in §1 (l. 83–91) but does not formalize, are the separate
  statements `EX_*` (§ 8 below; the first terms are `DATA_*`, § 9); they make the theorems
  non-vacuous.

Every custom definition is listed in the table "Definitions the reader must trust" of
`work/lean-backfill/paper2/STATEMENTS.md`, and tested in `ChallengeTests.lean`.
-/

set_option autoImplicit false

universe u

namespace BackfillPaper2.Challenge

open PowerSeries

/-! ## 0. Custom definitions (few and short) -/

/-- Reduction modulo `p` of an integer power series (Mathlib's `PowerSeries.map`). -/
noncomputable abbrev red (p : ℕ) (A : PowerSeries ℤ) : PowerSeries (ZMod p) :=
  PowerSeries.map (Int.castRingHom (ZMod p)) A

/-- The paper's Catalan series `C = ∑_{n ≥ 1} C_{n-1} xⁿ` (l. 124–125): `x` times Mathlib's
`PowerSeries.catalanSeries = ∑_{n ≥ 0} C_n xⁿ` (a series over `ℕ`), cast to `ℤ`. -/
noncomputable def catalanC : PowerSeries ℤ :=
  X * PowerSeries.map (Nat.castRingHom ℤ) PowerSeries.catalanSeries

/-- The ternary numbers `t(k) = binom(3k, k)/(2k+1)` (A001764, Remark 11, l. 357–358).
The division is exact (natural-number division; tested). -/
def ternary (k : ℕ) : ℕ := Nat.choose (3 * k) k / (2 * k + 1)

/-- `V = ∑_{k ≥ 0} t(k) x^{2k+1}` (Remark 11, l. 357). -/
noncomputable def ternarySeries : PowerSeries ℤ :=
  PowerSeries.mk fun n => if n % 2 = 1 then (ternary (n / 2) : ℤ) else 0

/-- A series over `𝔽₃` is *additive* if `[x^m] G = 0` whenever `m` is not a power of `3`
(l. 370–371). -/
def Additive3 (G : PowerSeries (ZMod 3)) : Prop :=
  ∀ m : ℕ, (¬ ∃ j : ℕ, m = 3 ^ j) → coeff m G = 0

/-- `P₀ = x`, `P_{m+1} = P_m + P_m³` (Theorem 12, l. 375). -/
noncomputable def P184894 : ℕ → Polynomial ℤ
  | 0 => Polynomial.X
  | m + 1 => P184894 m + P184894 m ^ 3

/-- `a(m) = [x^{2m-1}] P_m` (Theorem 12, l. 375; the paper uses it for `m ≥ 1`). -/
noncomputable def a184894 (m : ℕ) : ℤ := (P184894 m).coeff (2 * m - 1)

/-- "Every base-3 digit of `n` except the last is at most 1" (l. 394–395, l. 435–436).
`Nat.digits 3 n` lists the digits from the least significant one, so the "last" digit (in the
usual writing) is the head of the list. -/
def digitsExceptLastLeOne (n : ℕ) : Prop := ∀ d ∈ (Nat.digits 3 n).tail, d ≤ 1

/-- The reduction mod 3 of the additive series `∑_j binom(1/2, j) x^{3^j}` (final remark,
l. 425–427). `binom(1/2, j)` is Mathlib's `Ring.choose (1/2 : ℚ) j`; its residue mod 3 is
Mathlib's cast `ℚ → ZMod 3` (numerator times inverse of denominator), meaningful here because
the denominators are powers of 2 (tested). The inner sum picks the unique `j` with `m = 3^j`. -/
noncomputable def sqrtSeries3 : PowerSeries (ZMod 3) :=
  PowerSeries.mk fun m =>
    ∑ j ∈ Finset.range (m + 1), if m = 3 ^ j then ((Ring.choose (1 / 2 : ℚ) j : ℚ) : ZMod 3) else 0

/-! ### Defining equations (transcriptions of Table 1 / the theorems) -/

/-- A389472: `A(x² + x³) = x² (1 + A(x))` (Theorem 4, l. 206). -/
def Eq389472 (A : PowerSeries ℤ) : Prop :=
  A.subst ((X : PowerSeries ℤ) ^ 2 + X ^ 3) = X ^ 2 * (1 + A)

/-- A240998: `A² = x + A(x + 2x²)` (Theorem 5(1), l. 222). -/
def Eq240998 (A : PowerSeries ℤ) : Prop :=
  A ^ 2 = X + A.subst ((X : PowerSeries ℤ) + 2 * X ^ 2)

/-- A295762: `A(x − 2A(x²)) = x + A(x²)` (Theorem 5(2), l. 223). -/
def Eq295762 (A : PowerSeries ℤ) : Prop :=
  A.subst ((X : PowerSeries ℤ) - 2 * A.subst ((X : PowerSeries ℤ) ^ 2)) =
    X + A.subst ((X : PowerSeries ℤ) ^ 2)

/-- A301933: `A(1 + AA') = x(1 + 4AA')` (Theorem 5(3), l. 224; the entry's
`A = x(1+4AA')/(1+AA')` with the unit denominator cleared, as in the theorem). -/
def Eq301933 (A : PowerSeries ℤ) : Prop :=
  A * (1 + A * derivative (R := ℤ) A) = X * (1 + 4 * A * derivative (R := ℤ) A)

/-- The continued fraction `1 = A − x/(A − 2^e x/(A − 3^e x/(A − ⋯)))` "in the following
sense" (Theorem 5(4), l. 225–229): series `T₀, T₁, …` with constant terms `±1` such that
`(A − 1) T₀ = x` and `(A − T_k) T_{k+1} = (k+2)^e x` for all `k ≥ 0`. -/
def CF (e : ℕ) (A : PowerSeries ℤ) (T : ℕ → PowerSeries ℤ) : Prop :=
  (∀ k : ℕ, constantCoeff (T k) = 1 ∨ constantCoeff (T k) = -1) ∧
  (A - 1) * T 0 = X ∧
  ∀ k : ℕ, (A - T k) * T (k + 1) = C (((k : ℤ) + 2) ^ e) * X

/-- A273958: `C = x + C²` and `xA + x²A² = C²` (Theorem 5, "Moreover", l. 231). -/
def Eq273958 (Cs A : PowerSeries ℤ) : Prop :=
  Cs = X + Cs ^ 2 ∧ X * A + X ^ 2 * A ^ 2 = Cs ^ 2

/-- A388734: `A = 1 + xA² + x²(1 − x)A³` (Theorem 6, l. 259). -/
def Eq388734 (A : PowerSeries ℤ) : Prop :=
  A = 1 + X * A ^ 2 + X ^ 2 * (1 - X) * A ^ 3

/-- A377100: `A = A(x³)/A(x²) + A²` (Theorem 7, l. 281): the quotient is a power series `U`
with `A(x²) U = A(x³)`, and `A = U + A²`. -/
def Eq377100 (A U : PowerSeries ℤ) : Prop :=
  A.subst ((X : PowerSeries ℤ) ^ 2) * U = A.subst ((X : PowerSeries ℤ) ^ 3) ∧ A = U + A ^ 2

/-- `h = x²/(1 − 2x − 4x²)` (Theorem 8, l. 294). -/
noncomputable def h274479 : PowerSeries ℤ :=
  X ^ 2 * PowerSeries.invOfUnit (1 - 2 * X - 4 * X ^ 2) 1

/-- A274479: `A² = A(x²/(1 − 2x − 4x²))` (Theorem 8, l. 294). -/
def Eq274479 (A : PowerSeries ℤ) : Prop := A ^ 2 = A.subst h274479

/-- A120566: `A = A∘A − x·A∘A∘A` (Theorem 9, l. 312). -/
def Eq120566 (A : PowerSeries ℤ) : Prop :=
  A = A.subst A - X * A.subst (A.subst A)

/-- A361047: `A(x − x³A'²) = x` (Theorem 10, l. 337). -/
def Eq361047 (A : PowerSeries ℤ) : Prop :=
  A.subst ((X : PowerSeries ℤ) - X ^ 3 * (derivative (R := ℤ) A) ^ 2) = X

/-- A107099: `A∘A = x + 4x³` (Theorem 13, l. 398). -/
def Eq107099 (A : PowerSeries ℤ) : Prop :=
  A.subst A = X + 4 * X ^ 3

/-! ## 1. Section 2 (Tools): Lemmas 1–3 and the x-adic observation -/

/-- §2, l. 164–166: reduction modulo a prime `p` commutes with composition by series with zero
constant term and with formal differentiation. -/
def Sec2_reduction : Prop :=
  ∀ p : ℕ, p.Prime → ∀ A h : PowerSeries ℤ, constantCoeff h = 0 →
    red p (A.subst h) = (red p A).subst (red p h) ∧
    red p (derivative (R := ℤ) A) = derivative (R := ZMod p) (red p A)

/-- **Lemma 1 (Frobenius)** (l. 169–171): for `F ∈ 𝔽_p[[x]]`, `F(x)^p = F(x^p)`. -/
def Lemma1 : Prop :=
  ∀ p : ℕ, p.Prime → ∀ F : PowerSeries (ZMod p), F ^ p = F.subst ((X : PowerSeries (ZMod p)) ^ p)

/-- **Lemma 2** (l. 177–180): `K` a field, `h ∈ xK[[x]]` of order at least two, `H(h) = H`
⟹ `H` is constant. -/
def Lemma2 : Prop :=
  ∀ (K : Type u) [Field K] (h H : PowerSeries K),
    constantCoeff h = 0 → (2 : ℕ∞) ≤ h.order → H.subst h = H → H = C (constantCoeff H)

/-- **Lemma 3 (dyadic recursion)** (l. 186–189): `F ∈ 𝔽₂[[x]]`, `F(0) = 0`, `F = x + F²` ⟹
for `n ≥ 1`, `f(n) = 1` iff `n` is a power of 2. -/
def Lemma3 : Prop :=
  ∀ F : PowerSeries (ZMod 2), constantCoeff F = 0 → F = X + F ^ 2 →
    ∀ n : ℕ, 1 ≤ n → (coeff n F = 1 ↔ ∃ k : ℕ, n = 2 ^ k)

/-- **The x-adic observation** (l. 200–202): if `D ∈ 𝔽_p[[x]]`, `x^{n₀} ∣ D`, and
`xⁿ ∣ D ⟹ x^{n+1} ∣ D` for all `n ≥ n₀`, then `D = 0`. -/
def ObsXadic : Prop :=
  ∀ p : ℕ, p.Prime → ∀ (D : PowerSeries (ZMod p)) (n₀ : ℕ),
    X ^ n₀ ∣ D → (∀ n : ℕ, n₀ ≤ n → X ^ n ∣ D → X ^ (n + 1) ∣ D) → D = 0

/-- Remark after Lemma 3 (l. 196–198): the reduction of the Catalan series satisfies
`F = x + F²` (so Lemma 3 is the parity of the Catalan numbers). Over `ℤ`: `C = x + C²`
(l. 125). -/
def CatalanEq : Prop := catalanC = X + catalanC ^ 2

/-! ## 2. Theorem 4 (A389472) -/

/-- **Theorem 4** (l. 205–207): if `A(x²+x³) = x²(1+A(x))`, then `a(3n−1) ≡ 0 (mod 3)` for
every `n > 1`. -/
def Thm4 : Prop :=
  ∀ A : PowerSeries ℤ, Eq389472 A → ∀ n : ℕ, 1 < n → (3 : ℤ) ∣ coeff (3 * n - 1) A

/-! ## 3. Theorem 5 (parity via the dyadic recursion) -/

/-- **Theorem 5(1)** (A240998, l. 218–222): `a(n)` odd for `n ≥ 1` iff `n` is a power of 2. -/
def Thm5_1 : Prop :=
  ∀ A : PowerSeries ℤ, Eq240998 A → ∀ n : ℕ, 1 ≤ n → (Odd (coeff n A) ↔ ∃ k : ℕ, n = 2 ^ k)

/-- **Theorem 5(2)** (A295762, l. 223): with `a(0) = 0`. -/
def Thm5_2 : Prop :=
  ∀ A : PowerSeries ℤ, constantCoeff A = 0 → Eq295762 A →
    ∀ n : ℕ, 1 ≤ n → (Odd (coeff n A) ↔ ∃ k : ℕ, n = 2 ^ k)

/-- **Theorem 5(3)** (A301933, l. 224): with `a(0) = 0`. -/
def Thm5_3 : Prop :=
  ∀ A : PowerSeries ℤ, constantCoeff A = 0 → Eq301933 A →
    ∀ n : ℕ, 1 ≤ n → (Odd (coeff n A) ↔ ∃ k : ℕ, n = 2 ^ k)

/-- **Theorem 5(4)**, `e = 3` (A338633, l. 225–229). -/
def Thm5_4_A338633 : Prop :=
  ∀ (A : PowerSeries ℤ) (T : ℕ → PowerSeries ℤ), CF 3 A T →
    ∀ n : ℕ, 1 ≤ n → (Odd (coeff n A) ↔ ∃ k : ℕ, n = 2 ^ k)

/-- **Theorem 5(4)**, `e = 4` (A338634, l. 225–229). -/
def Thm5_4_A338634 : Prop :=
  ∀ (A : PowerSeries ℤ) (T : ℕ → PowerSeries ℤ), CF 4 A T →
    ∀ n : ℕ, 1 ≤ n → (Odd (coeff n A) ↔ ∃ k : ℕ, n = 2 ^ k)

/-- **Theorem 5, "Moreover"** (A273958, l. 231–232): if `C = x + C²` and `xA + x²A² = C²`,
then `a(n)` is odd iff `n = 2·4^k − 1` for some `k ≥ 0` (all `n ≥ 0`). -/
def Thm5_A273958 : Prop :=
  ∀ Cs A : PowerSeries ℤ, Eq273958 Cs A →
    ∀ n : ℕ, (Odd (coeff n A) ↔ ∃ k : ℕ, n = 2 * 4 ^ k - 1)

/-! ## 4. "Relation to classical results" (l. 122–153) -/

/-- l. 126–128: modulo 2 the series of A295762 and A301933, and those of A240998, A338633,
A338634 minus 1, equal `C`. For A240998 "minus 1" refers to the entry's solution, `a(0) = 1`
(the equation also has a solution with `a(0) = 0`, which is itself `≡ C`); for A338633/4,
`a(0) = 1` is forced by `(A − 1)T₀ = x`. -/
def RC_seriesMod2 : Prop :=
  (∀ A : PowerSeries ℤ, constantCoeff A = 0 → Eq295762 A → red 2 A = red 2 catalanC) ∧
  (∀ A : PowerSeries ℤ, constantCoeff A = 0 → Eq301933 A → red 2 A = red 2 catalanC) ∧
  (∀ A : PowerSeries ℤ, constantCoeff A = 1 → Eq240998 A → red 2 (A - 1) = red 2 catalanC) ∧
  (∀ (A : PowerSeries ℤ) (T : ℕ → PowerSeries ℤ), CF 3 A T → red 2 (A - 1) = red 2 catalanC) ∧
  (∀ (A : PowerSeries ℤ) (T : ℕ → PowerSeries ℤ), CF 4 A T → red 2 (A - 1) = red 2 catalanC)

/-- Abstract, l. 58–59: "Modulo 2, the series of A240998, A295762, A301933, A338633 and A338634
reduce, up to an additive constant, to the Catalan series" (every solution). -/
def RC_abstractMod2 : Prop :=
  (∀ A : PowerSeries ℤ, Eq240998 A → red 2 (A - C (constantCoeff A)) = red 2 catalanC) ∧
  (∀ A : PowerSeries ℤ, constantCoeff A = 0 → Eq295762 A →
      red 2 (A - C (constantCoeff A)) = red 2 catalanC) ∧
  (∀ A : PowerSeries ℤ, constantCoeff A = 0 → Eq301933 A →
      red 2 (A - C (constantCoeff A)) = red 2 catalanC) ∧
  (∀ (A : PowerSeries ℤ) (T : ℕ → PowerSeries ℤ), CF 3 A T →
      red 2 (A - C (constantCoeff A)) = red 2 catalanC) ∧
  (∀ (A : PowerSeries ℤ) (T : ℕ → PowerSeries ℤ), CF 4 A T →
      red 2 (A - C (constantCoeff A)) = red 2 catalanC)

/-- l. 131: "Hence `a(n) ≡ C_{n−1} (mod 2)` for `n ≥ 1`" (the five entries, every solution). -/
def RC_coeffMod2 : Prop :=
  (∀ A : PowerSeries ℤ, Eq240998 A → ∀ n : ℕ, 1 ≤ n → coeff n A ≡ (catalan (n - 1) : ℤ) [ZMOD 2]) ∧
  (∀ A : PowerSeries ℤ, constantCoeff A = 0 → Eq295762 A →
      ∀ n : ℕ, 1 ≤ n → coeff n A ≡ (catalan (n - 1) : ℤ) [ZMOD 2]) ∧
  (∀ A : PowerSeries ℤ, constantCoeff A = 0 → Eq301933 A →
      ∀ n : ℕ, 1 ≤ n → coeff n A ≡ (catalan (n - 1) : ℤ) [ZMOD 2]) ∧
  (∀ (A : PowerSeries ℤ) (T : ℕ → PowerSeries ℤ), CF 3 A T →
      ∀ n : ℕ, 1 ≤ n → coeff n A ≡ (catalan (n - 1) : ℤ) [ZMOD 2]) ∧
  (∀ (A : PowerSeries ℤ) (T : ℕ → PowerSeries ℤ), CF 4 A T →
      ∀ n : ℕ, 1 ≤ n → coeff n A ≡ (catalan (n - 1) : ℤ) [ZMOD 2])

/-- l. 129: the entry's remark `C = x(1 + 2CC')/(1 + CC')`, cleared of its unit denominator. -/
def RC_A301933_catalanIdentity : Prop :=
  catalanC * (1 + catalanC * derivative (R := ℤ) catalanC) =
    X * (1 + 2 * catalanC * derivative (R := ℤ) catalanC)

/-- l. 130–131: modulo 2 both equations reduce to `F = x/(1 + FF')`, "which determines `F`"
(for `F(0) = 0`, the normalization of the context; `1 + C` is a second solution). -/
def RC_A301933_determines : Prop :=
  ∀ F : PowerSeries (ZMod 2), constantCoeff F = 0 → F * (1 + F * derivative (R := ZMod 2) F) = X →
    F = red 2 catalanC

/-- l. 132–133: the classical fact "`C_n` is odd iff `n = 2^k − 1`". -/
def RC_catalanParity : Prop :=
  ∀ n : ℕ, (Odd (catalan n) ↔ ∃ k : ℕ, n = 2 ^ k - 1)

/-- l. 133–135: `ν₂(C_n) = s₂(n+1) − 1` (Deutsch–Sagan, Theorem 2.1 of arXiv:math/0407326v1),
cited as the source of `RC_catalanParity`; not used by any proof of the paper. -/
def RC_DS21 : Prop :=
  ∀ n : ℕ, padicValNat 2 (catalan n) = (Nat.digits 2 (n + 1)).sum - 1

/-- l. 138: for every `e ≥ 1` the continued fraction reduces to `A(A − 1) = x` modulo 2
("All of them", the family containing `e = 1, 2, 3, 4`). -/
def RC_CFfamilyMod2 : Prop :=
  ∀ e : ℕ, 1 ≤ e → ∀ (A : PowerSeries ℤ) (T : ℕ → PowerSeries ℤ), CF e A T →
    red 2 A * (red 2 A - 1) = X

/-- l. 139–141 (A273958): formula (1) of the entry gives `xA = −C(−C²)` (every solution). -/
def RC_A273958_closedForm : Prop :=
  ∀ Cs A : PowerSeries ℤ, Eq273958 Cs A → X * A = -(Cs.subst (-(Cs ^ 2)))

/-- l. 141: hence `xA ≡ C(C(x²)) (mod 2)`. -/
def RC_A273958_mod2 : Prop :=
  ∀ Cs A : PowerSeries ℤ, Eq273958 Cs A →
    red 2 (X * A) = (red 2 Cs).subst ((red 2 Cs).subst ((X : PowerSeries (ZMod 2)) ^ 2))

/-- l. 141–142: `C(C(x)) ≡ ∑_{k ≥ 0} x^{4^k} (mod 2)`. -/
def RC_CCmod2 : Prop :=
  ∀ n : ℕ, (coeff n ((red 2 catalanC).subst (red 2 catalanC)) = 1 ↔ ∃ k : ℕ, n = 4 ^ k)

/-! ## 5. Section 5 (explicit solutions): Theorems 6–10, Remark 11, three remarks -/

/-- **Theorem 6** (A388734, l. 258–260): every `a(n)` is odd. -/
def Thm6 : Prop := ∀ A : PowerSeries ℤ, Eq388734 A → ∀ n : ℕ, Odd (coeff n A)

/-- `φ = x(1 − x − x²)/(1 − x³)` (remark after Theorem 6, l. 271). -/
noncomputable def phi388734 : PowerSeries ℤ :=
  X * (1 - X - X ^ 2) * PowerSeries.invOfUnit (1 - X ^ 3) 1

/-- `B = (1 − x³)/(1 − x − x²)` (l. 271). -/
noncomputable def B388734 : PowerSeries ℤ :=
  (1 - X ^ 3) * PowerSeries.invOfUnit (1 - X - X ^ 2) 1

/-- Remark after Theorem 6 (l. 268–278), all its mathematical claims:
(a) `B` satisfies `B = 1 + φB² + φ²(1−φ)B³` and `φ = x/B`;
(b) two power-series solutions of `Y = 1 + φY² + φ²(1−φ)Y³` agree (existence is (a));
(c) `A(φ) = B` for every solution `A` of the defining equation;
(d) `xA` is the series reversion of `φ` (both compositions are `x`);
(e) `φ ≡ x/(1+x) (mod 2)`; (f) the reversion of `x/(1+x)` is `x/(1−x)` (mod 2);
(g) hence `A ≡ 1/(1−x) (mod 2)`. -/
def Rem6 : Prop :=
  (B388734 = 1 + phi388734 * B388734 ^ 2 + phi388734 ^ 2 * (1 - phi388734) * B388734 ^ 3 ∧
    phi388734 * B388734 = X) ∧
  (∀ Y Y' : PowerSeries ℤ,
    Y = 1 + phi388734 * Y ^ 2 + phi388734 ^ 2 * (1 - phi388734) * Y ^ 3 →
    Y' = 1 + phi388734 * Y' ^ 2 + phi388734 ^ 2 * (1 - phi388734) * Y' ^ 3 → Y = Y') ∧
  (∀ A : PowerSeries ℤ, Eq388734 A → A.subst phi388734 = B388734) ∧
  (∀ A : PowerSeries ℤ, Eq388734 A →
    (X * A).subst phi388734 = X ∧ phi388734.subst (X * A) = X) ∧
  (red 2 phi388734 = X * PowerSeries.invOfUnit (1 + X) 1) ∧
  ((X * PowerSeries.invOfUnit (1 + X) 1 : PowerSeries (ZMod 2)).subst
      (X * PowerSeries.invOfUnit (1 - X) 1 : PowerSeries (ZMod 2)) = X ∧
    (X * PowerSeries.invOfUnit (1 - X) 1 : PowerSeries (ZMod 2)).subst
      (X * PowerSeries.invOfUnit (1 + X) 1 : PowerSeries (ZMod 2)) = X) ∧
  (∀ A : PowerSeries ℤ, Eq388734 A → red 2 A = PowerSeries.invOfUnit (1 - X) 1)

/-- **Theorem 7** (A377100, l. 280–283): `a(0) = 0`, `a(1) = 1` ⟹ `a(n) ≡ 1 (mod 3)`, `n ≥ 1`. -/
def Thm7 : Prop :=
  ∀ A U : PowerSeries ℤ, constantCoeff A = 0 → coeff 1 A = 1 → Eq377100 A U →
    ∀ n : ℕ, 1 ≤ n → coeff n A ≡ 1 [ZMOD 3]

/-- **Theorem 8** (A274479, l. 293–296). -/
def Thm8 : Prop :=
  ∀ A : PowerSeries ℤ, constantCoeff A = 0 → coeff 1 A = 1 → Eq274479 A →
    ∀ n : ℕ, 1 ≤ n → coeff n A ≡ 1 [ZMOD 3]

/-- Remark after Theorem 8 (l. 304–309): (a) the entry's identity: `x/(1−x)` satisfies
`F² = F(x²/(1−2x+2x²))` over `ℤ`; (b) as `−4 ≡ 2 (mod 3)` this is the reduced equation:
`x²/(1−2x−4x²) ≡ x²/(1−2x+2x²) (mod 3)`. -/
def Rem8 : Prop :=
  (X * PowerSeries.invOfUnit (1 - X) 1 : PowerSeries ℤ) ^ 2 =
      (X * PowerSeries.invOfUnit (1 - X) 1 : PowerSeries ℤ).subst
        (X ^ 2 * PowerSeries.invOfUnit (1 - 2 * X + 2 * X ^ 2) 1 : PowerSeries ℤ) ∧
  red 3 h274479 = red 3 (X ^ 2 * PowerSeries.invOfUnit (1 - 2 * X + 2 * X ^ 2) 1)

/-- **Theorem 9** (A120566, l. 311–313): `a(0) = 0`, `a(1) = 1` ⟹ `a(n)` odd for `n ≥ 1`. -/
def Thm9 : Prop :=
  ∀ A : PowerSeries ℤ, constantCoeff A = 0 → coeff 1 A = 1 → Eq120566 A →
    ∀ n : ℕ, 1 ≤ n → Odd (coeff n A)

/-- The equation `B = B∘B + x·B∘B∘B` of the remark after Theorem 9 (l. 330). -/
def EqInv120566 (B : PowerSeries ℤ) : Prop :=
  B = B.subst B + X * B.subst (B.subst B)

/-- Remark after Theorem 9 (l. 327–334): (a) formula (2) of the entry, `A(−A(−x)) = x`;
(b) `−A(−x)` and the compositional inverse of `A` satisfy `B = B∘B + x B∘B∘B`;
(c) that equation has only one solution `B = x + O(x²)`;
(d) modulo 2, `−A(−x) ≡ A`, `F∘F = x` and `F = x/(1+x)`. -/
def Rem9 : Prop :=
  (∀ A : PowerSeries ℤ, constantCoeff A = 0 → coeff 1 A = 1 → Eq120566 A →
    A.subst (-(A.subst (-(X : PowerSeries ℤ)))) = X) ∧
  (∀ A : PowerSeries ℤ, constantCoeff A = 0 → coeff 1 A = 1 → Eq120566 A →
    EqInv120566 (-(A.subst (-(X : PowerSeries ℤ)))) ∧
    ∀ B : PowerSeries ℤ, constantCoeff B = 0 → A.subst B = X → B.subst A = X → EqInv120566 B) ∧
  (∀ B B' : PowerSeries ℤ, constantCoeff B = 0 → coeff 1 B = 1 → EqInv120566 B →
    constantCoeff B' = 0 → coeff 1 B' = 1 → EqInv120566 B' → B = B') ∧
  (∀ A : PowerSeries ℤ, constantCoeff A = 0 → coeff 1 A = 1 → Eq120566 A →
    red 2 (-(A.subst (-(X : PowerSeries ℤ)))) = red 2 A ∧
    (red 2 A).subst (red 2 A) = X ∧
    red 2 A = X * PowerSeries.invOfUnit (1 + X) 1)

/-- **Theorem 10** (A361047, l. 336–338): `A(0) = 0` and `A(x − x³A'²) = x` ⟹
`[x^m]A ≡ 1 (mod 3)` if `m` is a power of 3, and `≡ 0` otherwise. -/
def Thm10 : Prop :=
  ∀ A : PowerSeries ℤ, constantCoeff A = 0 → Eq361047 A → ∀ m : ℕ,
    ((∃ k : ℕ, m = 3 ^ k) → coeff m A ≡ 1 [ZMOD 3]) ∧
    ((¬ ∃ k : ℕ, m = 3 ^ k) → coeff m A ≡ 0 [ZMOD 3])

/-- Remark 11 (l. 351–354), the entry's indexing `A = ∑_{n ≥ 1} a(n) x^{2n−1}`:
the literal conjecture "`a(n) ≡ 1 (mod 3)` exactly for `n = (3^k−1)/2`, otherwise `≡ 0`" is
contradicted, because `a(2) = [x³]A = 1`. -/
def Rem11_literalFalse : Prop :=
  ∀ A : PowerSeries ℤ, constantCoeff A = 0 → Eq361047 A →
    coeff 3 A = 1 ∧
    ¬ (∀ n : ℕ, 1 ≤ n →
        (coeff (2 * n - 1) A ≡ 1 [ZMOD 3] ↔ ∃ k : ℕ, n = (3 ^ k - 1) / 2) ∧
        ((¬ ∃ k : ℕ, n = (3 ^ k - 1) / 2) → coeff (2 * n - 1) A ≡ 0 [ZMOD 3]))

/-- Remark 11 (l. 353–355): the statement is correct for the index `i = n − 1`
(coefficient of `x^{2i+1}`); "Theorem 10 is this intended statement". -/
def Rem11_intended : Prop :=
  ∀ A : PowerSeries ℤ, constantCoeff A = 0 → Eq361047 A → ∀ i : ℕ,
    (coeff (2 * i + 1) A ≡ 1 [ZMOD 3] ↔ ∃ k : ℕ, i = (3 ^ k - 1) / 2) ∧
    ((¬ ∃ k : ℕ, i = (3 ^ k - 1) / 2) → coeff (2 * i + 1) A ≡ 0 [ZMOD 3])

/-- Remark 11 (l. 357–359): over `ℤ` the reversion of `x − x³` is `V = ∑ t(k) x^{2k+1}`,
"since `V − V³ = x`" (both compositions are `x`). -/
def Rem11_ternaryReversion : Prop :=
  ternarySeries - ternarySeries ^ 3 = X ∧
  ((X : PowerSeries ℤ) - X ^ 3).subst ternarySeries = X ∧
  ternarySeries.subst ((X : PowerSeries ℤ) - X ^ 3) = X

/-- Remark 11 (l. 359–360): "Modulo 3 this reversion is `S = ∑ x^{3^k}`, so Theorem 10 says
that `a(n) ≡ t(n−1) (mod 3)`". -/
def Rem11_mod3 : Prop :=
  (∀ m : ℕ, ((∃ k : ℕ, m = 3 ^ k) → coeff m ternarySeries ≡ 1 [ZMOD 3]) ∧
    ((¬ ∃ k : ℕ, m = 3 ^ k) → coeff m ternarySeries ≡ 0 [ZMOD 3])) ∧
  (∀ A : PowerSeries ℤ, constantCoeff A = 0 → Eq361047 A →
    ∀ n : ℕ, 1 ≤ n → coeff (2 * n - 1) A ≡ (ternary (n - 1) : ℤ) [ZMOD 3])

/-- Remark 11 (l. 360–362): A113047, conjectured by Barry and proved by Ryde (2021):
`t(k) mod 3` is `1` for `k = (3^j − 1)/2` and `0` otherwise. -/
def Rem11_A113047 : Prop :=
  ∀ k : ℕ, ((∃ j : ℕ, k = (3 ^ j - 1) / 2) → (ternary k : ℤ) ≡ 1 [ZMOD 3]) ∧
    ((¬ ∃ j : ℕ, k = (3 ^ j - 1) / 2) → (ternary k : ℤ) ≡ 0 [ZMOD 3])

/-- Remark 11 (l. 363–366): the remaining step, `F = S` with `S = ∑_k x^{3^k}` over `𝔽₃`, "or
equivalently `F' = 1`", which reduces the equation mod 3 to `F(x − x³) = x`. For every solution of the
reduced equation with `F(0) = 0`: `F' = 1`, `F(x − x³) = x`, and `F = S` (coefficientwise). That `S` is
the reduction of `V` is the first half of `Rem11_mod3`. -/
def Rem11_remainingStep : Prop :=
  ∀ F : PowerSeries (ZMod 3), constantCoeff F = 0 →
    F.subst ((X : PowerSeries (ZMod 3)) - X ^ 3 * (derivative (R := ZMod 3) F) ^ 2) = X →
    derivative (R := ZMod 3) F = 1 ∧ F.subst ((X : PowerSeries (ZMod 3)) - X ^ 3) = X ∧
    ∀ m : ℕ, ((∃ k : ℕ, m = 3 ^ k) → coeff m F = 1) ∧ ((¬ ∃ k : ℕ, m = 3 ^ k) → coeff m F = 0)

/-! ## 6. Section 6 (additive series modulo three): Theorems 12, 13, text and final remark -/

/-- l. 371–372: the composition of two additive series is additive. -/
def Sec6_additiveComp : Prop :=
  ∀ G H : PowerSeries (ZMod 3), Additive3 G → Additive3 H → Additive3 (G.subst H)

/-- **Theorem 12(1)** (A184894, l. 377): if `2m − 1` is not a power of 3, then `3 ∣ a(m)`. -/
def Thm12_1 : Prop :=
  ∀ m : ℕ, 1 ≤ m → (¬ ∃ j : ℕ, 2 * m - 1 = 3 ^ j) → (3 : ℤ) ∣ a184894 m

/-- **Theorem 12(2)** (l. 378): if `2m − 1 = 3^j`, then `a(m) ≡ binom(m, j) (mod 3)`. -/
def Thm12_2 : Prop :=
  ∀ m j : ℕ, 1 ≤ m → 2 * m - 1 = 3 ^ j → a184894 m ≡ (m.choose j : ℤ) [ZMOD 3]

/-- **Theorem 12(3)** (l. 379): `3 ∣ a(365)`, although `2·365 − 1 = 3⁶`. -/
def Thm12_3 : Prop := 2 * 365 - 1 = 3 ^ 6 ∧ (3 : ℤ) ∣ a184894 365

/-- l. 390–392: the entry's conjecture as written, "`a(m) ≡ 0 (mod 3)` except at
`m = (3^n+1)/2`" (vanishing outside the exceptional indices), is proved. -/
def Thm12_entryLiteral : Prop :=
  ∀ m : ℕ, 1 ≤ m → (∀ n : ℕ, m ≠ (3 ^ n + 1) / 2) → (3 : ℤ) ∣ a184894 m

/-- l. 392–394: the stronger reading (non-zero mod 3 at every exceptional index) is false,
and the first failure is at `n = 6`. -/
def Thm12_firstFailure : Prop :=
  (∀ n : ℕ, n < 6 → ¬ (3 : ℤ) ∣ a184894 ((3 ^ n + 1) / 2)) ∧ (3 : ℤ) ∣ a184894 ((3 ^ 6 + 1) / 2)

/-- l. 394–395: by Lucas's theorem, `a((3^n+1)/2) ≢ 0 (mod 3)` exactly when every base-3
digit of `n` except the last is at most 1. -/
def Thm12_digits : Prop :=
  ∀ n : ℕ, ¬ (3 : ℤ) ∣ a184894 ((3 ^ n + 1) / 2) ↔ digitsExceptLastLeOne n

/-- **Theorem 13, first claim** (A107099, l. 397–399): `A(0) = 0`, `[x¹]A = 1`,
`A∘A = x + 4x³` ⟹ `3 ∣ [xⁿ]A` whenever `n` is not a power of 3 (this is also the entry's
conjecture "as written", l. 412–414). -/
def Thm13_1 : Prop :=
  ∀ A : PowerSeries ℤ, constantCoeff A = 0 → coeff 1 A = 1 → Eq107099 A →
    ∀ n : ℕ, (¬ ∃ k : ℕ, n = 3 ^ k) → (3 : ℤ) ∣ coeff n A

/-- **Theorem 13, second claim** (l. 399): `3 ∣ [x^{729}]A`; with the entry's indexing
`A = ∑ a(n) x^{2n+1}` this is `a(364)` (l. 415). -/
def Thm13_2 : Prop :=
  (2 * 364 + 1 = 729 ∧ 729 = 3 ^ 6) ∧
  ∀ A : PowerSeries ℤ, constantCoeff A = 0 → coeff 1 A = 1 → Eq107099 A → (3 : ℤ) ∣ coeff 729 A

/-- Proof of Theorem 13 (l. 409): `(c₁, …, c₆) = (2, 1, 1, 2, 1, 0)` with `c_k = [x^{3^k}]A`
mod 3 (so the first failure of non-vanishing at a power of 3 is at `3⁶`). -/
def Thm13_values : Prop :=
  ∀ A : PowerSeries ℤ, constantCoeff A = 0 → coeff 1 A = 1 → Eq107099 A →
    coeff 3 A ≡ 2 [ZMOD 3] ∧ coeff 9 A ≡ 1 [ZMOD 3] ∧ coeff 27 A ≡ 1 [ZMOD 3] ∧
    coeff 81 A ≡ 2 [ZMOD 3] ∧ coeff 243 A ≡ 1 [ZMOD 3] ∧ coeff 729 A ≡ 0 [ZMOD 3]

/-- Final remark (l. 419–423): the correspondence of linearised series over `𝔽₃` with their
3-associates, under which composition is multiplication: the `3^k` coefficient of `G∘H` is
`∑_{i+j=k} g_i h_j`. -/
def Rem13_correspondence : Prop :=
  ∀ G H : PowerSeries (ZMod 3), Additive3 G → Additive3 H → ∀ k : ℕ,
    coeff (3 ^ k) (G.subst H) =
      ∑ i ∈ Finset.range (k + 1), coeff (3 ^ i) G * coeff (3 ^ (k - i)) H

/-- Final remark (l. 423–424): `P_m ≡ ∑_j binom(m, j) x^{3^j} (mod 3)`. -/
def Rem13_PmMod3 : Prop :=
  ∀ m : ℕ, (P184894 m).map (Int.castRingHom (ZMod 3)) =
    ∑ j ∈ Finset.range (m + 1), Polynomial.C ((m.choose j : ℕ) : ZMod 3) * Polynomial.X ^ (3 ^ j)

/-- Final remark (l. 424–430): `∑_j binom(1/2,j) x^{3^j}` composes with itself to `x + x³`
mod 3, and the reduction `F` of Theorem 13 is this series. -/
def Rem13_sqrtSeries : Prop :=
  sqrtSeries3.subst sqrtSeries3 = X + X ^ 3 ∧
  ∀ A : PowerSeries ℤ, constantCoeff A = 0 → coeff 1 A = 1 → Eq107099 A → red 3 A = sqrtSeries3

/-- Final remark (l. 431): for `j ≥ 1`, `binom(1/2, j) = 2(−1)^{j−1} C_{j−1}/4^j`
`≡ (−1)^j C_{j−1} (mod 3)`. -/
def Rem13_binomHalf : Prop :=
  ∀ j : ℕ, 1 ≤ j →
    Ring.choose (1 / 2 : ℚ) j = 2 * (-1) ^ (j - 1) * (catalan (j - 1) : ℚ) / 4 ^ j ∧
    ((Ring.choose (1 / 2 : ℚ) j : ℚ) : ZMod 3) = (-1) ^ j * (catalan (j - 1) : ZMod 3)

/-- Final remark (l. 432–433): `binom((3^j+1)/2, j) ≡ binom(1/2, j) (mod 3)` (Lucas). -/
def Rem13_lucasHalf : Prop :=
  ∀ j : ℕ, ((Nat.choose ((3 ^ j + 1) / 2) j : ℕ) : ZMod 3) = ((Ring.choose (1 / 2 : ℚ) j : ℚ) : ZMod 3)

/-- Final remark (l. 433–434): in both entries the residue at an exceptional index with
`j ≥ 1` is `(−1)^j C_{j−1}` modulo 3. -/
def Rem13_residues : Prop :=
  (∀ j : ℕ, 1 ≤ j → a184894 ((3 ^ j + 1) / 2) ≡ (-1) ^ j * (catalan (j - 1) : ℤ) [ZMOD 3]) ∧
  (∀ A : PowerSeries ℤ, constantCoeff A = 0 → coeff 1 A = 1 → Eq107099 A →
    ∀ j : ℕ, 1 ≤ j → coeff (3 ^ j) A ≡ (-1) ^ j * (catalan (j - 1) : ℤ) [ZMOD 3])

/-- Final remark (l. 435–436): by Deutsch–Sagan (Theorem 5.2 of arXiv:math/0407326v1),
`C_{j−1} ≢ 0 (mod 3)` exactly when every base-3 digit of `j` except the last is 0 or 1. -/
def Rem13_DS52 : Prop :=
  ∀ j : ℕ, 1 ≤ j → (¬ 3 ∣ catalan (j - 1) ↔ digitsExceptLastLeOne j)

/-- Final remark (l. 436–437): "Both failures come from `3 ∣ C₅ = 42`". -/
def Rem13_C5 : Prop := catalan 5 = 42 ∧ 3 ∣ catalan 5

/-! ## 7. Section 7 (verification): the quoted Lean statement -/

/-- l. 456–461: the Lean statement quoted in the paper for A273958 (ASCII in the paper). The
check file must show that the released declaration `HannaA273958.hanna_a273958` has exactly
this type. -/
def Sec7_quotedA273958 : Prop :=
  ∀ (Cs A : PowerSeries ℤ), Cs = X + Cs ^ 2 → X * A + X ^ 2 * A ^ 2 = Cs ^ 2 → ∀ n : ℕ,
    (Odd (coeff n A) ↔ ∃ k : ℕ, n + 1 = 2 * 4 ^ k)

/-! ## 8. Section 1: existence and uniqueness (asserted, l. 83–91; not formalized so far)

"The equation and these initial terms determine the sequence by a triangular recursion with
integer solutions. … Hence the theorems apply to the sequences in the OEIS." The
normalizations are those of the theorems, plus those fixed by the entries where the equation
alone does not determine the series (A389472: `a(2) = 1`; A240998: `a(0) = 1`). -/

def EX_A389472 : Prop := ∃! A : PowerSeries ℤ, coeff 2 A = 1 ∧ Eq389472 A
def EX_A240998 : Prop := ∃! A : PowerSeries ℤ, constantCoeff A = 1 ∧ Eq240998 A
def EX_A295762 : Prop := ∃! A : PowerSeries ℤ, constantCoeff A = 0 ∧ Eq295762 A
def EX_A301933 : Prop := ∃! A : PowerSeries ℤ, constantCoeff A = 0 ∧ Eq301933 A
def EX_A338633 : Prop := ∃! A : PowerSeries ℤ, ∃ T : ℕ → PowerSeries ℤ, CF 3 A T
def EX_A338634 : Prop := ∃! A : PowerSeries ℤ, ∃ T : ℕ → PowerSeries ℤ, CF 4 A T
def EX_A273958 : Prop := ∃! p : PowerSeries ℤ × PowerSeries ℤ, Eq273958 p.1 p.2
def EX_A388734 : Prop := ∃! A : PowerSeries ℤ, Eq388734 A
def EX_A377100 : Prop :=
  ∃! A : PowerSeries ℤ, constantCoeff A = 0 ∧ coeff 1 A = 1 ∧ ∃ U : PowerSeries ℤ, Eq377100 A U
def EX_A274479 : Prop :=
  ∃! A : PowerSeries ℤ, constantCoeff A = 0 ∧ coeff 1 A = 1 ∧ Eq274479 A
def EX_A120566 : Prop :=
  ∃! A : PowerSeries ℤ, constantCoeff A = 0 ∧ coeff 1 A = 1 ∧ Eq120566 A
def EX_A361047 : Prop := ∃! A : PowerSeries ℤ, constantCoeff A = 0 ∧ Eq361047 A
def EX_A107099 : Prop :=
  ∃! A : PowerSeries ℤ, constantCoeff A = 0 ∧ coeff 1 A = 1 ∧ Eq107099 A

/-! ## 9. Data gate (playbook 3.5.1): the solutions have the entries' first terms

These make "the theorems apply to the sequences in the OEIS" checkable: with the uniqueness
part of `EX_*`, the series of each theorem is the entry's sequence. Values from the local
b-files `certificates/oeis-hanna/bfiles/` and `b389472.txt`. -/

def DATA_A389472 : Prop := ∀ A : PowerSeries ℤ, coeff 2 A = 1 → Eq389472 A →
  coeff 0 A = 0 ∧ coeff 1 A = 1 ∧ coeff 3 A = 2 ∧ coeff 4 A = 3 ∧ coeff 5 A = 6 ∧ coeff 6 A = 9
def DATA_A240998 : Prop := ∀ A : PowerSeries ℤ, constantCoeff A = 1 → Eq240998 A →
  coeff 1 A = 1 ∧ coeff 2 A = 1 ∧ coeff 3 A = 2 ∧ coeff 4 A = 11 ∧ coeff 5 A = 86
def DATA_A295762 : Prop := ∀ A : PowerSeries ℤ, constantCoeff A = 0 → Eq295762 A →
  coeff 1 A = 1 ∧ coeff 2 A = 3 ∧ coeff 3 A = 12 ∧ coeff 4 A = 69 ∧ coeff 5 A = 444
def DATA_A301933 : Prop := ∀ A : PowerSeries ℤ, constantCoeff A = 0 → Eq301933 A →
  coeff 1 A = 1 ∧ coeff 2 A = 3 ∧ coeff 3 A = 24 ∧ coeff 4 A = 291 ∧ coeff 5 A = 4596
def DATA_A338633 : Prop := ∀ (A : PowerSeries ℤ) (T : ℕ → PowerSeries ℤ), CF 3 A T →
  coeff 0 A = 1 ∧ coeff 1 A = 1 ∧ coeff 2 A = 7 ∧ coeff 3 A = 250 ∧ coeff 4 A = 21867
def DATA_A338634 : Prop := ∀ (A : PowerSeries ℤ) (T : ℕ → PowerSeries ℤ), CF 4 A T →
  coeff 0 A = 1 ∧ coeff 1 A = 1 ∧ coeff 2 A = 15 ∧ coeff 3 A = 1490 ∧ coeff 4 A = 472475
def DATA_A273958 : Prop := ∀ Cs A : PowerSeries ℤ, Eq273958 Cs A →
  coeff 0 A = 0 ∧ coeff 1 A = 1 ∧ coeff 2 A = 2 ∧ coeff 3 A = 4 ∧ coeff 4 A = 10 ∧ coeff 5 A = 30
def DATA_A388734 : Prop := ∀ A : PowerSeries ℤ, Eq388734 A →
  coeff 0 A = 1 ∧ coeff 1 A = 1 ∧ coeff 2 A = 3 ∧ coeff 3 A = 9 ∧ coeff 4 A = 33 ∧ coeff 5 A = 127
def DATA_A377100 : Prop := ∀ A U : PowerSeries ℤ, constantCoeff A = 0 → coeff 1 A = 1 →
  Eq377100 A U → coeff 2 A = 1 ∧ coeff 3 A = 1 ∧ coeff 4 A = 4 ∧ coeff 5 A = 10 ∧ coeff 6 A = 28
def DATA_A274479 : Prop := ∀ A : PowerSeries ℤ, constantCoeff A = 0 → coeff 1 A = 1 →
  Eq274479 A → coeff 2 A = 1 ∧ coeff 3 A = 4 ∧ coeff 4 A = 10 ∧ coeff 5 A = 34 ∧ coeff 6 A = 106
def DATA_A120566 : Prop := ∀ A : PowerSeries ℤ, constantCoeff A = 0 → coeff 1 A = 1 →
  Eq120566 A → coeff 2 A = 1 ∧ coeff 3 A = 1 ∧ coeff 4 A = 3 ∧ coeff 5 A = 7 ∧ coeff 6 A = 33
def DATA_A361047 : Prop := ∀ A : PowerSeries ℤ, constantCoeff A = 0 → Eq361047 A →
  coeff 1 A = 1 ∧ coeff 2 A = 0 ∧ coeff 3 A = 1 ∧ coeff 4 A = 0 ∧ coeff 5 A = 9 ∧ coeff 7 A = 159
def DATA_A107099 : Prop := ∀ A : PowerSeries ℤ, constantCoeff A = 0 → coeff 1 A = 1 →
  Eq107099 A → coeff 2 A = 0 ∧ coeff 3 A = 2 ∧ coeff 5 A = -6 ∧ coeff 7 A = 36 ∧ coeff 9 A = -266
def DATA_A184894 : Prop :=
  a184894 1 = 1 ∧ a184894 2 = 2 ∧ a184894 3 = 9 ∧ a184894 4 = 78 ∧ a184894 5 = 1045

end BackfillPaper2.Challenge
