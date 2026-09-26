import Mathlib
import Research.ICGEqualParityUnique

set_option autoImplicit false

/-!
# Theorem B (round 6): the column algebra of `T₂(p)`

Formalisation of the one-column lemmas of `work/round6/equal-parity-a2/PROOF.md` (§1–§5).
Notation: `P = p - 1`, `Q = q - 1`.  A column `c = (c₀,c₁,c₂)` of the sign matrix is mapped by
`M = T₂(p)` to `(Mc0, Mc1, Mc2)`.  For `A = M c` and a state `B = M ζ`,

  `Sc P Q μ A B = Q(1+μ)(D_p - ‖A‖₁) - Σ_i h_μ(A_i, B_i)`

is `q` times the column surplus `s(c, ζ)` of the note (`D_p = d₂(p) = 5P² + 2P + 1`,
`h` is the cell function `ICGGeneral.hcell` with first argument `Q`).

* `lemS`: Lemma S (`Sc ≥ 0`, and `> 0` unless `c = ±s₂`) for every state in the box
  `|B₀|, |B₁| ≤ 2pP`, `|B₂| ≤ p²`.
* `fd1`: Lemma FD1 (first deviation from the anti-checkerboard, state `m·α(A)`).
* `fd2a`, `fd2dom`, `two_col`: the pieces of Lemma FD2 (last column `B = (1,1,-1)`).
* `hc_zero_imp`, `hc_zero_imp'`: sign information from a vanishing cell (Lemma EQ).

The Lean route uses the crude parameter box `μ, m ∈ [μ₀, 1]`, `ρ ≤ μ₁` (plus the exact
relations for the Copp deviation) instead of the regime-by-regime vertex certificates of
`prove_fd.py`; the resulting polynomial inequalities are `poly_I1` … `poly_I7`, each proved by
the substitution `P = 4 + u²`, `Q = 2 + v²` (resp. `P = 2`, `Q = 4 + v²`) and
`ring_nf; positivity`.
-/

noncomputable section

namespace ICGEqualParityB

open Finset ICGGeneral ICGEqualParity

/-! ### Helpers -/

lemma exists_add_sq {P c : ℝ} (h : c ≤ P) : ∃ u : ℝ, P = c + u ^ 2 :=
  ⟨Real.sqrt (P - c), by rw [Real.sq_sqrt (by linarith)]; ring⟩

lemma aff_pos {α β t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) (ha : 0 < α) (hb : 0 < α + β) :
    0 < α + β * t := by
  rcases le_total 0 β with hβ | hβ
  · nlinarith [mul_nonneg hβ h0]
  · nlinarith [mul_nonneg (neg_nonneg.mpr hβ) (sub_nonneg.mpr h1)]

lemma bilin_pos {a b c d x y : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hy0 : 0 ≤ y) (hy1 : y ≤ 1)
    (h00 : 0 < a) (h10 : 0 < a + b) (h01 : 0 < a + c) (h11 : 0 < a + b + c + d) :
    0 < a + b * x + c * y + d * x * y := by
  have h1 : 0 < a + b * x := aff_pos hx0 hx1 h00 h10
  have h2 : 0 < (a + c) + (b + d) * x := aff_pos hx0 hx1 h01 (by linarith)
  have h3 : 0 < (a + b * x) + (c + d * x) * y := aff_pos hy0 hy1 h1 (by linarith)
  linarith [h3]

/-- Clearing the bound `ρ ≤ μ₁ = (Q²+1)/(Q+1)²`. -/
lemma need_of {P Q ρ X : ℝ} (hQ : 0 < Q + 1) (hρ : (Q + 1) ^ 2 * ρ ≤ Q ^ 2 + 1)
    (h : 2 * (P ^ 2 + 1) * (Q ^ 2 + 1) < (Q + 1) * X) : 2 * (Q + 1) * (P ^ 2 + 1) * ρ < X := by
  have hP : 0 < P ^ 2 + 1 := by positivity
  have h1 : (Q + 1) * (2 * (Q + 1) * (P ^ 2 + 1) * ρ) ≤ 2 * (P ^ 2 + 1) * (Q ^ 2 + 1) := by
    have := mul_le_mul_of_nonneg_left hρ (by positivity : (0:ℝ) ≤ 2 * (P ^ 2 + 1))
    nlinarith
  by_contra hc
  push Not at hc
  have := mul_le_mul_of_nonneg_left hc hQ.le
  linarith

/-! ### Exact values of the cell function `h_μ(A,B)` -/

lemma hc_same_neg {Q μ A B : ℝ} (hμ0 : 0 ≤ μ) (hQμ : μ ≤ Q) (hB : B ≤ 0) (hAB : A ≤ B) :
    hcell Q μ A B = 2 * (Q - μ) * B := by
  rw [← hcell_neg, hcell_same_pos hμ0 hQμ (by linarith) (by linarith)]
  ring

lemma hc_big_pos {Q μ A B : ℝ} (hQ : 0 ≤ Q) (hA : 0 ≤ A) (hAB : A ≤ B) :
    hcell Q μ A B = 2 * μ * B - 2 * Q * A := by
  unfold hcell
  rw [abs_of_nonpos (by linarith : A - B ≤ 0), abs_of_nonneg (by nlinarith : 0 ≤ B + Q * A),
    abs_of_nonneg (by linarith : 0 ≤ B), abs_of_nonneg hA]
  ring

lemma hc_big_neg {Q μ A B : ℝ} (hQ : 0 ≤ Q) (hA : A ≤ 0) (hAB : B ≤ A) :
    hcell Q μ A B = -(2 * μ * B) + 2 * Q * A := by
  rw [← hcell_neg, hc_big_pos hQ (by linarith) (by linarith)]
  ring

lemma hc_opp_big {Q μ A B : ℝ} (hQ : 0 ≤ Q) (hA : 0 ≤ A) (hBA : B ≤ -(Q * A)) :
    hcell Q μ A B = 2 * μ * (-B - Q * A) := by
  have hB : B ≤ 0 := by nlinarith
  unfold hcell
  rw [abs_of_nonneg (by linarith : 0 ≤ A - B), abs_of_nonpos (by linarith : B + Q * A ≤ 0),
    abs_of_nonpos hB, abs_of_nonneg hA]
  ring

/-- A vanishing cell with `A > 0` and `|B| < QA` forces `B ≤ 0`. -/
lemma hc_zero_imp {Q μ A B : ℝ} (hμ0 : 0 ≤ μ) (hμ1 : μ ≤ 1) (hQ : 1 < Q) (hA : 0 < A)
    (hB : |B| < Q * A) (h : hcell Q μ A B = 0) : B ≤ 0 := by
  by_contra hpos
  push Not at hpos
  rw [abs_of_pos hpos] at hB
  rcases le_total B A with hBA | hBA
  · rw [hcell_same_pos hμ0 (by linarith) hpos.le hBA] at h
    have : 0 < (Q - μ) * B := mul_pos (by linarith) hpos
    linarith
  · rw [hc_big_pos (by linarith) hA.le hBA] at h
    have : μ * B ≤ B := by nlinarith
    linarith

lemma hc_zero_imp' {Q μ A B : ℝ} (hμ0 : 0 ≤ μ) (hμ1 : μ ≤ 1) (hQ : 1 < Q) (hA : A < 0)
    (hB : |B| < Q * (-A)) (h : hcell Q μ A B = 0) : 0 ≤ B := by
  have h' : hcell Q μ (-A) (-B) = 0 := by rw [hcell_neg]; exact h
  have := hc_zero_imp hμ0 hμ1 hQ (by linarith) (by rwa [abs_neg]) h'
  linarith

/-! ### Columns and the column surplus -/

/-- Row `0` of `T₂(p) c` (`P = p - 1`). -/
def Mc0 (P _c0 c1 c2 : ℝ) : ℝ := P * (P + 1) * (c2 - c1)
/-- Row `1` of `T₂(p) c`. -/
def Mc1 (P c0 c1 c2 : ℝ) : ℝ := -(P * (P + 1)) * c0 + P ^ 2 * c1 + P * c2
/-- Row `2` of `T₂(p) c`. -/
def Mc2 (P c0 c1 c2 : ℝ) : ℝ := P * (P + 1) * c0 + P * c1 + c2

/-- `d₂(p) = ‖T₂(p) s₂‖₁ = 5P² + 2P + 1` (`P = p - 1`). -/
def Dp (P : ℝ) : ℝ := 5 * P ^ 2 + 2 * P + 1

/-- `q` times the column surplus `s(c, ζ)` (with `A = T₂(p) c`, `B = T₂(p) ζ`). -/
def Sc (P Q μ A0 A1 A2 B0 B1 B2 : ℝ) : ℝ :=
  Q * (1 + μ) * (Dp P - (|A0| + |A1| + |A2|)) -
    (hcell Q μ A0 B0 + hcell Q μ A1 B1 + hcell Q μ A2 B2)

/-- The parameter range of Theorem B′ in terms of `P = p - 1`, `Q = q - 1`:
`p ≥ 5, q ≥ 3` or `p = 3, q ≥ 5`. -/
def PQok (P Q : ℝ) : Prop := (4 ≤ P ∧ 2 ≤ Q) ∨ (P = 2 ∧ 4 ≤ Q)

lemma PQok.two {P Q : ℝ} (h : PQok P Q) : 2 ≤ P ∧ 2 ≤ Q := by
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> constructor <;> linarith

lemma k_le_Qg {P Q : ℝ} (h : PQok P Q) : (P + 1) ^ 2 ≤ Q * (P ^ 2 - 1) := by
  rcases h with ⟨hP, hQ⟩ | ⟨rfl, hQ⟩
  · nlinarith [mul_le_mul_of_nonneg_right hQ (by nlinarith : (0:ℝ) ≤ P ^ 2 - 1)]
  · nlinarith

lemma Sc_neg (P Q μ A0 A1 A2 B0 B1 B2 : ℝ) :
    Sc P Q μ (-A0) (-A1) (-A2) (-B0) (-B1) (-B2) = Sc P Q μ A0 A1 A2 B0 B1 B2 := by
  unfold Sc
  rw [hcell_neg, hcell_neg, hcell_neg, abs_neg, abs_neg, abs_neg]

lemma Sc_neg' (P Q μ A0 A1 A2 B0 B1 B2 : ℝ) :
    Sc P Q μ (-A0) (-A1) (-A2) B0 B1 B2 = Sc P Q μ A0 A1 A2 (-B0) (-B1) (-B2) := by
  rw [← Sc_neg P Q μ A0 A1 A2 (-B0) (-B1) (-B2), neg_neg, neg_neg, neg_neg]

/-- The "Lemma S bound" `h ≤ 2μ max(0, |B| - Q|A|)` applied to the three cells. -/
lemma Sc_lower {P Q μ A0 A1 A2 B0 B1 B2 : ℝ} (hμ0 : 0 ≤ μ) (hμ1 : μ ≤ 1) (hQ : 1 ≤ Q) :
    Q * (1 + μ) * (Dp P - (|A0| + |A1| + |A2|)) -
        2 * μ * (max 0 (|B0| - Q * |A0|) + max 0 (|B1| - Q * |A1|) +
          max 0 (|B2| - Q * |A2|)) ≤ Sc P Q μ A0 A1 A2 B0 B1 B2 := by
  unfold Sc
  have h0 := hcell_le hμ0 hμ1 (by linarith : μ ≤ Q) A0 B0
  have h1 := hcell_le hμ0 hμ1 (by linarith : μ ≤ Q) A1 B1
  have h2 := hcell_le hμ0 hμ1 (by linarith : μ ≤ Q) A2 B2
  nlinarith

/-- If all three cells are small (`|B_i| ≤ Q|A_i|`) they are `≤ 0`. -/
lemma Sc_ge_small {P Q μ A0 A1 A2 B0 B1 B2 : ℝ} (hμ0 : 0 ≤ μ) (hμ1 : μ ≤ 1) (hQ : 1 ≤ Q)
    (h0 : |B0| ≤ Q * |A0|) (h1 : |B1| ≤ Q * |A1|) (h2 : |B2| ≤ Q * |A2|) :
    Q * (1 + μ) * (Dp P - (|A0| + |A1| + |A2|)) ≤ Sc P Q μ A0 A1 A2 B0 B1 B2 := by
  unfold Sc
  have c0 := hcell_nonpos hμ0 hμ1 (by linarith : μ ≤ Q) h0
  have c1 := hcell_nonpos hμ0 hμ1 (by linarith : μ ≤ Q) h1
  have c2 := hcell_nonpos hμ0 hμ1 (by linarith : μ ≤ Q) h2
  linarith

/-! ### The eight columns -/

lemma col_A (P : ℝ) : Mc0 P 1 (-1) 1 = 2 * P * (P + 1) ∧ Mc1 P 1 (-1) 1 = -(2 * P ^ 2) ∧
    Mc2 P 1 (-1) 1 = P ^ 2 + 1 := by
  refine ⟨?_, ?_, ?_⟩ <;> simp only [Mc0, Mc1, Mc2] <;> ring

lemma col_nA (P : ℝ) : Mc0 P (-1) 1 (-1) = -(2 * P * (P + 1)) ∧ Mc1 P (-1) 1 (-1) = 2 * P ^ 2 ∧
    Mc2 P (-1) 1 (-1) = -(P ^ 2 + 1) := by
  refine ⟨?_, ?_, ?_⟩ <;> simp only [Mc0, Mc1, Mc2] <;> ring

lemma col_B (P : ℝ) : Mc0 P 1 1 (-1) = -(2 * P * (P + 1)) ∧ Mc1 P 1 1 (-1) = -(2 * P) ∧
    Mc2 P 1 1 (-1) = P ^ 2 + 2 * P - 1 := by
  refine ⟨?_, ?_, ?_⟩ <;> simp only [Mc0, Mc1, Mc2] <;> ring

lemma col_nB (P : ℝ) : Mc0 P (-1) (-1) 1 = 2 * P * (P + 1) ∧ Mc1 P (-1) (-1) 1 = 2 * P ∧
    Mc2 P (-1) (-1) 1 = -(P ^ 2 + 2 * P - 1) := by
  refine ⟨?_, ?_, ?_⟩ <;> simp only [Mc0, Mc1, Mc2] <;> ring

lemma col_C (P : ℝ) : Mc0 P 1 (-1) (-1) = 0 ∧ Mc1 P 1 (-1) (-1) = -(2 * P * (P + 1)) ∧
    Mc2 P 1 (-1) (-1) = P ^ 2 - 1 := by
  refine ⟨?_, ?_, ?_⟩ <;> simp only [Mc0, Mc1, Mc2] <;> ring

lemma col_nC (P : ℝ) : Mc0 P (-1) 1 1 = 0 ∧ Mc1 P (-1) 1 1 = 2 * P * (P + 1) ∧
    Mc2 P (-1) 1 1 = -(P ^ 2 - 1) := by
  refine ⟨?_, ?_, ?_⟩ <;> simp only [Mc0, Mc1, Mc2] <;> ring

lemma col_E (P : ℝ) : Mc0 P 1 1 1 = 0 ∧ Mc1 P 1 1 1 = 0 ∧ Mc2 P 1 1 1 = (P + 1) ^ 2 := by
  refine ⟨?_, ?_, ?_⟩ <;> simp only [Mc0, Mc1, Mc2] <;> ring

lemma col_nE (P : ℝ) : Mc0 P (-1) (-1) (-1) = 0 ∧ Mc1 P (-1) (-1) (-1) = 0 ∧
    Mc2 P (-1) (-1) (-1) = -((P + 1) ^ 2) := by
  refine ⟨?_, ?_, ?_⟩ <;> simp only [Mc0, Mc1, Mc2] <;> ring

/-- `|T₂(p) c| ≤ (2pP, 2pP, p²)` entrywise for `c ∈ [-1,1]³`. -/
lemma Mc_abs_le {P c0 c1 c2 : ℝ} (hP : 0 ≤ P) (h0 : |c0| ≤ 1) (h1 : |c1| ≤ 1) (h2 : |c2| ≤ 1) :
    |Mc0 P c0 c1 c2| ≤ 2 * P * (P + 1) ∧ |Mc1 P c0 c1 c2| ≤ 2 * P * (P + 1) ∧
      |Mc2 P c0 c1 c2| ≤ (P + 1) ^ 2 := by
  rw [abs_le] at h0 h1 h2
  obtain ⟨a0, b0⟩ := h0
  obtain ⟨a1, b1⟩ := h1
  obtain ⟨a2, b2⟩ := h2
  have hPP : 0 ≤ P * (P + 1) := by nlinarith
  have hP2 : 0 ≤ P ^ 2 := by positivity
  refine ⟨?_, ?_, ?_⟩ <;> rw [abs_le] <;> simp only [Mc0, Mc1, Mc2] <;> constructor
  · nlinarith [mul_nonneg hPP (by linarith : (0:ℝ) ≤ 1 - c2), mul_nonneg hPP (by linarith : (0:ℝ) ≤ 1 + c1)]
  · nlinarith [mul_nonneg hPP (by linarith : (0:ℝ) ≤ 1 + c2), mul_nonneg hPP (by linarith : (0:ℝ) ≤ 1 - c1)]
  · nlinarith [mul_nonneg hPP (by linarith : (0:ℝ) ≤ 1 - c0), mul_nonneg hP2 (by linarith : (0:ℝ) ≤ 1 + c1),
      mul_nonneg hP (by linarith : (0:ℝ) ≤ 1 + c2)]
  · nlinarith [mul_nonneg hPP (by linarith : (0:ℝ) ≤ 1 + c0), mul_nonneg hP2 (by linarith : (0:ℝ) ≤ 1 - c1),
      mul_nonneg hP (by linarith : (0:ℝ) ≤ 1 - c2)]
  · nlinarith [mul_nonneg hPP (by linarith : (0:ℝ) ≤ 1 + c0), mul_nonneg hP (by linarith : (0:ℝ) ≤ 1 + c1)]
  · nlinarith [mul_nonneg hPP (by linarith : (0:ℝ) ≤ 1 - c0), mul_nonneg hP (by linarith : (0:ℝ) ≤ 1 - c1)]

/-! ### Polynomial inequalities (all coefficients `≥ 0` after the substitution) -/

section Poly

variable {P Q : ℝ}

lemma poly_I1 (h : PQok P Q) :
    0 < (Q - 1) ^ 2 * (5 * P ^ 2 + 2 * P + 1) - (P ^ 2 + 1) * (Q ^ 2 + 1) := by
  rcases h with ⟨hP, hQ⟩ | ⟨rfl, hQ⟩
  · obtain ⟨u, rfl⟩ := exists_add_sq hP
    obtain ⟨v, rfl⟩ := exists_add_sq hQ
    ring_nf; positivity
  · obtain ⟨v, rfl⟩ := exists_add_sq hQ
    ring_nf; positivity

lemma poly_I2 (h : PQok P Q) :
    0 < (P - 1) ^ 2 * Q * (Q + 1) + (Q - 1) ^ 2 * (3 * P ^ 2 + 1) - (P ^ 2 + 1) * (Q ^ 2 + 1) := by
  rcases h with ⟨hP, hQ⟩ | ⟨rfl, hQ⟩
  · obtain ⟨u, rfl⟩ := exists_add_sq hP
    obtain ⟨v, rfl⟩ := exists_add_sq hQ
    ring_nf; positivity
  · obtain ⟨v, rfl⟩ := exists_add_sq hQ
    ring_nf; positivity

lemma poly_I3 (h : PQok P Q) :
    0 < 2 * (P ^ 2 + 1) * (Q - 1) +
      (Q + 1) * (2 * Q * (P - 1) ^ 2 + 2 * Q * (P ^ 2 + 1) - 6 * P ^ 2 - 2) := by
  rcases h with ⟨hP, hQ⟩ | ⟨rfl, hQ⟩
  · obtain ⟨u, rfl⟩ := exists_add_sq hP
    obtain ⟨v, rfl⟩ := exists_add_sq hQ
    ring_nf; positivity
  · obtain ⟨v, rfl⟩ := exists_add_sq hQ
    ring_nf; positivity

lemma poly_I4 (h : PQok P Q) :
    0 < 2 * (P - 1) ^ 2 * Q * (Q + 1) + 4 * (Q - 1) ^ 2 * P * (P + 1) -
      2 * (P ^ 2 + 1) * (Q ^ 2 + 1) := by
  rcases h with ⟨hP, hQ⟩ | ⟨rfl, hQ⟩
  · obtain ⟨u, rfl⟩ := exists_add_sq hP
    obtain ⟨v, rfl⟩ := exists_add_sq hQ
    ring_nf; positivity
  · obtain ⟨v, rfl⟩ := exists_add_sq hQ
    ring_nf; positivity

lemma poly_I5 (h : PQok P Q) :
    0 < (Q + 1) * (2 * Q * (2 * P ^ 2 - 6 * P)) + 4 * Q ^ 2 * (Q + 1) * (P + 1) -
      2 * (P ^ 2 + 1) * (Q ^ 2 + 1) := by
  rcases h with ⟨hP, hQ⟩ | ⟨rfl, hQ⟩
  · obtain ⟨u, rfl⟩ := exists_add_sq hP
    obtain ⟨v, rfl⟩ := exists_add_sq hQ
    ring_nf; positivity
  · obtain ⟨v, rfl⟩ := exists_add_sq hQ
    ring_nf; positivity

lemma poly_I5b (h : PQok P Q) :
    0 < (Q + 1) * (2 * (P - 1) ^ 2 * Q + 4 * Q ^ 2 * (P + 1)) - 2 * (P ^ 2 + 1) * (Q ^ 2 + 1) := by
  rcases h with ⟨hP, hQ⟩ | ⟨rfl, hQ⟩
  · obtain ⟨u, rfl⟩ := exists_add_sq hP
    obtain ⟨v, rfl⟩ := exists_add_sq hQ
    ring_nf; positivity
  · obtain ⟨v, rfl⟩ := exists_add_sq hQ
    ring_nf; positivity

lemma poly_I6 (h : PQok P Q) :
    0 < (P ^ 2 + 1) * Q * (Q + 1) ^ 2 - 2 * P * (P + 1) * (Q ^ 2 + 1) := by
  rcases h with ⟨hP, hQ⟩ | ⟨rfl, hQ⟩
  · obtain ⟨u, rfl⟩ := exists_add_sq hP
    obtain ⟨v, rfl⟩ := exists_add_sq hQ
    ring_nf; positivity
  · obtain ⟨v, rfl⟩ := exists_add_sq hQ
    ring_nf; positivity

lemma poly_I7 (h : PQok P Q) :
    0 < 4 * P * (P * Q - 1) * (Q + 1) - 2 * (P ^ 2 + 1) * (Q ^ 2 + 1) := by
  rcases h with ⟨hP, hQ⟩ | ⟨rfl, hQ⟩
  · obtain ⟨u, rfl⟩ := exists_add_sq hP
    obtain ⟨v, rfl⟩ := exists_add_sq hQ
    ring_nf; positivity
  · obtain ⟨v, rfl⟩ := exists_add_sq hQ
    ring_nf; positivity

end Poly

/-! ### Lemma S (one-step bound), by column type; only `|A_i|` matters -/

section LemmaS

variable {P Q μ A0 A1 A2 B0 B1 B2 : ℝ}

/-- Type `A = ±s₂`: all three cells are `≤ 0` and `Sc = -Σ h`. -/
lemma lemS_A (hPQ : PQok P Q) (hμ0 : 0 ≤ μ) (hμ1 : μ ≤ 1)
    (hA0 : |A0| = 2 * P * (P + 1)) (hA1 : |A1| = 2 * P ^ 2) (hA2 : |A2| = P ^ 2 + 1)
    (hB0 : |B0| ≤ 2 * P * (P + 1)) (hB1 : |B1| ≤ 2 * P * (P + 1)) (hB2 : |B2| ≤ (P + 1) ^ 2) :
    hcell Q μ A0 B0 ≤ 0 ∧ hcell Q μ A1 B1 ≤ 0 ∧ hcell Q μ A2 B2 ≤ 0 ∧
      Sc P Q μ A0 A1 A2 B0 B1 B2 = -(hcell Q μ A0 B0 + hcell Q μ A1 B1 + hcell Q μ A2 B2) := by
  obtain ⟨hP, hQ⟩ := hPQ.two
  have hμQ : μ ≤ Q := by linarith
  have hPP : 0 ≤ P * (P + 1) := by nlinarith
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply hcell_nonpos hμ0 hμ1 hμQ
    rw [hA0]
    nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ Q - 1) hPP]
  · apply hcell_nonpos hμ0 hμ1 hμQ
    rw [hA1]
    nlinarith [mul_nonneg (mul_nonneg (by linarith : (0:ℝ) ≤ P) (by linarith : (0:ℝ) ≤ Q - 2))
      (by linarith : (0:ℝ) ≤ P), mul_nonneg (by linarith : (0:ℝ) ≤ P) (by linarith : (0:ℝ) ≤ P - 1)]
  · apply hcell_nonpos hμ0 hμ1 hμQ
    rw [hA2]
    nlinarith [sq_nonneg (P - 1), mul_nonneg (by linarith : (0:ℝ) ≤ Q - 2)
      (by positivity : (0:ℝ) ≤ P ^ 2 + 1)]
  · unfold Sc Dp
    rw [hA0, hA1, hA2]
    ring

/-- Type `B = ±(1,1,-1)`. -/
lemma lemS_B (hPQ : PQok P Q) (hμ0 : 0 ≤ μ) (hμ1 : μ ≤ 1)
    (hA0 : |A0| = 2 * P * (P + 1)) (hA1 : |A1| = 2 * P) (hA2 : |A2| = P ^ 2 + 2 * P - 1)
    (hB0 : |B0| ≤ 2 * P * (P + 1)) (hB1 : |B1| ≤ 2 * P * (P + 1)) (hB2 : |B2| ≤ (P + 1) ^ 2) :
    0 < Sc P Q μ A0 A1 A2 B0 B1 B2 := by
  obtain ⟨hP, hQ⟩ := hPQ.two
  have hL := Sc_lower (P := P) (A0 := A0) (A1 := A1) (A2 := A2) (B0 := B0) (B1 := B1)
    (B2 := B2) hμ0 hμ1 (by linarith : (1:ℝ) ≤ Q)
  have hPP : 0 ≤ P * (P + 1) := by nlinarith
  rw [hA0, hA1, hA2] at hL
  have m0 : max 0 (|B0| - Q * (2 * P * (P + 1))) = 0 :=
    max_eq_left (by nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ Q - 1) hPP])
  have hf0 : (0:ℝ) ≤ P ^ 2 + 2 * P - 1 := by nlinarith
  have hf1 := mul_nonneg (by linarith : (0:ℝ) ≤ Q - 2) hf0
  have m2 : max 0 (|B2| - Q * (P ^ 2 + 2 * P - 1)) = 0 := max_eq_left (by nlinarith)
  have m1 : max 0 (|B1| - Q * (2 * P)) ≤ max 0 (2 * P * (P + 1) - Q * (2 * P)) :=
    max_le_max le_rfl (by linarith)
  rw [m0, m2] at hL
  unfold Dp at hL
  have key : 0 < Q * (1 + μ) * (2 * (P - 1) ^ 2) -
      2 * μ * max 0 (2 * P * (P + 1) - Q * (2 * P)) := by
    rcases le_total (2 * P * (P + 1) - Q * (2 * P)) 0 with hn | hn
    · rw [max_eq_left hn]
      have : 0 < (P - 1) ^ 2 := by nlinarith
      nlinarith [mul_pos (by linarith : (0:ℝ) < Q) this]
    · rw [max_eq_right hn]
      have hP4 : 4 ≤ P := by
        rcases hPQ with ⟨h1, _⟩ | ⟨h1, h2⟩
        · exact h1
        · subst h1; linarith
      have e : Q * (1 + μ) * (2 * (P - 1) ^ 2) - 2 * μ * (2 * P * (P + 1) - Q * (2 * P)) =
          2 * Q * (P - 1) ^ 2 + (2 * Q * (P - 1) ^ 2 - 4 * P * (P + 1) + 4 * P * Q) * μ := by ring
      rw [e]
      apply aff_pos hμ0 hμ1
      · nlinarith [mul_pos (by linarith : (0:ℝ) < Q) (by nlinarith : (0:ℝ) < (P - 1) ^ 2)]
      · nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ Q - 2) (by nlinarith : (0:ℝ) ≤ P ^ 2 - P + 1),
          mul_pos (by linarith : (0:ℝ) < P - 1) (by linarith : (0:ℝ) < P - 2)]
  have hm1' := mul_le_mul_of_nonneg_left m1 (by linarith : (0:ℝ) ≤ 2 * μ)
  nlinarith

/-- Type `C = ±(1,-1,-1)` (with the exact `|B₀|`). -/
lemma boundC (hPQ : PQok P Q) (hμ0 : 0 ≤ μ) (hμ1 : μ ≤ 1)
    (hA1 : |A1| = 2 * P * (P + 1)) (hA2 : |A2| = P ^ 2 - 1)
    (hB1 : |B1| ≤ 2 * P * (P + 1)) (hB2 : |B2| ≤ (P + 1) ^ 2) :
    2 * (P ^ 2 + 1) * Q * (1 + μ) - 2 * μ * |B0| ≤ Sc P Q μ 0 A1 A2 B0 B1 B2 := by
  obtain ⟨hP, hQ⟩ := hPQ.two
  have hL := Sc_lower (P := P) (A0 := 0) (A1 := A1) (A2 := A2) (B0 := B0) (B1 := B1)
    (B2 := B2) hμ0 hμ1 (by linarith : (1:ℝ) ≤ Q)
  have hPP : 0 ≤ P * (P + 1) := by nlinarith
  have hk := k_le_Qg hPQ
  rw [abs_zero, hA1, hA2, mul_zero, sub_zero, max_eq_right (abs_nonneg B0)] at hL
  have m1 : max 0 (|B1| - Q * (2 * P * (P + 1))) = 0 :=
    max_eq_left (by nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ Q - 1) hPP])
  have m2 : max 0 (|B2| - Q * (P ^ 2 - 1)) = 0 := max_eq_left (by linarith)
  rw [m1, m2] at hL
  unfold Dp at hL
  nlinarith

/-- Type `E = ±(1,1,1)` (with the exact `|B₀|, |B₁|`). -/
lemma boundE (hPQ : PQok P Q) (hμ0 : 0 ≤ μ) (hμ1 : μ ≤ 1)
    (hA2 : |A2| = (P + 1) ^ 2) (hB2 : |B2| ≤ (P + 1) ^ 2) :
    4 * P ^ 2 * Q * (1 + μ) - 2 * μ * (|B0| + |B1|) ≤ Sc P Q μ 0 0 A2 B0 B1 B2 := by
  obtain ⟨hP, hQ⟩ := hPQ.two
  have hL := Sc_lower (P := P) (A0 := 0) (A1 := 0) (A2 := A2) (B0 := B0) (B1 := B1)
    (B2 := B2) hμ0 hμ1 (by linarith : (1:ℝ) ≤ Q)
  rw [abs_zero, hA2, mul_zero, sub_zero, sub_zero, max_eq_right (abs_nonneg B0),
    max_eq_right (abs_nonneg B1)] at hL
  have m2 : max 0 (|B2| - Q * (P + 1) ^ 2) = 0 :=
    max_eq_left (by nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ Q - 1) (sq_nonneg (P + 1))])
  rw [m2] at hL
  unfold Dp at hL
  nlinarith

lemma lemS_C (hPQ : PQok P Q) (hμ0 : 0 ≤ μ) (hμ1 : μ ≤ 1)
    (hA1 : |A1| = 2 * P * (P + 1)) (hA2 : |A2| = P ^ 2 - 1)
    (hB0 : |B0| ≤ 2 * P * (P + 1)) (hB1 : |B1| ≤ 2 * P * (P + 1)) (hB2 : |B2| ≤ (P + 1) ^ 2) :
    0 < Sc P Q μ 0 A1 A2 B0 B1 B2 := by
  obtain ⟨hP, hQ⟩ := hPQ.two
  have h := boundC hPQ hμ0 hμ1 hA1 hA2 hB1 hB2 (B0 := B0)
  have hb := mul_le_mul_of_nonneg_left hB0 (by linarith : (0:ℝ) ≤ 2 * μ)
  nlinarith [mul_nonneg hμ0 (by nlinarith : (0:ℝ) ≤ (P ^ 2 + 1) * Q - 2 * P * (P + 1) + 2 * P ^ 2 + 2),
    mul_nonneg hμ0 (mul_nonneg (by linarith : (0:ℝ) ≤ Q - 2) (by positivity : (0:ℝ) ≤ P ^ 2 + 1))]

lemma lemS_E (hPQ : PQok P Q) (hμ0 : 0 ≤ μ) (hμ1 : μ ≤ 1) (hA2 : |A2| = (P + 1) ^ 2)
    (hB0 : |B0| ≤ 2 * P * (P + 1)) (hB1 : |B1| ≤ 2 * P * (P + 1)) (hB2 : |B2| ≤ (P + 1) ^ 2) :
    0 < Sc P Q μ 0 0 A2 B0 B1 B2 := by
  obtain ⟨hP, hQ⟩ := hPQ.two
  have h := boundE hPQ hμ0 hμ1 hA2 hB2 (B0 := B0) (B1 := B1)
  have hb := mul_le_mul_of_nonneg_left (add_le_add hB0 hB1) (by linarith : (0:ℝ) ≤ 2 * μ)
  nlinarith [mul_nonneg hμ0 (mul_nonneg (by linarith : (0:ℝ) ≤ Q - 2) (sq_nonneg P)),
    mul_nonneg (by linarith : (0:ℝ) ≤ 1 - μ) (by nlinarith : (0:ℝ) ≤ P * (P - 1)),
    mul_nonneg hμ0 (by nlinarith : (0:ℝ) ≤ P * (P - 1))]

end LemmaS

/-- **Lemma S.** For every column `c ∈ {±1}³` and every state in the box, `Sc ≥ 0`, and
`Sc > 0` unless `c = ±s₂`. -/
theorem lemS {P Q μ c0 c1 c2 B0 B1 B2 : ℝ} (hPQ : PQok P Q) (hμ0 : 0 ≤ μ) (hμ1 : μ ≤ 1)
    (hc0 : c0 = 1 ∨ c0 = -1) (hc1 : c1 = 1 ∨ c1 = -1) (hc2 : c2 = 1 ∨ c2 = -1)
    (hB0 : |B0| ≤ 2 * P * (P + 1)) (hB1 : |B1| ≤ 2 * P * (P + 1)) (hB2 : |B2| ≤ (P + 1) ^ 2) :
    0 ≤ Sc P Q μ (Mc0 P c0 c1 c2) (Mc1 P c0 c1 c2) (Mc2 P c0 c1 c2) B0 B1 B2 ∧
      (¬ ((c0 = 1 ∧ c1 = -1 ∧ c2 = 1) ∨ (c0 = -1 ∧ c1 = 1 ∧ c2 = -1)) →
        0 < Sc P Q μ (Mc0 P c0 c1 c2) (Mc1 P c0 c1 c2) (Mc2 P c0 c1 c2) B0 B1 B2) := by
  obtain ⟨hP, hQ⟩ := hPQ.two
  have hPP : 0 ≤ 2 * P * (P + 1) := by nlinarith
  have hf : 0 ≤ P ^ 2 + 2 * P - 1 := by nlinarith
  have hg : 0 ≤ P ^ 2 - 1 := by nlinarith
  have posC : ∀ A1 A2 : ℝ, |A1| = 2 * P * (P + 1) → |A2| = P ^ 2 - 1 →
      0 < Sc P Q μ 0 A1 A2 B0 B1 B2 := fun A1 A2 h1 h2 => lemS_C hPQ hμ0 hμ1 h1 h2 hB0 hB1 hB2
  have posE : ∀ A2 : ℝ, |A2| = (P + 1) ^ 2 → 0 < Sc P Q μ 0 0 A2 B0 B1 B2 :=
    fun A2 h2 => lemS_E hPQ hμ0 hμ1 h2 hB0 hB1 hB2
  have posB : ∀ A0 A1 A2 : ℝ, |A0| = 2 * P * (P + 1) → |A1| = 2 * P →
      |A2| = P ^ 2 + 2 * P - 1 → 0 < Sc P Q μ A0 A1 A2 B0 B1 B2 :=
    fun A0 A1 A2 h0 h1 h2 => lemS_B hPQ hμ0 hμ1 h0 h1 h2 hB0 hB1 hB2
  have nnA : ∀ A0 A1 A2 : ℝ, |A0| = 2 * P * (P + 1) → |A1| = 2 * P ^ 2 → |A2| = P ^ 2 + 1 →
      0 ≤ Sc P Q μ A0 A1 A2 B0 B1 B2 := by
    intro A0 A1 A2 h0 h1 h2
    obtain ⟨c0', c1', c2', e⟩ := lemS_A hPQ hμ0 hμ1 h0 h1 h2 hB0 hB1 hB2
    rw [e]
    linarith
  have aP : |2 * P * (P + 1)| = 2 * P * (P + 1) := abs_of_nonneg hPP
  have aN : |-(2 * P * (P + 1))| = 2 * P * (P + 1) := by rw [abs_neg, aP]
  rcases hc0 with rfl | rfl <;> rcases hc1 with rfl | rfl <;> rcases hc2 with rfl | rfl
  · obtain ⟨e0, e1, e2⟩ := col_E P
    rw [e0, e1, e2]
    have := posE ((P + 1) ^ 2) (abs_of_nonneg (sq_nonneg _))
    exact ⟨this.le, fun _ => this⟩
  · obtain ⟨e0, e1, e2⟩ := col_B P
    rw [e0, e1, e2]
    have := posB (-(2 * P * (P + 1))) (-(2 * P)) (P ^ 2 + 2 * P - 1) aN
      (by rw [abs_neg, abs_of_nonneg (by linarith)]) (abs_of_nonneg hf)
    exact ⟨this.le, fun _ => this⟩
  · obtain ⟨e0, e1, e2⟩ := col_A P
    rw [e0, e1, e2]
    refine ⟨nnA (2 * P * (P + 1)) (-(2 * P ^ 2)) (P ^ 2 + 1) aP (by rw [abs_neg, abs_of_nonneg (by positivity)])
      (abs_of_nonneg (by positivity)), fun h => absurd (Or.inl ⟨rfl, rfl, rfl⟩) h⟩
  · obtain ⟨e0, e1, e2⟩ := col_C P
    rw [e0, e1, e2]
    have := posC (-(2 * P * (P + 1))) (P ^ 2 - 1) aN (abs_of_nonneg hg)
    exact ⟨this.le, fun _ => this⟩
  · obtain ⟨e0, e1, e2⟩ := col_nC P
    rw [e0, e1, e2]
    have := posC (2 * P * (P + 1)) (-(P ^ 2 - 1)) aP (by rw [abs_neg, abs_of_nonneg hg])
    exact ⟨this.le, fun _ => this⟩
  · obtain ⟨e0, e1, e2⟩ := col_nA P
    rw [e0, e1, e2]
    refine ⟨nnA (-(2 * P * (P + 1))) (2 * P ^ 2) (-(P ^ 2 + 1)) aN (abs_of_nonneg (by positivity))
      (by rw [abs_neg, abs_of_nonneg (by positivity)]), fun h => absurd (Or.inr ⟨rfl, rfl, rfl⟩) h⟩
  · obtain ⟨e0, e1, e2⟩ := col_nB P
    rw [e0, e1, e2]
    have := posB (2 * P * (P + 1)) (2 * P) (-(P ^ 2 + 2 * P - 1)) aP (abs_of_nonneg (by linarith))
      (by rw [abs_neg, abs_of_nonneg hf])
    exact ⟨this.le, fun _ => this⟩
  · obtain ⟨e0, e1, e2⟩ := col_nE P
    rw [e0, e1, e2]
    have := posE (-((P + 1) ^ 2)) (by rw [abs_neg, abs_of_nonneg (sq_nonneg _)])
    exact ⟨this.le, fun _ => this⟩

end ICGEqualParityB
