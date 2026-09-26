import Mathlib
import Research.ICGEqualParityBCol

set_option autoImplicit false

/-!
# Theorem B (round 6): Lemmas FD1 and FD2 at the level of one column

* `fd1`: **Lemma FD1.**  At the first deviation `J` from the anti-checkerboard the state is
  `ζ_J = ε m s₂`, i.e. `B = ε m α(A)` with `α(A) = T₂(p) s₂ = (2pP, -2P², P²+1)`.  Every column
  `c ≠ -ε s₂` has `Sc > 2 q δ₂(p) ρ` (`δ₂(p) = P² + 1`).  By the symmetry `Sc_neg` we state it
  for `ε = 1`.  Parameters (`Q = q - 1`): `μ, m ∈ [μ₀, 1]`, `ρ ≤ μ₁`, and one of the three
  regimes `J = 0`, `J = b - 1`, `1 ≤ J ≤ b - 2` (only the `Copp` deviation needs them).
* `fd2a`: at the last-but-one column when `c_b = B`: the state is exactly `α(B)` and every
  column `c ≠ -B` (and also `c = -B` when `P ≥ 4`) has `Sc > 4P(Q - μ) = 4P q ρ`.
* `fd2dom`: for `P = 2` at the state `-μ₀ α(B)` every column has `Sc ≥ 2Q(1+μ) = q ĉ Δ(B)`.
* `two_col`: `2ĉ_{b-1} + 2ĉ_{b-2} > 8ρ` for `P = 2`.
-/

noncomputable section

namespace ICGEqualParityB

open Finset ICGGeneral ICGEqualParity

/-! ### FD1: the seven deviations at the state `m α(A)` -/

section FD1

variable {P Q μ m ρ : ℝ}

/-- `A same` (`c = s₂`, the tight case). -/
lemma fd1_A (hPQ : PQok P Q) (hμ0 : Q - 1 ≤ (Q + 1) * μ) (hμ1 : μ ≤ 1)
    (hm0 : Q - 1 ≤ (Q + 1) * m) (hm1 : m ≤ 1) (hρ : (Q + 1) ^ 2 * ρ ≤ Q ^ 2 + 1) :
    2 * (Q + 1) * (P ^ 2 + 1) * ρ <
      Sc P Q μ (2 * P * (P + 1)) (-(2 * P ^ 2)) (P ^ 2 + 1)
        (m * (2 * P * (P + 1))) (m * (-(2 * P ^ 2))) (m * (P ^ 2 + 1)) := by
  obtain ⟨hP, hQ⟩ := hPQ.two
  have hmpos : 0 ≤ m := by nlinarith
  have hμpos : 0 ≤ μ := by nlinarith
  have ha : 0 ≤ 2 * P * (P + 1) := by nlinarith
  have hb : 0 ≤ 2 * P ^ 2 := by positivity
  have he : 0 ≤ P ^ 2 + 1 := by positivity
  have h0 : hcell Q μ (2 * P * (P + 1)) (m * (2 * P * (P + 1))) =
      -2 * (Q - μ) * (m * (2 * P * (P + 1))) :=
    hcell_same_pos hμpos (by linarith) (mul_nonneg hmpos ha) (by nlinarith)
  have h1 : hcell Q μ (-(2 * P ^ 2)) (m * (-(2 * P ^ 2))) = 2 * (Q - μ) * (m * (-(2 * P ^ 2))) :=
    hc_same_neg hμpos (by linarith) (by nlinarith) (by nlinarith)
  have h2 : hcell Q μ (P ^ 2 + 1) (m * (P ^ 2 + 1)) = -2 * (Q - μ) * (m * (P ^ 2 + 1)) :=
    hcell_same_pos hμpos (by linarith) (mul_nonneg hmpos he) (by nlinarith)
  apply need_of (by linarith) hρ
  unfold Sc Dp
  rw [h0, h1, h2, abs_of_nonneg ha, abs_neg, abs_of_nonneg hb, abs_of_nonneg he]
  have hI := poly_I1 hPQ
  have hk : (Q - 1) * (Q - 1) ≤ (Q - μ) * ((Q + 1) * m) :=
    mul_le_mul (by linarith) hm0 (by linarith) (by linarith)
  have hk2 := mul_le_mul_of_nonneg_left hk (by nlinarith : (0:ℝ) ≤ 2 * (5 * P ^ 2 + 2 * P + 1))
  nlinarith

/-- `B same` (`c = (1,1,-1)`). -/
lemma fd1_Bs (hPQ : PQok P Q) (hμ0 : Q - 1 ≤ (Q + 1) * μ) (hμ1 : μ ≤ 1)
    (hm0 : Q - 1 ≤ (Q + 1) * m) (hm1 : m ≤ 1) (hρ : (Q + 1) ^ 2 * ρ ≤ Q ^ 2 + 1) :
    2 * (Q + 1) * (P ^ 2 + 1) * ρ <
      Sc P Q μ (-(2 * P * (P + 1))) (-(2 * P)) (P ^ 2 + 2 * P - 1)
        (m * (2 * P * (P + 1))) (m * (-(2 * P ^ 2))) (m * (P ^ 2 + 1)) := by
  obtain ⟨hP, hQ⟩ := hPQ.two
  have hmpos : 0 ≤ m := by nlinarith
  have hμpos : 0 ≤ μ := by nlinarith
  have ha : 0 ≤ 2 * P * (P + 1) := by nlinarith
  have hf : 0 ≤ P ^ 2 + 2 * P - 1 := by nlinarith
  have he : 0 ≤ P ^ 2 + 1 := by positivity
  have h0 : hcell Q μ (-(2 * P * (P + 1))) (m * (2 * P * (P + 1))) = 0 :=
    hcell_opp' (by linarith) (mul_nonneg hmpos ha) (by nlinarith)
  have h2 : hcell Q μ (P ^ 2 + 2 * P - 1) (m * (P ^ 2 + 1)) = -2 * (Q - μ) * (m * (P ^ 2 + 1)) :=
    hcell_same_pos hμpos (by linarith) (mul_nonneg hmpos he) (by nlinarith)
  apply need_of (by linarith) hρ
  unfold Sc Dp
  rw [h0, h2, abs_neg, abs_of_nonneg ha, abs_neg, abs_of_nonneg (by linarith : (0:ℝ) ≤ 2 * P),
    abs_of_nonneg hf]
  have hPm := mul_le_mul_of_nonneg_left hm1 (by linarith : (0:ℝ) ≤ P)
  rcases le_total (m * P) 1 with hmP | hmP
  · have hPmP := mul_le_mul_of_nonneg_left hmP (by linarith : (0:ℝ) ≤ P)
    rw [hc_same_neg hμpos (by linarith) (by nlinarith) (by nlinarith)]
    have hI := poly_I2 hPQ
    have hk : (Q - 1) * (Q - 1) ≤ (Q - μ) * ((Q + 1) * m) :=
      mul_le_mul (by linarith) hm0 (by linarith) (by linarith)
    have hk2 := mul_le_mul_of_nonneg_left hk (by positivity : (0:ℝ) ≤ 2 * (3 * P ^ 2 + 1))
    have hμ2 : 0 ≤ μ * ((P - 1) ^ 2 * (Q * (Q + 1))) :=
      mul_nonneg hμpos (mul_nonneg (sq_nonneg _) (by nlinarith))
    nlinarith
  · have hPmP := mul_le_mul_of_nonneg_left hmP (by linarith : (0:ℝ) ≤ P)
    rw [hc_big_neg (by linarith) (by linarith) (by nlinarith)]
    have hI := poly_I3 hPQ
    have hQQ : 0 ≤ (Q + 1) * Q := by nlinarith
    have ha0 : 0 < 2 * (P ^ 2 + 1) * (Q - 1) := by nlinarith
    have hb1 := mul_nonneg hQQ (sq_nonneg (P - 1))
    have hc1 := mul_nonneg hQQ he
    have hb := bilin_pos hμpos hμ1 hmpos hm1 (a := 2 * (P ^ 2 + 1) * (Q - 1))
      (b := 2 * (Q + 1) * Q * (P - 1) ^ 2) (c := 2 * (Q + 1) * Q * (P ^ 2 + 1))
      (d := -((Q + 1) * (6 * P ^ 2 + 2))) ha0 (by nlinarith) (by nlinarith) (by nlinarith)
    nlinarith

/-- `B opp` (`c = (-1,-1,1)`). -/
lemma fd1_Bo (hPQ : PQok P Q) (hμ0 : Q - 1 ≤ (Q + 1) * μ) (hμ1 : μ ≤ 1)
    (hm0 : Q - 1 ≤ (Q + 1) * m) (hm1 : m ≤ 1) (hρ : (Q + 1) ^ 2 * ρ ≤ Q ^ 2 + 1) :
    2 * (Q + 1) * (P ^ 2 + 1) * ρ <
      Sc P Q μ (2 * P * (P + 1)) (2 * P) (-(P ^ 2 + 2 * P - 1))
        (m * (2 * P * (P + 1))) (m * (-(2 * P ^ 2))) (m * (P ^ 2 + 1)) := by
  obtain ⟨hP, hQ⟩ := hPQ.two
  have hmpos : 0 ≤ m := by nlinarith
  have hμpos : 0 ≤ μ := by nlinarith
  have ha : 0 ≤ 2 * P * (P + 1) := by nlinarith
  have hf : 0 ≤ P ^ 2 + 2 * P - 1 := by nlinarith
  have he : 0 ≤ P ^ 2 + 1 := by positivity
  have h0 : hcell Q μ (2 * P * (P + 1)) (m * (2 * P * (P + 1))) =
      -2 * (Q - μ) * (m * (2 * P * (P + 1))) :=
    hcell_same_pos hμpos (by linarith) (mul_nonneg hmpos ha) (by nlinarith)
  have h2 : hcell Q μ (-(P ^ 2 + 2 * P - 1)) (m * (P ^ 2 + 1)) = 0 :=
    hcell_opp' (by linarith) (mul_nonneg hmpos he) (by nlinarith)
  apply need_of (by linarith) hρ
  unfold Sc Dp
  rw [h0, h2, abs_of_nonneg ha, abs_of_nonneg (by linarith : (0:ℝ) ≤ 2 * P), abs_neg,
    abs_of_nonneg hf]
  rcases le_total (m * P) Q with hmP | hmP
  · have hPmP := mul_le_mul_of_nonneg_left hmP (by linarith : (0:ℝ) ≤ 2 * P)
    rw [hcell_opp (by linarith) (by nlinarith) (by nlinarith)]
    have hI := poly_I4 hPQ
    have hk : (Q - 1) * (Q - 1) ≤ (Q - μ) * ((Q + 1) * m) :=
      mul_le_mul (by linarith) hm0 (by linarith) (by linarith)
    have hk2 := mul_le_mul_of_nonneg_left hk ha
    have hμ2 : 0 ≤ μ * ((P - 1) ^ 2 * (Q * (Q + 1))) :=
      mul_nonneg hμpos (mul_nonneg (sq_nonneg _) (by nlinarith))
    nlinarith
  · have hPmP := mul_le_mul_of_nonneg_left hmP (by linarith : (0:ℝ) ≤ 2 * P)
    rw [hc_opp_big (by linarith) (by linarith) (by nlinarith)]
    have hX : 0 ≤ Q * (P + 1) - μ * (2 * P + 1) := by nlinarith
    have hXX := mul_nonneg (by linarith : (0:ℝ) ≤ m * P - Q) hX
    -- Sc ≥ 2(P-1)²Q + 4Q²(P+1) + 2μQ(P² - 4P - 1)
    have hlow : 2 * (P - 1) ^ 2 * Q + 4 * Q ^ 2 * (P + 1) + 2 * μ * Q * (P ^ 2 - 4 * P - 1) ≤
        Q * (1 + μ) * (5 * P ^ 2 + 2 * P + 1 -
          (2 * P * (P + 1) + 2 * P + (P ^ 2 + 2 * P - 1))) -
          (-2 * (Q - μ) * (m * (2 * P * (P + 1))) + 2 * μ * (-(m * -(2 * P ^ 2)) - Q * (2 * P)) +
            0) := by
      nlinarith
    have hI5 := poly_I5 hPQ
    have hI5b := poly_I5b hPQ
    have hA := aff_pos hμpos hμ1 (α := (Q + 1) * (2 * (P - 1) ^ 2 * Q + 4 * Q ^ 2 * (P + 1)) -
        2 * (P ^ 2 + 1) * (Q ^ 2 + 1)) (β := (Q + 1) * (2 * Q * (P ^ 2 - 4 * P - 1))) hI5b
      (by nlinarith)
    have hQ1 : (0:ℝ) ≤ Q + 1 := by linarith
    have := mul_le_mul_of_nonneg_left hlow hQ1
    nlinarith

/-- `C same` / `C opp` (`A = (0, ±2pP, ±(P²-1))`), in the three regimes. -/
lemma fd1_C {A1 A2 : ℝ} (hPQ : PQok P Q) (hμ0 : Q - 1 ≤ (Q + 1) * μ) (hμ1 : μ ≤ 1)
    (hm0 : Q - 1 ≤ (Q + 1) * m) (hm1 : m ≤ 1) (hρ : (Q + 1) ^ 2 * ρ ≤ Q ^ 2 + 1)
    (hreg : (μ = 1 ∧ (Q + 1) * ρ = Q - m) ∨ (m = 1 ∧ (Q + 1) * ρ = Q - μ) ∨
      (Q + 1) ^ 2 * m ≤ Q ^ 2 + 1)
    (hA1 : |A1| = 2 * P * (P + 1)) (hA2 : |A2| = P ^ 2 - 1) :
    2 * (Q + 1) * (P ^ 2 + 1) * ρ <
      Sc P Q μ 0 A1 A2 (m * (2 * P * (P + 1))) (m * (-(2 * P ^ 2))) (m * (P ^ 2 + 1)) := by
  obtain ⟨hP, hQ⟩ := hPQ.two
  have hmpos : 0 ≤ m := by nlinarith
  have hμpos : 0 ≤ μ := by nlinarith
  have ha : 0 ≤ 2 * P * (P + 1) := by nlinarith
  have he : 0 ≤ P ^ 2 + 1 := by positivity
  have hB1 : |m * (-(2 * P ^ 2))| ≤ 2 * P * (P + 1) := by
    rw [abs_mul, abs_neg, abs_of_nonneg hmpos, abs_of_nonneg (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left hm1 (by positivity : (0:ℝ) ≤ 2 * P ^ 2)]
  have hB2 : |m * (P ^ 2 + 1)| ≤ (P + 1) ^ 2 := by
    rw [abs_of_nonneg (mul_nonneg hmpos he)]
    nlinarith [mul_le_mul_of_nonneg_left hm1 he]
  have hL := boundC hPQ hμpos hμ1 hA1 hA2 hB1 hB2 (B0 := m * (2 * P * (P + 1)))
  rw [abs_of_nonneg (mul_nonneg hmpos ha)] at hL
  rcases hreg with ⟨rfl, hr⟩ | ⟨rfl, hr⟩ | hr
  · have hr2 : 2 * (Q + 1) * (P ^ 2 + 1) * ρ = 2 * (P ^ 2 + 1) * (Q - m) := by
      rw [← hr]; ring
    rw [hr2]
    nlinarith [mul_le_mul_of_nonneg_left hm1 (by nlinarith : (0:ℝ) ≤ P ^ 2 + 2 * P - 1),
      mul_le_mul_of_nonneg_left hQ he]
  · have hr2 : 2 * (Q + 1) * (P ^ 2 + 1) * ρ = 2 * (P ^ 2 + 1) * (Q - μ) := by
      rw [← hr]; ring
    rw [hr2]
    have hμp : 0 < μ := by nlinarith
    have hbr : 0 < (P ^ 2 + 1) * (Q + 1) - 2 * P * (P + 1) := by nlinarith
    nlinarith [mul_pos hμp hbr]
  · apply need_of (by linarith) hρ
    have h6 := poly_I6 hPQ
    have hmm := mul_le_mul_of_nonneg_left hr ha
    have hX : 0 ≤ (P ^ 2 + 1) * Q - 2 * P * (P + 1) * m := by
      nlinarith [pow_pos (by linarith : (0:ℝ) < Q + 1) 2]
    nlinarith [mul_nonneg hμpos hX]

/-- `E same` / `E opp` (`A = (0, 0, ±p²)`). -/
lemma fd1_E {A2 : ℝ} (hPQ : PQok P Q) (hμ0 : Q - 1 ≤ (Q + 1) * μ) (hμ1 : μ ≤ 1)
    (hm0 : Q - 1 ≤ (Q + 1) * m) (hm1 : m ≤ 1) (hρ : (Q + 1) ^ 2 * ρ ≤ Q ^ 2 + 1)
    (hA2 : |A2| = (P + 1) ^ 2) :
    2 * (Q + 1) * (P ^ 2 + 1) * ρ <
      Sc P Q μ 0 0 A2 (m * (2 * P * (P + 1))) (m * (-(2 * P ^ 2))) (m * (P ^ 2 + 1)) := by
  obtain ⟨hP, hQ⟩ := hPQ.two
  have hmpos : 0 ≤ m := by nlinarith
  have hμpos : 0 ≤ μ := by nlinarith
  have ha : 0 ≤ 2 * P * (P + 1) := by nlinarith
  have he : 0 ≤ P ^ 2 + 1 := by positivity
  have hB2 : |m * (P ^ 2 + 1)| ≤ (P + 1) ^ 2 := by
    rw [abs_of_nonneg (mul_nonneg hmpos he)]
    nlinarith [mul_le_mul_of_nonneg_left hm1 he]
  have hL := boundE hPQ hμpos hμ1 hA2 hB2 (B0 := m * (2 * P * (P + 1)))
    (B1 := m * (-(2 * P ^ 2)))
  rw [abs_of_nonneg (mul_nonneg hmpos ha), abs_mul, abs_neg, abs_of_nonneg hmpos,
    abs_of_nonneg (by positivity : (0:ℝ) ≤ 2 * P ^ 2)] at hL
  apply need_of (by linarith) hρ
  have hA : 0 ≤ μ * (1 - m) * (P * (2 * P + 1)) :=
    mul_nonneg (mul_nonneg hμpos (by linarith)) (by nlinarith)
  have hB : 0 ≤ μ * P ^ 2 * (Q - 2) := mul_nonneg (mul_nonneg hμpos (sq_nonneg P)) (by linarith)
  have hC : 0 ≤ (1 - μ) * P := mul_nonneg (by linarith) (by linarith)
  have hS : 4 * P * (P * Q - 1) ≤ Sc P Q μ 0 0 A2 (m * (2 * P * (P + 1))) (m * (-(2 * P ^ 2)))
      (m * (P ^ 2 + 1)) := by nlinarith
  have h7 := poly_I7 hPQ
  nlinarith

end FD1

/-- **Lemma FD1** (column form, `ε = 1`): every column `c ≠ -s₂` pays more than `2qδ₂(p)ρ` at the
state `m α(A)`. -/
theorem fd1 {P Q μ m ρ c0 c1 c2 : ℝ} (hPQ : PQok P Q) (hμ0 : Q - 1 ≤ (Q + 1) * μ) (hμ1 : μ ≤ 1)
    (hm0 : Q - 1 ≤ (Q + 1) * m) (hm1 : m ≤ 1) (hρ : (Q + 1) ^ 2 * ρ ≤ Q ^ 2 + 1)
    (hreg : (μ = 1 ∧ (Q + 1) * ρ = Q - m) ∨ (m = 1 ∧ (Q + 1) * ρ = Q - μ) ∨
      (Q + 1) ^ 2 * m ≤ Q ^ 2 + 1)
    (hc0 : c0 = 1 ∨ c0 = -1) (hc1 : c1 = 1 ∨ c1 = -1) (hc2 : c2 = 1 ∨ c2 = -1)
    (hne : ¬ (c0 = -1 ∧ c1 = 1 ∧ c2 = -1)) :
    2 * (Q + 1) * (P ^ 2 + 1) * ρ <
      Sc P Q μ (Mc0 P c0 c1 c2) (Mc1 P c0 c1 c2) (Mc2 P c0 c1 c2)
        (m * (2 * P * (P + 1))) (m * (-(2 * P ^ 2))) (m * (P ^ 2 + 1)) := by
  obtain ⟨hP, hQ⟩ := hPQ.two
  have hPP : 0 ≤ 2 * P * (P + 1) := by nlinarith
  have hg : 0 ≤ P ^ 2 - 1 := by nlinarith
  rcases hc0 with rfl | rfl <;> rcases hc1 with rfl | rfl <;> rcases hc2 with rfl | rfl
  · obtain ⟨e0, e1, e2⟩ := col_E P
    rw [e0, e1, e2]
    exact fd1_E hPQ hμ0 hμ1 hm0 hm1 hρ (abs_of_nonneg (sq_nonneg _))
  · obtain ⟨e0, e1, e2⟩ := col_B P
    rw [e0, e1, e2]
    exact fd1_Bs hPQ hμ0 hμ1 hm0 hm1 hρ
  · obtain ⟨e0, e1, e2⟩ := col_A P
    rw [e0, e1, e2]
    exact fd1_A hPQ hμ0 hμ1 hm0 hm1 hρ
  · obtain ⟨e0, e1, e2⟩ := col_C P
    rw [e0, e1, e2]
    exact fd1_C hPQ hμ0 hμ1 hm0 hm1 hρ hreg (by rw [abs_neg, abs_of_nonneg hPP])
      (abs_of_nonneg hg)
  · obtain ⟨e0, e1, e2⟩ := col_nC P
    rw [e0, e1, e2]
    exact fd1_C hPQ hμ0 hμ1 hm0 hm1 hρ hreg (abs_of_nonneg hPP) (by rw [abs_neg, abs_of_nonneg hg])
  · exact absurd ⟨rfl, rfl, rfl⟩ hne
  · obtain ⟨e0, e1, e2⟩ := col_nB P
    rw [e0, e1, e2]
    exact fd1_Bo hPQ hμ0 hμ1 hm0 hm1 hρ
  · obtain ⟨e0, e1, e2⟩ := col_nE P
    rw [e0, e1, e2]
    exact fd1_E hPQ hμ0 hμ1 hm0 hm1 hρ (by rw [abs_neg, abs_of_nonneg (sq_nonneg _)])

/-! ### FD2 (a): the column `b - 1` at the exact state `α(B)` -/

section FD2a

variable {P Q μ : ℝ}

lemma fd2a_C {A1 A2 : ℝ} (hPQ : PQok P Q) (hμ0 : 0 ≤ μ) (hμ1 : μ ≤ 1)
    (h1 : |A1| = 2 * P * (P + 1)) (h2 : |A2| = P ^ 2 - 1) :
    4 * P * (Q - μ) < Sc P Q μ 0 A1 A2 (-(2 * P * (P + 1))) (-(2 * P)) (P ^ 2 + 2 * P - 1) := by
  obtain ⟨hP, hQ⟩ := hPQ.two
  have hPP : 0 ≤ 2 * P * (P + 1) := by nlinarith
  have hf : 0 ≤ P ^ 2 + 2 * P - 1 := by nlinarith
  have hk := k_le_Qg hPQ
  have hL := boundC hPQ hμ0 hμ1 h1 h2 (B0 := -(2 * P * (P + 1))) (B1 := -(2 * P))
    (B2 := P ^ 2 + 2 * P - 1) (by rw [abs_neg, abs_of_nonneg (by linarith)]; nlinarith)
    (by rw [abs_of_nonneg hf]; nlinarith)
  rw [abs_neg, abs_of_nonneg hPP] at hL
  have F1 : 0 < 2 * Q * (P - 1) ^ 2 :=
    mul_pos (by linarith) (pow_pos (by linarith : (0:ℝ) < P - 1) 2)
  have F2 : 0 ≤ μ * ((P ^ 2 + 1) * Q - 2 * P ^ 2) :=
    mul_nonneg hμ0 (by nlinarith [mul_le_mul_of_nonneg_right hQ (by positivity : (0:ℝ) ≤ P ^ 2 + 1)])
  linarith

lemma fd2a_E {A2 : ℝ} (hPQ : PQok P Q) (hμ0 : 0 ≤ μ) (hμ1 : μ ≤ 1) (h2 : |A2| = (P + 1) ^ 2) :
    4 * P * (Q - μ) < Sc P Q μ 0 0 A2 (-(2 * P * (P + 1))) (-(2 * P)) (P ^ 2 + 2 * P - 1) := by
  obtain ⟨hP, hQ⟩ := hPQ.two
  have hPP : 0 ≤ 2 * P * (P + 1) := by nlinarith
  have hf : 0 ≤ P ^ 2 + 2 * P - 1 := by nlinarith
  have hL := boundE hPQ hμ0 hμ1 h2 (B0 := -(2 * P * (P + 1))) (B1 := -(2 * P))
    (B2 := P ^ 2 + 2 * P - 1) (by rw [abs_of_nonneg hf]; nlinarith)
  rw [abs_neg, abs_of_nonneg hPP, abs_neg, abs_of_nonneg (by linarith : (0:ℝ) ≤ 2 * P)] at hL
  have F1 : 0 < 4 * P * Q * (P - 1) :=
    mul_pos (mul_pos (by linarith) (by linarith)) (by linarith)
  have hPQ2 := mul_le_mul_of_nonneg_left hQ (by linarith : (0:ℝ) ≤ P)
  have F2 : 0 ≤ μ * (P * (P * Q - P - 1)) :=
    mul_nonneg hμ0 (mul_nonneg (by linarith) (by nlinarith))
  linarith

lemma fd2a_Bs (hPQ : PQok P Q) (hμ0 : 0 ≤ μ) (hμ1 : μ ≤ 1) :
    4 * P * (Q - μ) < Sc P Q μ (-(2 * P * (P + 1))) (-(2 * P)) (P ^ 2 + 2 * P - 1)
      (-(2 * P * (P + 1))) (-(2 * P)) (P ^ 2 + 2 * P - 1) := by
  obtain ⟨hP, hQ⟩ := hPQ.two
  have hμQ : μ ≤ Q := by linarith
  have hPP : 0 ≤ 2 * P * (P + 1) := by nlinarith
  have hf : 0 ≤ P ^ 2 + 2 * P - 1 := by nlinarith
  have c0 : hcell Q μ (-(2 * P * (P + 1))) (-(2 * P * (P + 1))) =
      2 * (Q - μ) * (-(2 * P * (P + 1))) := hc_same_neg hμ0 hμQ (by linarith) le_rfl
  have c1 := hcell_nonpos hμ0 hμ1 hμQ (A := -(2 * P)) (B := -(2 * P))
    (by have := mul_le_mul_of_nonneg_right (by linarith : (1:ℝ) ≤ Q) (abs_nonneg (-(2 * P))); linarith)
  have c2 := hcell_nonpos hμ0 hμ1 hμQ (A := P ^ 2 + 2 * P - 1) (B := P ^ 2 + 2 * P - 1)
    (by have := mul_le_mul_of_nonneg_right (by linarith : (1:ℝ) ≤ Q)
          (abs_nonneg (P ^ 2 + 2 * P - 1)); linarith)
  unfold Sc Dp
  rw [c0, abs_neg, abs_of_nonneg hPP, abs_neg, abs_of_nonneg (by linarith : (0:ℝ) ≤ 2 * P),
    abs_of_nonneg hf]
  have F1 : 0 < (Q - μ) * P ^ 2 := mul_pos (by linarith) (by positivity)
  have F2 : 0 ≤ Q * (1 + μ) * (P - 1) ^ 2 :=
    mul_nonneg (mul_nonneg (by linarith) (by linarith)) (sq_nonneg _)
  linarith

lemma fd2a_As (hPQ : PQok P Q) (hμ0 : 0 ≤ μ) (hμ1 : μ ≤ 1) :
    4 * P * (Q - μ) < Sc P Q μ (2 * P * (P + 1)) (-(2 * P ^ 2)) (P ^ 2 + 1)
      (-(2 * P * (P + 1))) (-(2 * P)) (P ^ 2 + 2 * P - 1) := by
  obtain ⟨hP, hQ⟩ := hPQ.two
  have hμQ : μ ≤ Q := by linarith
  have hPP : 0 ≤ 2 * P * (P + 1) := by nlinarith
  have hf : 0 ≤ P ^ 2 + 2 * P - 1 := by nlinarith
  have he : 0 ≤ P ^ 2 + 1 := by positivity
  have c0 : hcell Q μ (2 * P * (P + 1)) (-(2 * P * (P + 1))) = 0 :=
    hcell_opp hPP (by linarith) (by nlinarith)
  have c1 : hcell Q μ (-(2 * P ^ 2)) (-(2 * P)) = 2 * (Q - μ) * (-(2 * P)) :=
    hc_same_neg hμ0 hμQ (by linarith) (by nlinarith)
  have c2 : hcell Q μ (P ^ 2 + 1) (P ^ 2 + 2 * P - 1) =
      2 * μ * (P ^ 2 + 2 * P - 1) - 2 * Q * (P ^ 2 + 1) :=
    hc_big_pos (by linarith) he (by nlinarith)
  unfold Sc Dp
  rw [c0, c1, c2, abs_of_nonneg hPP, abs_neg, abs_of_nonneg (by positivity : (0:ℝ) ≤ 2 * P ^ 2),
    abs_of_nonneg he]
  have F1 := mul_le_mul_of_nonneg_right hμ1 hf
  have F2 := mul_le_mul_of_nonneg_right hQ he
  have F3 : P ^ 2 + 2 * P - 1 < 2 * (P ^ 2 + 1) := by nlinarith [sq_nonneg (P - 1)]
  linarith

lemma fd2a_Ao (hPQ : PQok P Q) (hμ0 : 0 ≤ μ) (hμ1 : μ ≤ 1) :
    4 * P * (Q - μ) < Sc P Q μ (-(2 * P * (P + 1))) (2 * P ^ 2) (-(P ^ 2 + 1))
      (-(2 * P * (P + 1))) (-(2 * P)) (P ^ 2 + 2 * P - 1) := by
  obtain ⟨hP, hQ⟩ := hPQ.two
  have hμQ : μ ≤ Q := by linarith
  have hPP : 0 ≤ 2 * P * (P + 1) := by nlinarith
  have hf : 0 ≤ P ^ 2 + 2 * P - 1 := by nlinarith
  have he : 0 ≤ P ^ 2 + 1 := by positivity
  have c0 : hcell Q μ (-(2 * P * (P + 1))) (-(2 * P * (P + 1))) =
      2 * (Q - μ) * (-(2 * P * (P + 1))) := hc_same_neg hμ0 hμQ (by linarith) le_rfl
  have c1 := hcell_nonpos hμ0 hμ1 hμQ (A := 2 * P ^ 2) (B := -(2 * P))
    (by rw [abs_neg, abs_of_nonneg (by linarith : (0:ℝ) ≤ 2 * P),
          abs_of_nonneg (by positivity : (0:ℝ) ≤ 2 * P ^ 2)]; nlinarith)
  have c2 := hcell_nonpos hμ0 hμ1 hμQ (A := -(P ^ 2 + 1)) (B := P ^ 2 + 2 * P - 1)
    (by rw [abs_of_nonneg hf, abs_neg, abs_of_nonneg he]; nlinarith)
  unfold Sc Dp
  rw [c0, abs_neg, abs_of_nonneg hPP, abs_of_nonneg (by positivity : (0:ℝ) ≤ 2 * P ^ 2), abs_neg,
    abs_of_nonneg he]
  have F1 : 0 < (Q - μ) * P ^ 2 := mul_pos (by linarith) (by positivity)
  linarith

lemma fd2a_chain (hPQ : PQok P Q) (hP4 : 4 ≤ P) (hμ0 : 0 ≤ μ) (hμ1 : μ ≤ 1) :
    4 * P * (Q - μ) < Sc P Q μ (2 * P * (P + 1)) (2 * P) (-(P ^ 2 + 2 * P - 1))
      (-(2 * P * (P + 1))) (-(2 * P)) (P ^ 2 + 2 * P - 1) := by
  obtain ⟨hP, hQ⟩ := hPQ.two
  have hPP : 0 ≤ 2 * P * (P + 1) := by nlinarith
  have hf : 0 ≤ P ^ 2 + 2 * P - 1 := by nlinarith
  have hL := Sc_ge_small (P := P) (A0 := 2 * P * (P + 1)) (A1 := 2 * P)
    (A2 := -(P ^ 2 + 2 * P - 1)) (B0 := -(2 * P * (P + 1))) (B1 := -(2 * P))
    (B2 := P ^ 2 + 2 * P - 1) hμ0 hμ1 (by linarith)
    (by rw [abs_neg]; have := mul_le_mul_of_nonneg_right (by linarith : (1:ℝ) ≤ Q)
          (abs_nonneg (2 * P * (P + 1))); linarith)
    (by rw [abs_neg]; have := mul_le_mul_of_nonneg_right (by linarith : (1:ℝ) ≤ Q)
          (abs_nonneg (2 * P)); linarith)
    (by rw [abs_neg]; have := mul_le_mul_of_nonneg_right (by linarith : (1:ℝ) ≤ Q)
          (abs_nonneg (P ^ 2 + 2 * P - 1)); linarith)
  rw [abs_of_nonneg hPP, abs_of_nonneg (by linarith : (0:ℝ) ≤ 2 * P), abs_neg,
    abs_of_nonneg hf] at hL
  unfold Dp at hL
  have F1 : 0 ≤ Q * (P * (P - 4)) := mul_nonneg (by linarith) (mul_nonneg (by linarith) (by linarith))
  have F2 : 0 ≤ μ * (2 * Q * (P - 1) ^ 2 + 4 * P) :=
    mul_nonneg hμ0 (by nlinarith [sq_nonneg (P - 1)])
  linarith

end FD2a

/-- **Lemma FD2 (a).**  At the state `α(B) = (-2pP, -2P, p²-2)` every column other than the
chain column `-B` has `Sc > 4P(Q - μ)`; the chain column too when `P ≥ 4`. -/
theorem fd2a {P Q μ c0 c1 c2 : ℝ} (hPQ : PQok P Q) (hμ0 : 0 ≤ μ) (hμ1 : μ ≤ 1)
    (hc0 : c0 = 1 ∨ c0 = -1) (hc1 : c1 = 1 ∨ c1 = -1) (hc2 : c2 = 1 ∨ c2 = -1)
    (hch : ¬ (c0 = -1 ∧ c1 = -1 ∧ c2 = 1) ∨ 4 ≤ P) :
    4 * P * (Q - μ) < Sc P Q μ (Mc0 P c0 c1 c2) (Mc1 P c0 c1 c2) (Mc2 P c0 c1 c2)
      (-(2 * P * (P + 1))) (-(2 * P)) (P ^ 2 + 2 * P - 1) := by
  obtain ⟨hP, hQ⟩ := hPQ.two
  have hPP : 0 ≤ 2 * P * (P + 1) := by nlinarith
  have hg : 0 ≤ P ^ 2 - 1 := by nlinarith
  rcases hc0 with rfl | rfl <;> rcases hc1 with rfl | rfl <;> rcases hc2 with rfl | rfl
  · obtain ⟨e0, e1, e2⟩ := col_E P
    rw [e0, e1, e2]
    exact fd2a_E hPQ hμ0 hμ1 (abs_of_nonneg (sq_nonneg _))
  · obtain ⟨e0, e1, e2⟩ := col_B P
    rw [e0, e1, e2]
    exact fd2a_Bs hPQ hμ0 hμ1
  · obtain ⟨e0, e1, e2⟩ := col_A P
    rw [e0, e1, e2]
    exact fd2a_As hPQ hμ0 hμ1
  · obtain ⟨e0, e1, e2⟩ := col_C P
    rw [e0, e1, e2]
    exact fd2a_C hPQ hμ0 hμ1 (by rw [abs_neg, abs_of_nonneg hPP]) (abs_of_nonneg hg)
  · obtain ⟨e0, e1, e2⟩ := col_nC P
    rw [e0, e1, e2]
    exact fd2a_C hPQ hμ0 hμ1 (abs_of_nonneg hPP) (by rw [abs_neg, abs_of_nonneg hg])
  · obtain ⟨e0, e1, e2⟩ := col_nA P
    rw [e0, e1, e2]
    exact fd2a_Ao hPQ hμ0 hμ1
  · have hP4 : 4 ≤ P := by
      rcases hch with h | h
      · exact absurd ⟨rfl, rfl, rfl⟩ h
      · exact h
    obtain ⟨e0, e1, e2⟩ := col_nB P
    rw [e0, e1, e2]
    exact fd2a_chain hPQ hP4 hμ0 hμ1
  · obtain ⟨e0, e1, e2⟩ := col_nE P
    rw [e0, e1, e2]
    exact fd2a_E hPQ hμ0 hμ1 (by rw [abs_neg, abs_of_nonneg (sq_nonneg _)])

/-! ### FD2 (b), `P = 2`: dominance at the state `-μ₀ α(B)` -/

section Dom

variable {Q μ m : ℝ}

/-- Common facts at `P = 2`, `m = μ₀`. -/
lemma dom_facts (hQ : 4 ≤ Q) (hμ0 : Q - 1 ≤ (Q + 1) * μ) (hμ1 : μ ≤ 1)
    (hm : (Q + 1) * m = Q - 1) : 0 ≤ μ ∧ 0 ≤ m ∧ m ≤ 1 ∧ μ * m ≤ μ ∧ 4 * μ ≤ Q * μ := by
  have hμpos : 0 ≤ μ := by nlinarith
  have hm0 : 0 ≤ m := by nlinarith
  have hm1 : m ≤ 1 := by nlinarith
  refine ⟨hμpos, hm0, hm1, ?_, mul_le_mul_of_nonneg_right hQ hμpos⟩
  have := mul_le_mul_of_nonneg_left hm1 hμpos
  linarith

/-- `24 (Q - μ) m ≥ 2Q(1+μ)` and `22 (Q - μ) m ≥ 2Q(1+μ)` for `m = μ₀`, `Q ≥ 4`. -/
lemma dom_key (hQ : 4 ≤ Q) (hμ1 : μ ≤ 1) (hm : (Q + 1) * m = Q - 1) :
    2 * Q * (1 + μ) ≤ 22 * ((Q - μ) * m) := by
  have hQ1 : (0:ℝ) < Q + 1 := by linarith
  have e1 : (Q + 1) * (22 * ((Q - μ) * m)) = 22 * ((Q - μ) * (Q - 1)) := by rw [← hm]; ring
  have e2 : (Q - 1) * (Q - 1) ≤ (Q - μ) * (Q - 1) :=
    mul_le_mul_of_nonneg_right (by linarith) (by linarith)
  have e3 : (Q + 1) * (2 * Q * (1 + μ)) ≤ (Q + 1) * (4 * Q) :=
    mul_le_mul_of_nonneg_left (by nlinarith) hQ1.le
  have e4 : 4 * Q * (Q + 1) ≤ 22 * (Q - 1) * (Q - 1) := by nlinarith
  apply le_of_mul_le_mul_left _ hQ1
  nlinarith

lemma dom_E {A2 : ℝ} (hQ : 4 ≤ Q) (hμ0 : Q - 1 ≤ (Q + 1) * μ) (hμ1 : μ ≤ 1)
    (hm : (Q + 1) * m = Q - 1) (h2 : |A2| = (2 + 1) ^ 2) :
    2 * Q * (1 + μ) ≤ Sc 2 Q μ 0 0 A2 (m * (2 * 2 * (2 + 1))) (m * (2 * 2))
      (-(m * (2 ^ 2 + 2 * 2 - 1))) := by
  obtain ⟨hμpos, hm0, hm1, F1, F2⟩ := dom_facts hQ hμ0 hμ1 hm
  have hL := boundE (Or.inr ⟨rfl, hQ⟩) hμpos hμ1 h2 (B0 := m * (2 * 2 * (2 + 1)))
    (B1 := m * (2 * 2)) (B2 := -(m * (2 ^ 2 + 2 * 2 - 1)))
    (by rw [abs_neg, abs_of_nonneg (by positivity)]; nlinarith)
  rw [abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)] at hL
  linarith

lemma dom_C {A1 A2 : ℝ} (hQ : 4 ≤ Q) (hμ0 : Q - 1 ≤ (Q + 1) * μ) (hμ1 : μ ≤ 1)
    (hm : (Q + 1) * m = Q - 1) (h1 : |A1| = 2 * 2 * (2 + 1)) (h2 : |A2| = 2 ^ 2 - 1) :
    2 * Q * (1 + μ) ≤ Sc 2 Q μ 0 A1 A2 (m * (2 * 2 * (2 + 1))) (m * (2 * 2))
      (-(m * (2 ^ 2 + 2 * 2 - 1))) := by
  obtain ⟨hμpos, hm0, hm1, F1, F2⟩ := dom_facts hQ hμ0 hμ1 hm
  have hL := boundC (Or.inr ⟨rfl, hQ⟩) hμpos hμ1 h1 h2 (B0 := m * (2 * 2 * (2 + 1)))
    (B1 := m * (2 * 2)) (B2 := -(m * (2 ^ 2 + 2 * 2 - 1)))
    (by rw [abs_of_nonneg (by positivity)]; nlinarith)
    (by rw [abs_neg, abs_of_nonneg (by positivity)]; nlinarith)
  rw [abs_of_nonneg (by positivity)] at hL
  linarith

lemma dom_B {A0 A1 A2 : ℝ} (hQ : 4 ≤ Q) (hμ0 : Q - 1 ≤ (Q + 1) * μ) (hμ1 : μ ≤ 1)
    (hm : (Q + 1) * m = Q - 1) (h0 : |A0| = 2 * 2 * (2 + 1)) (h1 : |A1| = 2 * 2)
    (h2 : |A2| = 2 ^ 2 + 2 * 2 - 1) :
    2 * Q * (1 + μ) ≤ Sc 2 Q μ A0 A1 A2 (m * (2 * 2 * (2 + 1))) (m * (2 * 2))
      (-(m * (2 ^ 2 + 2 * 2 - 1))) := by
  obtain ⟨hμpos, hm0, hm1, F1, F2⟩ := dom_facts hQ hμ0 hμ1 hm
  have hL := Sc_ge_small (P := 2) (Q := Q) (μ := μ) (A0 := A0) (A1 := A1) (A2 := A2) (B0 := m * (2 * 2 * (2 + 1)))
    (B1 := m * (2 * 2)) (B2 := -(m * (2 ^ 2 + 2 * 2 - 1))) hμpos hμ1 (by linarith)
    (by rw [h0, abs_of_nonneg (by positivity)]; nlinarith)
    (by rw [h1, abs_of_nonneg (by positivity)]; nlinarith)
    (by rw [h2, abs_neg, abs_of_nonneg (by positivity)]; nlinarith)
  rw [h0, h1, h2] at hL
  unfold Dp at hL
  linarith

lemma dom_A (hQ : 4 ≤ Q) (hμ0 : Q - 1 ≤ (Q + 1) * μ) (hμ1 : μ ≤ 1)
    (hm : (Q + 1) * m = Q - 1) :
    2 * Q * (1 + μ) ≤ Sc 2 Q μ (2 * 2 * (2 + 1)) (-(2 * 2 ^ 2)) (2 ^ 2 + 1)
      (m * (2 * 2 * (2 + 1))) (m * (2 * 2)) (-(m * (2 ^ 2 + 2 * 2 - 1))) := by
  obtain ⟨hμpos, hm0, hm1, F1, F2⟩ := dom_facts hQ hμ0 hμ1 hm
  have hμQ : μ ≤ Q := by linarith
  have c0 : hcell Q μ (2 * 2 * (2 + 1)) (m * (2 * 2 * (2 + 1))) =
      -2 * (Q - μ) * (m * (2 * 2 * (2 + 1))) :=
    hcell_same_pos hμpos hμQ (by positivity) (by nlinarith)
  have c1 := hcell_nonpos hμpos hμ1 hμQ (A := -(2 * 2 ^ 2)) (B := m * (2 * 2))
    (by rw [abs_neg, abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)]; nlinarith)
  have c2 := hcell_nonpos hμpos hμ1 hμQ (A := 2 ^ 2 + 1) (B := -(m * (2 ^ 2 + 2 * 2 - 1)))
    (by rw [abs_neg, abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)]; nlinarith)
  have K := dom_key hQ hμ1 hm
  have K2 : 0 ≤ (Q - μ) * m := mul_nonneg (by linarith) hm0
  unfold Sc Dp
  rw [c0, abs_of_nonneg (by positivity), abs_neg, abs_of_nonneg (by positivity),
    abs_of_nonneg (by positivity)]
  linarith

lemma dom_nA (hQ : 4 ≤ Q) (hμ0 : Q - 1 ≤ (Q + 1) * μ) (hμ1 : μ ≤ 1)
    (hm : (Q + 1) * m = Q - 1) :
    2 * Q * (1 + μ) ≤ Sc 2 Q μ (-(2 * 2 * (2 + 1))) (2 * 2 ^ 2) (-(2 ^ 2 + 1))
      (m * (2 * 2 * (2 + 1))) (m * (2 * 2)) (-(m * (2 ^ 2 + 2 * 2 - 1))) := by
  obtain ⟨hμpos, hm0, hm1, F1, F2⟩ := dom_facts hQ hμ0 hμ1 hm
  have hμQ : μ ≤ Q := by linarith
  have c0 := hcell_nonpos hμpos hμ1 hμQ (A := -(2 * 2 * (2 + 1))) (B := m * (2 * 2 * (2 + 1)))
    (by rw [abs_neg, abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)]; nlinarith)
  have c1 : hcell Q μ (2 * 2 ^ 2) (m * (2 * 2)) = -2 * (Q - μ) * (m * (2 * 2)) :=
    hcell_same_pos hμpos hμQ (by positivity) (by nlinarith)
  have K := dom_key hQ hμ1 hm
  have K2 : 0 ≤ (Q - μ) * m := mul_nonneg (by linarith) hm0
  unfold Sc Dp
  rw [c1, abs_neg, abs_of_nonneg (by positivity), abs_of_nonneg (by positivity), abs_neg,
    abs_of_nonneg (by positivity)]
  rcases le_total (7 * m) 5 with h7 | h7
  · rw [hc_same_neg (A := -(2 ^ 2 + 1)) (B := -(m * (2 ^ 2 + 2 * 2 - 1))) hμpos hμQ
      (by nlinarith) (by nlinarith)]
    linarith
  · rw [hc_big_neg (A := -(2 ^ 2 + 1)) (B := -(m * (2 ^ 2 + 2 * 2 - 1))) (by linarith)
      (by norm_num) (by nlinarith)]
    have G1 := mul_le_mul_of_nonneg_right hμ1 hm0
    have G2 := mul_le_mul_of_nonneg_left hμ1 (by linarith : (0:ℝ) ≤ Q)
    have G3 := mul_le_mul_of_nonneg_right hQ hm0
    linarith

end Dom

/-- For `P = 2`, at the state `μ₀ (2pP, 2P, -(p²-2))` every column pays at least the chain
cost `Q(1+μ) Δ(B) = 2Q(1+μ)`. -/
theorem fd2dom {P Q μ m c0 c1 c2 : ℝ} (hP : P = 2) (hQ : 4 ≤ Q) (hμ0 : Q - 1 ≤ (Q + 1) * μ)
    (hμ1 : μ ≤ 1) (hm : (Q + 1) * m = Q - 1)
    (hc0 : c0 = 1 ∨ c0 = -1) (hc1 : c1 = 1 ∨ c1 = -1) (hc2 : c2 = 1 ∨ c2 = -1) :
    2 * Q * (1 + μ) ≤ Sc P Q μ (Mc0 P c0 c1 c2) (Mc1 P c0 c1 c2) (Mc2 P c0 c1 c2)
      (m * (2 * P * (P + 1))) (m * (2 * P)) (-(m * (P ^ 2 + 2 * P - 1))) := by
  subst hP
  rcases hc0 with rfl | rfl <;> rcases hc1 with rfl | rfl <;> rcases hc2 with rfl | rfl
  · obtain ⟨e0, e1, e2⟩ := col_E 2
    rw [e0, e1, e2]
    exact dom_E hQ hμ0 hμ1 hm (abs_of_nonneg (sq_nonneg _))
  · obtain ⟨e0, e1, e2⟩ := col_B 2
    rw [e0, e1, e2]
    exact dom_B hQ hμ0 hμ1 hm (by rw [abs_neg, abs_of_nonneg (by positivity)])
      (by rw [abs_neg, abs_of_nonneg (by positivity)]) (abs_of_nonneg (by norm_num))
  · obtain ⟨e0, e1, e2⟩ := col_A 2
    rw [e0, e1, e2]
    exact dom_A hQ hμ0 hμ1 hm
  · obtain ⟨e0, e1, e2⟩ := col_C 2
    rw [e0, e1, e2]
    exact dom_C hQ hμ0 hμ1 hm (by rw [abs_neg, abs_of_nonneg (by positivity)])
      (abs_of_nonneg (by norm_num))
  · obtain ⟨e0, e1, e2⟩ := col_nC 2
    rw [e0, e1, e2]
    exact dom_C hQ hμ0 hμ1 hm (abs_of_nonneg (by positivity))
      (by rw [abs_neg, abs_of_nonneg (by norm_num)])
  · obtain ⟨e0, e1, e2⟩ := col_nA 2
    rw [e0, e1, e2]
    exact dom_nA hQ hμ0 hμ1 hm
  · obtain ⟨e0, e1, e2⟩ := col_nB 2
    rw [e0, e1, e2]
    exact dom_B hQ hμ0 hμ1 hm (abs_of_nonneg (by positivity)) (abs_of_nonneg (by positivity))
      (by rw [abs_neg, abs_of_nonneg (by norm_num)])
  · obtain ⟨e0, e1, e2⟩ := col_nE 2
    rw [e0, e1, e2]
    exact dom_E hQ hμ0 hμ1 hm (by rw [abs_neg, abs_of_nonneg (sq_nonneg _)])

/-- **Two chain columns pay for the corner** (`P = 2`): with `x = μ_{b-2}`, `y = μ_{b-3} > L`,
`q x = Q - y`, `q ρ = Q - x`: `2Q(1+x) + 2Q(1+y) > 8 q ρ`. -/
lemma two_col {Q x y ρ : ℝ} (hQ : 4 ≤ Q) (hx : (Q + 1) * x = Q - y) (hρ : (Q + 1) * ρ = Q - x)
    (hy : Q < (Q + 2) * y) : 8 * (Q + 1) * ρ < 2 * Q * (1 + x) + 2 * Q * (1 + y) := by
  have h1 : (Q + 1) * (-4 * Q + (2 * Q + 8) * x + 2 * Q * y) =
      -2 * Q ^ 2 + 4 * Q + 2 * (Q ^ 2 - 4) * y := by linear_combination (2 * Q + 8) * hx
  have h2 : 0 < -2 * Q ^ 2 + 4 * Q + 2 * (Q ^ 2 - 4) * y := by
    nlinarith [mul_lt_mul_of_pos_left hy (by linarith : (0:ℝ) < Q - 2)]
  have h3 : 0 < -4 * Q + (2 * Q + 8) * x + 2 * Q * y := by
    by_contra hc
    push Not at hc
    nlinarith [mul_nonpos_of_nonneg_of_nonpos (by linarith : (0:ℝ) ≤ Q + 1) hc]
  have h4 : 8 * (Q + 1) * ρ = 8 * (Q - x) := by rw [← hρ]; ring
  rw [h4]
  linarith

end ICGEqualParityB
