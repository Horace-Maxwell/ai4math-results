import Mathlib
import Research.ICGGeneralMain

/-!
# Equal-parity exponents: one-dimensional lemmas (round 4)

Formalisation of §1 of `work/round4/icg-equal-parity/PROOF.md`. Index conventions follow
`ICGGeneralPath`: `Zp x m w k` is the note's `z_{k-1}`, `nu x k` is the note's `μ_{k-1}`.

* `L1_potential` (Lemma P): for every real vector `w`,
  `‖T_m(x) w‖₁ = x^m (∑_{k<m} c_k |w_k| + ν_m |w_m| + (1/x) ∑_{k<m} h_{ν_k}(w_k, Z_{k+1}))`.
* `nu_sub_L` (Lemma M): `ν_k - L = (-1/x)^k (1 - L)`, `L = (x-1)/(x+1)`.
* `Zp_alt_tail`: along an alternating tail `|Z_j| = ν_{m-j}`; `Zp_sgnv_zero`: `Z_0(s) = ν_m`.
* `noncorner_le` (Lemma C′): `∑_{k<m} |Z_k(y) - Z_{k+1}(y)| ≤ ∑_{k<m} |Z_k(s) - Z_{k+1}(s)|` for sign vectors.
* `lemmaB`: if `m` is odd and `y_0 = y_m`, then `(R-1)·2ν_m < (3R-1)·slack(y)`.
-/

noncomputable section

namespace ICGEqualParity

open Finset ICGGeneral

/-! ### Lemma P -/

lemma step_real {x : ℝ} (hx : 1 < x) (m : ℕ) (w : ℕ → ℝ) {k : ℕ} (hk : k < m) :
    |Zp x m w k - Zp x m w (k + 1)| + nu x k * |Zp x m w k| -
        nu x (k + 1) * |Zp x m w (k + 1)| =
      cc x k * |w k| + hcell (x - 1) (nu x k) (w k) (Zp x m w (k + 1)) / x := by
  have hx0 : 0 < x := by linarith
  have hx1 : 0 < x - 1 := by linarith
  rw [Zp_rec hx0.ne' m w hk, nu_succ]
  unfold cc hcell
  set Z := Zp x m w (k + 1) with hZ
  have e1 : (Z + (x - 1) * w k) / x - Z = (x - 1) * (w k - Z) / x := by
    field_simp
    ring
  rw [e1, abs_div, abs_div, abs_mul, abs_of_pos hx0, abs_of_pos hx1]
  field_simp
  ring

/-- **Lemma P** (potential identity for real vectors). -/
theorem L1_potential {x : ℝ} (hx : 1 < x) (m : ℕ) (w : ℕ → ℝ) :
    L1 x m w = x ^ m * (∑ k ∈ range m, cc x k * |w k| + nu x m * |w m| +
      (∑ k ∈ range m, hcell (x - 1) (nu x k) (w k) (Zp x m w (k + 1))) / x) := by
  have hx0 : 0 < x := by linarith
  rw [L1_path hx0]
  congr 1
  have hf : ∀ k ∈ range m, |Zp x m w k - Zp x m w (k + 1)| =
      (cc x k * |w k| + hcell (x - 1) (nu x k) (w k) (Zp x m w (k + 1)) / x) -
        (nu x k * |Zp x m w k| - nu x (k + 1) * |Zp x m w (k + 1)|) := by
    intro k hk
    rw [Finset.mem_range] at hk
    rw [← step_real hx m w hk]
    ring
  have htel := Finset.sum_range_sub' (fun k => nu x k * |Zp x m w k|) m
  rw [Finset.sum_congr rfl hf, Finset.sum_sub_distrib, Finset.sum_add_distrib, htel, nu_zero,
    one_mul, Zp_self, Finset.sum_div]
  ring

/-! ### Lemma M: the potential oscillates around `L = (x-1)/(x+1)` -/

lemma nu_sub_L {x : ℝ} (hx : 0 < x) (k : ℕ) :
    nu x k - (x - 1) / (x + 1) = (-1 / x) ^ k * (1 - (x - 1) / (x + 1)) := by
  induction k with
  | zero => simp [nu_zero]
  | succ k ih =>
    rw [nu_succ, pow_succ]
    have hx1 : x + 1 ≠ 0 := by linarith
    have e : (x - 1 - nu x k) / x - (x - 1) / (x + 1) =
        (-1 / x) * (nu x k - (x - 1) / (x + 1)) := by
      field_simp
      ring
    rw [e, ih]
    ring

lemma nu_even_gt {x : ℝ} (hx : 1 < x) {k : ℕ} (hk : Even k) : (x - 1) / (x + 1) < nu x k := by
  have hx0 : 0 < x := by linarith
  have h := nu_sub_L hx0 k
  have hL : 0 < 1 - (x - 1) / (x + 1) := by
    rw [sub_pos, div_lt_one (by linarith)]
    linarith
  have hp : 0 < (-1 / x) ^ k := by
    rw [neg_div, hk.neg_pow]
    positivity
  nlinarith

lemma nu_odd_lt {x : ℝ} (hx : 1 < x) {k : ℕ} (hk : Odd k) : nu x k < (x - 1) / (x + 1) := by
  have hx0 : 0 < x := by linarith
  have h := nu_sub_L hx0 k
  have hL : 0 < 1 - (x - 1) / (x + 1) := by
    rw [sub_pos, div_lt_one (by linarith)]
    linarith
  have hp : (-1 / x) ^ k < 0 := by
    rw [neg_div, hk.neg_pow, neg_lt_zero]
    positivity
  nlinarith

/-- For even `k ≥ 2`, `ν_k ≤ ν_2` (the even-indexed potentials decrease towards `L`). -/
lemma nu_even_le_two {x : ℝ} (hx : 1 < x) {k : ℕ} (hk : Even k) (hk2 : 2 ≤ k) :
    nu x k ≤ nu x 2 := by
  have hx0 : 0 < x := by linarith
  have h := nu_sub_L hx0 k
  have h2 := nu_sub_L hx0 2
  have hL : 0 < 1 - (x - 1) / (x + 1) := by
    rw [sub_pos, div_lt_one (by linarith)]
    linarith
  have hk' : (-1 / x) ^ k = (1 / x) ^ k := by
    rw [neg_div, hk.neg_pow]
  have h2' : (-1 / x) ^ 2 = (1 / x) ^ 2 := by ring
  have hmono : (1 / x) ^ k ≤ (1 / x) ^ 2 := by
    apply pow_le_pow_of_le_one (by positivity) _ hk2
    rw [div_le_one hx0]
    linarith
  rw [hk'] at h
  rw [h2'] at h2
  nlinarith

/-! ### Paths of sign vectors: one step -/

lemma Zp_step_alt {x : ℝ} (hx : 2 ≤ x) {m : ℕ} {y : ℕ → ℝ} (hy : IsSign m y) {k : ℕ} (hk : k < m)
    (halt : y k ≠ y (k + 1)) : |Zp x m y k| = (x - 1 - |Zp x m y (k + 1)|) / x := by
  have hx0 : 0 < x := by linarith
  have hZ1 : |Zp x m y (k + 1)| ≤ 1 := Zp_abs_le (by linarith) (isSign_abs_le hy) (k + 1) hk
  have hs := Zp_abs_eq hx hy (show k + 1 ≤ m from hk)
  have hlo := neg_abs_le (Zp x m y (k + 1))
  have hhi := le_abs_self (Zp x m y (k + 1))
  rw [Zp_rec hx0.ne' m y hk, abs_div, abs_of_pos hx0, hs]
  congr 1
  rcases hy k hk.le with h0 | h0 <;> rcases hy (k + 1) hk with h1 | h1
  · exact absurd (h0.trans h1.symm) halt
  · rw [h0, h1]
    have hnn : 0 ≤ Zp x m y (k + 1) + (x - 1) * 1 := by linarith
    rw [abs_of_nonneg hnn]
    ring
  · rw [h0, h1]
    have hnp : Zp x m y (k + 1) + (x - 1) * -1 ≤ 0 := by linarith
    rw [abs_of_nonpos hnp]
    ring
  · exact absurd (h0.trans h1.symm) halt

/-- Along an alternating tail the path magnitudes are the potentials: `|Z_j| = ν_{m-j}`. -/
lemma Zp_alt_tail {x : ℝ} (hx : 2 ≤ x) {m : ℕ} {y : ℕ → ℝ} (hy : IsSign m y) :
    ∀ d j, j + d = m → (∀ i, j ≤ i → i < m → y i ≠ y (i + 1)) → |Zp x m y j| = nu x d := by
  intro d
  induction d with
  | zero =>
    intro j hj _
    simp only [Nat.add_zero] at hj
    subst hj
    rw [Zp_self, isSign_abs hy le_rfl, nu_zero]
  | succ d ih =>
    intro j hj halt
    rw [Zp_step_alt hx hy (by omega) (halt j le_rfl (by omega)),
      ih (j + 1) (by omega) (fun i hi him => halt i (by omega) him), nu_succ]

lemma Zp_sgnv_zero {x : ℝ} (hx : 2 < x) (m : ℕ) : Zp x m sgnv 0 = nu x m := by
  have hx0 : 0 < x := by linarith
  have h := Zp_alt_tail hx.le (sgnv_isSign m) m 0 (by omega) (by
    intro i _ _ h
    rw [sgnv_succ] at h
    have h0 : sgnv i ≠ 0 := by simp [sgnv]
    exact h0 (by linarith))
  have hpos : 0 < Zp x m sgnv 0 := by
    have hs := Zp_sign hx.le (sgnv_isSign m) 0 (Nat.zero_le _)
    rw [sgnv_zero, one_mul] at hs
    exact lt_of_lt_of_le (div_pos (by linarith) hx0) hs
  rw [← h, abs_of_pos hpos]

/-! ### Lemma C′: the non-corner part is maximised by `s` -/

/-- Potential with an arbitrary start value. -/
def nuc (x c : ℝ) : ℕ → ℝ
  | 0 => c
  | k + 1 => (x - 1 - nuc x c k) / x

lemma nuc_succ (x c : ℝ) (k : ℕ) : nuc x c (k + 1) = (x - 1 - nuc x c k) / x := rfl

lemma nuc_zero_bounds {x : ℝ} (hx : 2 < x) : ∀ k, 0 ≤ nuc x 0 k ∧ nuc x 0 k ≤ 1 := by
  have hx0 : 0 < x := by linarith
  intro k
  induction k with
  | zero => simp [nuc]
  | succ k ih =>
    rw [nuc_succ]
    constructor
    · apply div_nonneg _ hx0.le
      linarith [ih.2]
    · rw [div_le_one hx0]
      linarith [ih.1]

/-- One step of the potential `nuc`, for sign vectors (as in `fk_eq`). -/
lemma step_sign_c {x : ℝ} (hx : 2 < x) (c : ℝ) {m : ℕ} {y : ℕ → ℝ} (hy : IsSign m y) {k : ℕ}
    (hk : k < m) :
    |Zp x m y k - Zp x m y (k + 1)| + nuc x c k * |Zp x m y k| -
        nuc x c (k + 1) * |Zp x m y (k + 1)| =
      (x - 1) * (1 + nuc x c k) / x -
        (if y k = y (k + 1) then 2 * nuc x c (k + 1) * |Zp x m y (k + 1)| else 0) := by
  have hx0 : 0 < x := by linarith
  have hb1 : |Zp x m y (k + 1)| ≤ 1 := Zp_abs_le (by linarith) (isSign_abs_le hy) (k + 1) hk
  have hs1 := Zp_sign hx.le hy (k + 1) hk
  have hq : 0 < (x - 2) / x := div_pos (by linarith) hx0
  rw [Zp_rec hx0.ne' m y hk, nuc_succ]
  set Z := Zp x m y (k + 1) with hZ
  have hZle := le_abs_self Z
  have hZge := neg_abs_le Z
  rcases hy k hk.le with h0 | h0 <;> rcases hy (k + 1) hk with h1 | h1
  · rw [h1, one_mul] at hs1
    have hZpos : 0 < Z := lt_of_lt_of_le hq hs1
    have e1 : (Z + (x - 1) * y k) / x - Z = (x - 1) * (1 - Z) / x := by
      rw [h0]; field_simp; ring
    have e2 : 0 < (Z + (x - 1) * y k) / x := by
      rw [h0]; apply div_pos _ hx0; linarith
    rw [e1, abs_of_nonneg (div_nonneg (mul_nonneg (by linarith) (by linarith)) hx0.le),
      abs_of_pos e2, abs_of_pos hZpos, if_pos (by rw [h0, h1]), h0]
    field_simp
    ring
  · rw [h1] at hs1
    have hZneg : Z < 0 := by linarith
    have e1 : (Z + (x - 1) * y k) / x - Z = (x - 1) * (1 - Z) / x := by
      rw [h0]; field_simp; ring
    have e2 : 0 < (Z + (x - 1) * y k) / x := by
      rw [h0]; apply div_pos _ hx0; linarith
    rw [e1, abs_of_nonneg (div_nonneg (mul_nonneg (by linarith) (by linarith)) hx0.le),
      abs_of_pos e2, abs_of_neg hZneg, if_neg (by rw [h0, h1]; norm_num), h0]
    field_simp
    ring
  · rw [h1, one_mul] at hs1
    have hZpos : 0 < Z := lt_of_lt_of_le hq hs1
    have e1 : (Z + (x - 1) * y k) / x - Z = -((x - 1) * (1 + Z) / x) := by
      rw [h0]; field_simp; ring
    have e2 : (Z + (x - 1) * y k) / x < 0 := by
      rw [h0]; apply div_neg_of_neg_of_pos _ hx0; linarith
    rw [e1, abs_neg, abs_of_nonneg (div_nonneg (mul_nonneg (by linarith) (by linarith)) hx0.le),
      abs_of_neg e2, abs_of_pos hZpos, if_neg (by rw [h0, h1]; norm_num), h0]
    field_simp
    ring
  · rw [h1] at hs1
    have hZneg : Z < 0 := by linarith
    have e1 : (Z + (x - 1) * y k) / x - Z = -((x - 1) * (1 + Z) / x) := by
      rw [h0]; field_simp; ring
    have e2 : (Z + (x - 1) * y k) / x < 0 := by
      rw [h0]; apply div_neg_of_neg_of_pos _ hx0; linarith
    rw [e1, abs_neg, abs_of_nonneg (div_nonneg (mul_nonneg (by linarith) (by linarith)) hx0.le),
      abs_of_neg e2, abs_of_neg hZneg, if_pos (by rw [h0, h1]), h0]
    field_simp
    ring

/-- The non-corner part of the path length, expressed with the potential `nuc x 0`. -/
lemma noncorner_eq {x : ℝ} (hx : 2 < x) {m : ℕ} {y : ℕ → ℝ} (hy : IsSign m y) :
    ∑ k ∈ range m, |Zp x m y k - Zp x m y (k + 1)| =
      ∑ k ∈ range m, (x - 1) * (1 + nuc x 0 k) / x + nuc x 0 m -
        ∑ k ∈ range m,
          (if y k = y (k + 1) then 2 * nuc x 0 (k + 1) * |Zp x m y (k + 1)| else 0) := by
  have hf : ∀ k ∈ range m, |Zp x m y k - Zp x m y (k + 1)| =
      ((x - 1) * (1 + nuc x 0 k) / x -
        (if y k = y (k + 1) then 2 * nuc x 0 (k + 1) * |Zp x m y (k + 1)| else 0)) -
        (nuc x 0 k * |Zp x m y k| - nuc x 0 (k + 1) * |Zp x m y (k + 1)|) := by
    intro k hk
    rw [Finset.mem_range] at hk
    rw [← step_sign_c hx 0 hy hk]
    ring
  have htel := Finset.sum_range_sub' (fun k => nuc x 0 k * |Zp x m y k|) m
  rw [Finset.sum_congr rfl hf, Finset.sum_sub_distrib, Finset.sum_sub_distrib, htel]
  simp only [nuc, zero_mul, Zp_self]
  rw [isSign_abs hy le_rfl]
  ring

/-- **Lemma C′.** -/
theorem noncorner_le {x : ℝ} (hx : 2 < x) {m : ℕ} {y : ℕ → ℝ} (hy : IsSign m y) :
    ∑ k ∈ range m, |Zp x m y k - Zp x m y (k + 1)| ≤
      ∑ k ∈ range m, |Zp x m sgnv k - Zp x m sgnv (k + 1)| := by
  rw [noncorner_eq hx hy, noncorner_eq hx (sgnv_isSign m)]
  have h1 : 0 ≤ ∑ k ∈ range m,
      (if y k = y (k + 1) then 2 * nuc x 0 (k + 1) * |Zp x m y (k + 1)| else 0) := by
    apply Finset.sum_nonneg
    intro k _
    split_ifs
    · exact mul_nonneg (mul_nonneg (by norm_num) (nuc_zero_bounds hx _).1) (abs_nonneg _)
    · exact le_rfl
  have h2 : ∑ k ∈ range m,
      (if sgnv k = sgnv (k + 1) then 2 * nuc x 0 (k + 1) * |Zp x m sgnv (k + 1)| else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro k _
    rw [if_neg]
    rw [sgnv_succ]
    intro h
    have h0 : sgnv k ≠ 0 := by simp [sgnv]
    exact h0 (by linarith)
  linarith

/-- The non-corner part of `s`: `∑ |ΔZ(s)| = ∑ c_k` (i.e. `D̂ - ρ`). -/
lemma noncorner_sgnv {x : ℝ} (hx : 2 < x) (m : ℕ) :
    ∑ k ∈ range m, |Zp x m sgnv k - Zp x m sgnv (k + 1)| = ∑ k ∈ range m, cc x k := by
  have hx0 : 0 < x := by linarith
  have h1 := L1_path hx0 m sgnv
  have h2 := L1_sgnv hx m
  rw [Zp_sgnv_zero hx, abs_of_pos (nu_pos hx m)] at h1
  have hp := pow_pos hx0 m
  have : x ^ m * (nu x m + ∑ k ∈ range m, |Zp x m sgnv k - Zp x m sgnv (k + 1)|) =
      x ^ m * (∑ k ∈ range m, cc x k + nu x m) := by rw [← h1, h2]
  have := mul_left_cancel₀ hp.ne' this
  linarith

/-! ### Lemma B -/

/-- If `m` is odd and `y_0 = y_m`, the slack pays for the corner: `(R-1)·2ν_m < (3R-1)·slack(y)`. -/
theorem lemmaB {x R : ℝ} (hx : 3 ≤ x) (hR : 1 ≤ R) {m : ℕ} (hm : Odd m) {y : ℕ → ℝ}
    (hy : IsSign m y) (hy0 : y 0 = y m) :
    (R - 1) * (2 * nu x m) < (3 * R - 1) * slack x m y := by
  have hx0 : 0 < x := by linarith
  have hx2 : 2 < x := by linarith
  set S := (range m).filter (fun k => y k = y (k + 1)) with hS
  -- S is nonempty, otherwise y alternates
  have hSne : S.Nonempty := by
    by_contra hne
    rw [Finset.not_nonempty_iff_eq_empty] at hne
    have halt : ∀ k < m, y k ≠ y (k + 1) := by
      intro k hk heq
      have : k ∈ S := by rw [hS, Finset.mem_filter, Finset.mem_range]; exact ⟨hk, heq⟩
      rw [hne] at this
      exact absurd this (Finset.notMem_empty k)
    rcases alternating_eq hy halt with h | h
    · have e0 := h 0 (Nat.zero_le _)
      have em := h m le_rfl
      rw [sgnv_zero] at e0
      rw [hy0, em] at e0
      unfold sgnv at e0
      rw [hm.neg_one_pow] at e0
      norm_num at e0
    · have e0 := h 0 (Nat.zero_le _)
      have em := h m le_rfl
      rw [sgnv_zero] at e0
      rw [hy0, em] at e0
      unfold sgnv at e0
      rw [hm.neg_one_pow] at e0
      norm_num at e0
  set J := S.max' hSne with hJ
  have hJS : J ∈ S := Finset.max'_mem S hSne
  rw [hS, Finset.mem_filter, Finset.mem_range] at hJS
  obtain ⟨hJm, hJeq⟩ := hJS
  -- after J the vector alternates
  have halt : ∀ i, J + 1 ≤ i → i < m → y i ≠ y (i + 1) := by
    intro i hi him heq
    have hiS : i ∈ S := by rw [hS, Finset.mem_filter, Finset.mem_range]; exact ⟨him, heq⟩
    have := Finset.le_max' S i hiS
    rw [← hJ] at this
    omega
  have htail := Zp_alt_tail hx2.le hy (m - (J + 1)) (J + 1) (by omega) halt
  -- slack ≥ 2 ν_{J+1} |Z_{J+1}|
  have hsl : 2 * nu x (J + 1) * nu x (m - (J + 1)) ≤ slack x m y := by
    unfold slack
    have hterm : (if y J = y (J + 1) then 2 * nu x (J + 1) * |Zp x m y (J + 1)| else 0) =
        2 * nu x (J + 1) * nu x (m - (J + 1)) := by
      rw [if_pos hJeq, htail]
    rw [← hterm]
    apply Finset.single_le_sum (f := fun k =>
      if y k = y (k + 1) then 2 * nu x (k + 1) * |Zp x m y (k + 1)| else 0)
    · intro k _
      split_ifs
      · exact mul_nonneg (mul_nonneg (by norm_num) (nu_pos hx2 _).le) (abs_nonneg _)
      · exact le_rfl
    · exact Finset.mem_range.mpr hJm
  -- parity: one of J+1, m-(J+1) is even
  set L := (x - 1) / (x + 1) with hL
  have hLpos : 0 < L := div_pos (by linarith) (by linarith)
  have hcpos : 0 < (x - 2) / x := div_pos (by linarith) hx0
  have hprod : L * ((x - 2) / x) < nu x (J + 1) * nu x (m - (J + 1)) := by
    have hsum : (J + 1) + (m - (J + 1)) = m := by omega
    rcases Nat.even_or_odd (J + 1) with he | ho
    · have h1 := nu_even_gt (x := x) (by linarith) he
      have h2 := (nu_bounds hx2.le (m - (J + 1))).1
      calc L * ((x - 2) / x) < nu x (J + 1) * ((x - 2) / x) :=
            mul_lt_mul_of_pos_right h1 hcpos
        _ ≤ nu x (J + 1) * nu x (m - (J + 1)) :=
            mul_le_mul_of_nonneg_left h2 (nu_pos hx2 _).le
    · have he : Even (m - (J + 1)) := by
        rcases ho with ⟨a, ha⟩
        rcases hm with ⟨b, hb⟩
        exact ⟨b - a, by omega⟩
      have h1 := nu_even_gt (x := x) (by linarith) he
      have h2 := (nu_bounds hx2.le (J + 1)).1
      calc L * ((x - 2) / x) = ((x - 2) / x) * L := by ring
        _ < ((x - 2) / x) * nu x (m - (J + 1)) := mul_lt_mul_of_pos_left h1 hcpos
        _ ≤ nu x (J + 1) * nu x (m - (J + 1)) :=
            mul_le_mul_of_nonneg_right h2 (nu_pos hx2 _).le
  have hnum : (R - 1) ≤ (3 * R - 1) * ((x - 2) / x) := by
    rw [mul_div_assoc', le_div_iff₀ hx0]
    nlinarith
  have hnum_m : nu x m < L := nu_odd_lt (by linarith) hm
  have h3R : 0 < 3 * R - 1 := by linarith
  have hR1 : 0 ≤ R - 1 := by linarith
  calc (R - 1) * (2 * nu x m) ≤ (R - 1) * (2 * L) := by nlinarith
    _ ≤ (3 * R - 1) * ((x - 2) / x) * (2 * L) := by nlinarith
    _ = (3 * R - 1) * 2 * (L * ((x - 2) / x)) := by ring
    _ < (3 * R - 1) * 2 * (nu x (J + 1) * nu x (m - (J + 1))) := by
        apply mul_lt_mul_of_pos_left hprod; linarith
    _ ≤ (3 * R - 1) * slack x m y := by nlinarith

end ICGEqualParity
