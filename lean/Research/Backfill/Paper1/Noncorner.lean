import Research.Backfill.Paper1.Additional

/-!
# Paper 1: full non-corner equality case (Lemma 19)

The target is the complete frozen Challenge.Lemma19, SHA-256
88900a3e49be210812de76aed47d0c6baa2534159f0389fe7b68d2fdc1f5d9a2.
Acceptance evidence is recorded separately by check_noncorner_graph.py.

The essential extra step beyond noncorner_le is strict positivity of the
zero-start potential defect at every repeated adjacent sign. In particular,
the proof does not infer the equality case from the non-strict bound alone.
-/

set_option autoImplicit false

noncomputable section

namespace CodexPaper1

open BackfillPaper1 Finset
open Additional

namespace Noncorner

def length (x : ℝ) (m : ℕ) (y : ℕ → ℝ) : ℝ :=
  ∑ k ∈ range m, |ICGGeneral.Zp x m y k - ICGGeneral.Zp x m y (k + 1)|

def defect (x : ℝ) (m : ℕ) (y : ℕ → ℝ) : ℝ := by
  classical
  exact ∑ k ∈ range m,
    if y k = y (k + 1) then
      2 * ICGEqualParity.nuc x 0 (k + 1) * |ICGGeneral.Zp x m y (k + 1)|
    else 0

lemma nuc_zero_succ_pos {x : ℝ} (hx : 2 < x) (k : ℕ) :
    0 < ICGEqualParity.nuc x 0 (k + 1) := by
  rw [ICGEqualParity.nuc_succ]
  apply div_pos
  · linarith [(ICGEqualParity.nuc_zero_bounds hx k).2]
  · linarith

lemma defect_nonneg {x : ℝ} (hx : 2 < x) (m : ℕ) (y : ℕ → ℝ) :
    0 ≤ defect x m y := by
  classical
  unfold defect
  apply Finset.sum_nonneg
  intro k _
  split_ifs
  · exact mul_nonneg (mul_nonneg (by norm_num) (nuc_zero_succ_pos hx k).le)
      (abs_nonneg _)
  · exact le_rfl

lemma defect_pos_of_repeat {x : ℝ} (hx : 2 < x) {m : ℕ} {y : ℕ → ℝ}
    (hy : ICGGeneral.IsSign m y) {k : ℕ} (hk : k < m)
    (he : y k = y (k + 1)) : 0 < defect x m y := by
  classical
  unfold defect
  apply Finset.sum_pos'
  · intro j _
    split_ifs
    · exact mul_nonneg (mul_nonneg (by norm_num) (nuc_zero_succ_pos hx j).le)
        (abs_nonneg _)
    · exact le_rfl
  · refine ⟨k, Finset.mem_range.mpr hk, ?_⟩
    rw [ite_eq_left he]
    have hx0 : 0 < x := by linarith
    have hZ : 0 < |ICGGeneral.Zp x m y (k + 1)| := by
      rw [ICGGeneral.Zp_abs_eq hx.le hy hk]
      exact lt_of_lt_of_le (div_pos (by linarith) hx0)
        (ICGGeneral.Zp_sign hx.le hy (k + 1) hk)
    exact mul_pos (mul_pos (by norm_num) (nuc_zero_succ_pos hx k)) hZ

lemma sgnv_ne_succ (k : ℕ) : ICGGeneral.sgnv k ≠ ICGGeneral.sgnv (k + 1) := by
  rw [ICGGeneral.sgnv_succ]
  intro h
  have hn : ICGGeneral.sgnv k ≠ 0 := by simp [ICGGeneral.sgnv]
  exact hn (by linarith)

lemma defect_eq_zero_of_alternating (x : ℝ) (m : ℕ) (y : ℕ → ℝ)
    (halt : ∀ k < m, y k ≠ y (k + 1)) : defect x m y = 0 := by
  classical
  unfold defect
  apply Finset.sum_eq_zero
  intro k hk
  exact ite_eq_right (halt k (Finset.mem_range.mp hk))

lemma defect_sgnv (x : ℝ) (m : ℕ) : defect x m ICGGeneral.sgnv = 0 :=
  defect_eq_zero_of_alternating x m ICGGeneral.sgnv (fun k _ => sgnv_ne_succ k)

lemma length_gap {x : ℝ} (hx : 2 < x) {m : ℕ} {y : ℕ → ℝ}
    (hy : ICGGeneral.IsSign m y) :
    length x m y = length x m ICGGeneral.sgnv - defect x m y := by
  have hs := defect_sgnv x m
  unfold defect at hs
  unfold length defect
  rw [ICGEqualParity.noncorner_eq hx hy,
    ICGEqualParity.noncorner_eq hx (ICGGeneral.sgnv_isSign m), hs]
  ring

lemma length_le {x : ℝ} (hx : 2 < x) {m : ℕ} {y : ℕ → ℝ}
    (hy : ICGGeneral.IsSign m y) : length x m y ≤ length x m ICGGeneral.sgnv := by
  rw [length_gap hx hy]
  exact sub_le_self _ (defect_nonneg hx m y)

/-- Equality holds exactly for the two alternating vectors on the finite range. -/
lemma length_eq_iff {x : ℝ} (hx : 2 < x) {m : ℕ} {y : ℕ → ℝ}
    (hy : ICGGeneral.IsSign m y) :
    length x m y = length x m ICGGeneral.sgnv ↔ Challenge.IsPmAlt m y := by
  constructor
  · intro heq
    have halt : ∀ k < m, y k ≠ y (k + 1) := by
      intro k hk he
      have hp := defect_pos_of_repeat hx hy hk he
      rw [length_gap hx hy] at heq
      linarith
    exact ICGGeneral.alternating_eq hy halt
  · intro hpm
    have halt : ∀ k < m, y k ≠ y (k + 1) := by
      rcases hpm with h | h
      · intro k hk he
        change (∀ i ≤ m, y i = ICGGeneral.sgnv i) at h
        rw [h k hk.le, h (k + 1) hk] at he
        exact sgnv_ne_succ k he
      · intro k hk he
        change (∀ i ≤ m, y i = -ICGGeneral.sgnv i) at h
        rw [h k hk.le, h (k + 1) hk] at he
        exact sgnv_ne_succ k (neg_injective he)
    rw [length_gap hx hy, defect_eq_zero_of_alternating x m y halt, sub_zero]

/-- The integer endpoint j = -1 is the path coordinate Zp 0. -/
lemma z_neg_one_eq_Zp_zero {x : ℝ} (hx : x ≠ 0) (m : ℕ) (w : ℕ → ℝ) :
    Challenge.z x m w (-1) = ICGGeneral.Zp x m w 0 := by
  have hidx : ((m : ℤ) - 1 - (-1)).toNat = m := by omega
  rw [Challenge.z, hidx, zRev_eq_Zp hx m w m le_rfl, Nat.sub_self]

lemma normalized_noncorner {x : ℝ} (hx : 0 < x) (m : ℕ) (w : ℕ → ℝ) :
    Challenge.l1 m (Challenge.tMulVec m x w) / x ^ m - |Challenge.z x m w (-1)| =
      length x m w := by
  rw [l1_tMulVec_eq_L1, z_neg_one_eq_Zp_zero hx.ne', ICGGeneral.L1_path hx,
    mul_div_cancel_left₀ _ (pow_pos hx m).ne']
  unfold length
  ring

lemma normalized_sgnv {x : ℝ} (hx : 2 < x) (m : ℕ) :
    Challenge.dNorm m x / x ^ m - Challenge.mu x ((m : ℤ) - 1) =
      length x m ICGGeneral.sgnv := by
  have hx0 : 0 < x := by linarith
  rw [dNorm_eq_L1, mu_pred_eq_nu, ICGGeneral.L1_path hx0,
    ICGEqualParity.Zp_sgnv_zero hx, abs_of_pos (ICGGeneral.nu_pos hx m),
    mul_div_cancel_left₀ _ (pow_pos hx0 m).ne']
  unfold length
  ring

end Noncorner

/-- The complete frozen statement, including both directions of equality. -/
theorem check_Lemma19 : Challenge.Lemma19 := by
  intro x hx m _hm y hy
  dsimp only
  have hx0 : 0 < x := by linarith
  rw [Noncorner.normalized_noncorner hx0, Noncorner.normalized_sgnv hx]
  exact ⟨Noncorner.length_le hx hy, Noncorner.length_eq_iff hx hy⟩

#print axioms check_Lemma19

end CodexPaper1
