import Research.TaskE.C0PairBudget
import Research.TaskE.FGain

set_option autoImplicit false
noncomputable section
namespace CodexPaper1.TaskE.FCProof
open Finset BackfillPaper1.Challenge

lemma matched_row_gain {P y L x : ℝ} (hP : 0 ≤ P) (hL : 0 ≤ L)
    (hx0 : -1 ≤ x) (hx1 : x ≤ 1) :
    2 * y * max 0 (2 * L - 2 * |L * (1 + x)|) -
      hcell P y (L * (1 + x)) (L * (1 - x)) = 2 * (P - y) * L * (1 - |x|) := by
  have hA : 0 ≤ L * (1 + x) := mul_nonneg hL (by linarith)
  have hB : 0 ≤ L * (1 - x) := mul_nonneg hL (by linarith)
  rw [abs_of_nonneg hA]
  by_cases hx : 0 ≤ x
  · have hBA : L * (1 - x) ≤ L * (1 + x) := by nlinarith [mul_nonneg hL hx]
    rw [hcell_same_large hP hB hBA, abs_of_nonneg hx, max_eq_left (by nlinarith [mul_nonneg hL hx])]
    ring
  · have hx' : x ≤ 0 := by linarith
    have hAB : L * (1 + x) ≤ L * (1 - x) := by nlinarith [mul_nonpos_of_nonneg_of_nonpos hL hx']
    rw [hcell_same_small hP hA hAB, abs_of_nonpos hx', max_eq_right (by nlinarith [mul_nonpos_of_nonneg_of_nonpos hL hx'])]
    ring

lemma pair_match_gain {a j : ℕ} (ha : 1 ≤ a) (hj : j < a) {q y : ℝ}
    (hq : 5 ≤ q) (hy0 : 0 ≤ y) (hy1 : y ≤ 1) {c g : ℕ → ℝ}
    (hc : IsSignVec a c) (hg : IsSignVec a g) (he : c j = g j)
    (htail : ∀ l, j < l → l ≤ a → c l = -g l) :
    ((q - 1) * (1 + y) - 4 * y) * DeltaC a 3 c +
      2 * (q - 1 - y) * (3 ^ (a - 1) * (3 - 1)) * (1 - |z 3 a g (j : ℤ)|) ≤
      psi a 3 q y c g := by
  let L : ℝ := 3 ^ (a - 1) * (3 - 1)
  let x : ℝ := c j * z 3 a g (j : ℤ)
  have hL : 0 < L := by dsimp [L]; positivity
  have hsg := hc j hj.le
  have hε : -c j = 1 ∨ -c j = -1 := by rcases hsg with h | h <;> simp [h]
  have hεabs : |-c j| = 1 := by rcases hε with h | h <;> norm_num [h]
  have hxabs : |x| = |z 3 a g (j : ℤ)| := by
    dsimp [x]
    rw [abs_mul, show |c j| = 1 by rcases hsg with h | h <;> norm_num [h], one_mul]
  have hx1 : x ≤ 1 := by
    have hh := (SProof.path_bounds ha hj (by norm_num : (3 : ℝ) ≤ 3) hg).2.2
    rw [← hxabs] at hh
    exact (le_abs_self x).trans hh
  have hx0 : -1 ≤ x := by
    have hh := (SProof.path_bounds ha hj (by norm_num : (3 : ℝ) ≤ 3) hg).2.2
    rw [← hxabs] at hh
    linarith [neg_abs_le x]
  have hz := opposite_tail_z hj htail
  have hA : tMulVec a 3 c (a - 1 - j) = (-c j) * (L * (1 + x)) := by
    rw [SProof.row_path ha hj (by norm_num : (3 : ℝ) ≤ 3) c, hz]
    rcases hsg with h | h <;> dsimp [L, x] <;> rw [h] <;> ring
  have hB : tMulVec a 3 g (a - 1 - j) = (-c j) * (L * (1 - x)) := by
    rw [SProof.row_path ha hj (by norm_num : (3 : ℝ) ≤ 3) g, ← he]
    rcases hsg with h | h <;> dsimp [L, x] <;> rw [h] <;> ring
  have hrow := SProof.row_abs_mass a ha 3 (by norm_num) (a - 1 - j) (by omega)
  rw [ite_eq_right (by omega : a - 1 - j ≠ a)] at hrow
  have hrow' : rowAbsSum a 3 (a - 1 - j) = 2 * L := by
    rw [hrow]
    dsimp [L]
    ring
  have hgain : 2 * y * max 0 (rowAbsSum a 3 (a - 1 - j) -
        2 * |tMulVec a 3 c (a - 1 - j)|) -
      hcell (q - 1) y (tMulVec a 3 c (a - 1 - j)) (tMulVec a 3 g (a - 1 - j)) =
      2 * (q - 1 - y) * L * (1 - |z 3 a g (j : ℤ)|) := by
    rw [hrow', hA, hB, hcell_sign _ _ _ _ _ hε, abs_mul, hεabs, one_mul]
    change 2 * y * max 0 (2 * L - 2 * |L * (1 + x)|) -
      hcell (q - 1) y (L * (1 + x)) (L * (1 - x)) = _
    rw [matched_row_gain (by linarith) hL.le hx0 hx1, hxabs]
  have hζ : ∀ l ≤ a, |g l| ≤ 1 := by
    intro l hl
    rcases hg l hl with h | h <;> norm_num [h]
  have hh := psi_row_gain ha (i := a - 1 - j) (by omega) hq hy0 hy1 hc hζ
  rw [hgain] at hh
  exact hh

end CodexPaper1.TaskE.FCProof
#print axioms CodexPaper1.TaskE.FCProof.pair_match_gain
