import Research.TaskE.C0AltTail

set_option autoImplicit false
noncomputable section
namespace CodexPaper1.TaskE.FCProof
open Finset BackfillPaper1.Challenge

lemma alt_terminal_cell_neg {a : ℕ} (ha : 3 ≤ a) {q y : ℝ} (hq : 5 ≤ q)
    (_hy0 : 0 ≤ y) (hy1 : y ≤ 1) {g : ℕ → ℝ} (hg : IsSignVec a g) (hg0 : g 0 = 1) :
    hcell (q - 1) y (tMulVec a 3 sAlt a) (tMulVec a 3 g a) < 0 := by
  have ha1 : 1 ≤ a := by omega
  have hzs : 0 < z 3 a sAlt (-1) := by
    have hh := (CodexPaper1.check_Lemma8 3 (by norm_num) a ha1 sAlt (alt_sign a)).1 0 (by omega)
    simpa [sAlt] using hh.1
  have hzg : 0 < z 3 a g (-1) := by
    have hh := (CodexPaper1.check_Lemma8 3 (by norm_num) a ha1 g hg).1 0 (by omega)
    simpa only [hg0, one_mul, Nat.cast_zero, zero_sub] using hh.1
  have hMs := (CodexPaper1.check_PathCoordinates 3 (by norm_num) a ha1 sAlt).1
  have hMg := (CodexPaper1.check_PathCoordinates 3 (by norm_num) a ha1 g).1
  have hA : 0 < tMulVec a 3 sAlt a := by rw [hMs]; positivity
  have hB : 0 < tMulVec a 3 g a := by rw [hMg]; positivity
  have hAlow := SProof.terminal_lower ha1 (by norm_num : (3 : ℝ) ≤ 3) (alt_sign a)
  rw [abs_of_pos hA] at hAlow
  norm_num at hAlow
  have hζ : ∀ i ≤ a, |g i| ≤ 1 := by intro i hi; rcases hg i hi with h | h <;> norm_num [h]
  have hBup := CodexPaper1.Prop31.tMulVec_abs_le_rowAbs a 3 g hζ a
  have hrow := SProof.row_abs_mass a ha1 3 (by norm_num) a le_rfl
  rw [ite_eq_left rfl] at hrow
  rw [abs_of_pos hB, hrow] at hBup
  have hpow : (3 : ℝ) ^ a = 3 ^ (a - 1) * 3 := by rw [← pow_succ, Nat.sub_add_cancel ha1]
  have hPA := mul_le_mul_of_nonneg_left hAlow (show 0 ≤ q - 1 by linarith)
  have hbonus := mul_pos (show 0 < q - 4 by linarith) (show 0 < (3 : ℝ) ^ (a - 1) by positivity)
  have hdom : tMulVec a 3 g a < (q - 1) * tMulVec a 3 sAlt a := by nlinarith
  by_cases hBA : tMulVec a 3 g a ≤ tMulVec a 3 sAlt a
  · rw [hcell_same_large (by linarith) hB.le hBA]
    have hp := mul_pos (show 0 < q - 1 - y by linarith) hB
    nlinarith
  · rw [hcell_same_small (by linarith) hA.le (by linarith)]
    have hm := mul_le_mul_of_nonneg_right hy1 hB.le
    nlinarith

lemma alt_psi_two_rows {a i : ℕ} (ha : 3 ≤ a) (hi : i < a) {q y : ℝ}
    (hq : 5 ≤ q) (hy0 : 0 ≤ y) (hy1 : y ≤ 1) {g : ℕ → ℝ} (hg : IsSignVec a g) :
    -hcell (q - 1) y (tMulVec a 3 sAlt i) (tMulVec a 3 g i) -
      hcell (q - 1) y (tMulVec a 3 sAlt a) (tMulVec a 3 g a) ≤ psi a 3 q y sAlt g := by
  classical
  have hζ : ∀ l ≤ a, |g l| ≤ 1 := by intro l hl; rcases hg l hl with h | h <;> norm_num [h]
  have hc := ((CodexPaper1.check_Lemma22 a (by omega) 3 q (Or.inr ⟨rfl, hq⟩) y hy0 hy1
    sAlt g (alt_sign a) hζ).2 (Or.inl (by intros; rfl))).1
  let f : ℕ → ℝ := fun l => -hcell (q - 1) y (tMulVec a 3 sAlt l) (tMulVec a 3 g l)
  have hsubset : ({i, a} : Finset ℕ) ⊆ range (a + 1) := by
    intro l hl
    rcases mem_insert.mp hl with h | h
    · subst l; exact mem_range.mpr (by omega)
    · have he := mem_singleton.mp h; subst l; exact mem_range.mpr (by omega)
  have hs := sum_le_sum_of_subset_of_nonneg hsubset
    (fun l hl _hl' => neg_nonneg.mpr (hc l (by have hh := mem_range.mp hl; omega)))
  simp only [sum_insert, mem_singleton, show i ≠ a by omega, not_false_eq_true, sum_singleton] at hs
  change f i + f a ≤ ∑ l ∈ range (a + 1), f l at hs
  dsimp [f] at hs
  rw [sum_neg_distrib] at hs
  unfold psi
  rw [CodexPaper1.OneColumn.delta_pmAlt (p := (3 : ℝ)) (Or.inl (by intros; rfl)), mul_zero, zero_sub]
  linarith

lemma c0_alt_tail_zero {a : ℕ} (ha : 3 ≤ a) {q y : ℝ} (hq : 5 ≤ q)
    (hy0 : 0 ≤ y) (hy1 : y ≤ 1) {g : ℕ → ℝ} (hg : IsSignVec a g) (he : g 0 = sAlt 0)
    (htail : ∀ l, 0 < l → l ≤ a → g l = -sAlt l) :
    psi a 3 q y sAlt g > (q - 1 - y) * (2 * deltaK a 3 - DeltaC a 3 g) := by
  have hj : (0 : ℕ) ≤ a - 2 := by omega
  obtain ⟨hv0, hv1, _hd, hG, hA⟩ := alt_tail_geometry ha hj hg he htail
  simp only [Nat.sub_zero, Nat.cast_zero] at hA hG
  let L : ℝ := 3 ^ (a - 1) * (3 - 1)
  let v : ℝ := |z 3 a sAlt (0 : ℤ)|
  have hL : 0 < L := by dsimp [L]; positivity
  change v ≤ (5 / 9 : ℝ) at hv1
  have hε : -sAlt 0 = 1 ∨ -sAlt 0 = -1 := by norm_num [sAlt]
  have hh : hcell (q - 1) y (tMulVec a 3 sAlt (a - 1)) (tMulVec a 3 g (a - 1)) =
      -2 * (q - 1 - y) * L * (1 - v) := by
    rw [hA, hG, hcell_sign _ _ _ _ _ hε]
    have hB0 : 0 ≤ L * (1 - v) := mul_nonneg hL.le (by linarith)
    have hBA : L * (1 - v) ≤ L * (1 + v) := by
      have hv : 0 ≤ v := abs_nonneg _
      nlinarith [mul_nonneg hL.le hv]
    rw [hcell_same_large (by linarith) hB0 hBA]
    ring
  have ht := alt_terminal_cell_neg ha hq hy0 hy1 hg (by simpa only [sAlt, pow_zero] using he)
  have hp := alt_psi_two_rows ha (i := a - 1) (by omega) hq hy0 hy1 hg
  rw [hh] at hp
  have hψ : 2 * (q - 1 - y) * L * (1 - v) < psi a 3 q y sAlt g := by linarith
  have hz : |z 3 a g (0 : ℤ)| = v := by
    dsimp [v]
    have hz0 := congrArg abs (negative_tail_z (by omega : (0 : ℕ) < a) htail)
    simpa only [Nat.cast_zero, abs_neg] using hz0
  have hb := zero_tail_budget a (by omega) g hg 0 (by omega)
  simp only [Nat.cast_zero] at hb
  rw [alt_tail_NA_empty htail, sum_empty, mul_zero, add_zero, hz] at hb
  have hd := deficit_pays_term (by omega : 1 ≤ a) hg (alt_tail_match_repeat (by omega) he htail)
  simp only [Nat.cast_zero] at hd
  rw [hz] at hd
  have hγ : 2 * deltaK a 3 - DeltaC a 3 g ≤ 2 * L * (1 - v) := by
    change _ ≤ _ + 2 * L * (1 - v) at hb
    linarith
  have hR := mul_le_mul_of_nonneg_left hγ (show 0 ≤ q - 1 - y by linarith)
  nlinarith

end CodexPaper1.TaskE.FCProof
#print axioms CodexPaper1.TaskE.FCProof.c0_alt_tail_zero
#print axioms CodexPaper1.TaskE.FCProof.alt_terminal_cell_neg
