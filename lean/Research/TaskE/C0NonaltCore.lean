import Research.TaskE.C0PairGain
import Research.TaskE.FDeltaRatio
import Research.TaskE.PotentialLower

set_option autoImplicit false
noncomputable section
namespace CodexPaper1.TaskE.FCProof
open Finset BackfillPaper1.Challenge

lemma different_signs {a i : ℕ} {c g : ℕ → ℝ} (hc : IsSignVec a c) (hg : IsSignVec a g)
    (hi : i ≤ a) (hne : c i ≠ g i) : c i = -g i := by
  rcases hc i hi with h | h <;> rcases hg i hi with h' | h' <;> simp_all

lemma c0_nonalt_match {a j : ℕ} (ha : 3 ≤ a) (hj : j < a) {q y : ℝ}
    (hq : 5 ≤ q) (hy0 : 0 < y) (hy1 : y ≤ 1) {c g : ℕ → ℝ}
    (hc : IsSignVec a c) (hg : IsSignVec a g) (hcna : ¬ IsPmAlt a c)
    (he : c j = g j) (htail : ∀ l, j < l → l ≤ a → c l = -g l) :
    psi a 3 q y c g > (q - 1 - y) * (2 * deltaK a 3 - DeltaC a 3 g) := by
  have hb := pair_match_budget (by omega : 1 ≤ a) hj hc hg he htail
  have hp := pair_match_gain (by omega : 1 ≤ a) hj hq hy0.le hy1 hc hg he htail
  have hd := SProof.deficit_pos (a := a) (p := (3 : ℝ)) (by omega) (by norm_num) hc hcna
  have hR : 0 ≤ q - 1 - y := by linarith
  have hm := mul_le_mul_of_nonneg_left hb hR
  have hx := mul_pos hy0 (show 0 < q - 4 by linarith)
  have hcoef : 0 < ((q - 1) * (1 + y) - 4 * y) - (q - 1 - y) := by nlinarith
  have hs := mul_pos hcoef hd
  nlinarith

lemma c0_nonalt_sum_high {a : ℕ} (ha : 3 ≤ a) {q y : ℝ}
    (hq : 5 ≤ q) (hy0 : 0 < y) (hy1 : y ≤ 1) {c g : ℕ → ℝ}
    (hc : IsSignVec a c) (hg : IsSignVec a g) (hcna : ¬ IsPmAlt a c)
    (hsum : 2 * deltaK a 3 ≤ DeltaC a 3 c + DeltaC a 3 g) :
    psi a 3 q y c g > (q - 1 - y) * (2 * deltaK a 3 - DeltaC a 3 g) := by
  have hζ : ∀ i ≤ a, |g i| ≤ 1 := by intro i hi; rcases hg i hi with h | h <;> norm_num [h]
  have hp := potential_lower a (by omega) q y hq hy0.le hy1 c g hc hζ
  have hd := SProof.deficit_pos (a := a) (p := (3 : ℝ)) (by omega) (by norm_num) hc hcna
  have hm := mul_le_mul_of_nonneg_left hsum (show 0 ≤ q - 1 - y by linarith)
  have hs := mul_pos hy0 hd
  nlinarith

lemma common_last_pair_gain {a : ℕ} (ha : 3 ≤ a) {q y : ℝ}
    (hq : 5 ≤ q) (hy0 : 0 ≤ y) (hy1 : y ≤ 1) {c g : ℕ → ℝ}
    (hc : IsSignVec a c) (hg : IsSignVec a g) (he : c a = g a)
    (hcprev : c (a - 1) = -c a) (hgprev : g (a - 1) = -g a) :
    4 * (q - 1 - y) * (3 ^ (a - 1) * (3 - 1)) ≤ psi a 3 q y c g := by
  have ha1 : 1 ≤ a := by omega
  have hj : a - 1 < a := by omega
  have hi : a - 1 - (a - 1) = 0 := by omega
  let L : ℝ := 3 ^ (a - 1) * (3 - 1)
  have hL : 0 < L := by dsimp [L]; positivity
  have hA : tMulVec a 3 c 0 = c a * (2 * L) := by
    have hh := SProof.row_path ha1 hj (by norm_num : (3 : ℝ) ≤ 3) c
    rw [hi, z_end ha1 c, hcprev] at hh
    rw [hh]; dsimp [L]; ring
  have hB : tMulVec a 3 g 0 = c a * (2 * L) := by
    have hh := SProof.row_path ha1 hj (by norm_num : (3 : ℝ) ≤ 3) g
    rw [hi, z_end ha1 g, hgprev, ← he] at hh
    rw [hh]; dsimp [L]; ring
  have hε := hc a le_rfl
  have hAbs : |tMulVec a 3 c 0| = 2 * L := by
    rw [hA, abs_mul, show |c a| = 1 by rcases hε with h | h <;> norm_num [h], one_mul,
      abs_of_pos (by positivity : 0 < 2 * L)]
  have hh : hcell (q - 1) y (tMulVec a 3 c 0) (tMulVec a 3 g 0) = -4 * (q - 1 - y) * L := by
    rw [hA, hB, hcell_sign _ _ _ _ _ hε, hcell_same_large (by linarith) (by positivity : 0 ≤ 2 * L) le_rfl]
    ring
  have hrow := SProof.row_abs_mass a ha1 3 (by norm_num) 0 (by omega)
  rw [ite_eq_right (by omega : (0 : ℕ) ≠ a)] at hrow
  have hpen : max 0 (rowAbsSum a 3 0 - 2 * |tMulVec a 3 c 0|) = 0 := by
    rw [hrow, hAbs]
    apply max_eq_left
    dsimp [L]; nlinarith
  have hζ : ∀ i ≤ a, |g i| ≤ 1 := by intro i hi; rcases hg i hi with h | h <;> norm_num [h]
  have hp := psi_row_gain ha1 (i := 0) (by omega) hq hy0 hy1 hc hζ
  rw [hpen, hh] at hp
  have hd := CodexPaper1.Prop31.delta_nonneg (p := (3 : ℝ)) (by norm_num) hc
  have hK : 0 ≤ (q - 1) * (1 + y) - 4 * y := by
    nlinarith [mul_nonneg (show 0 ≤ q - 5 by linarith) hy0]
  have hm := mul_nonneg hK hd
  change 4 * (q - 1 - y) * L ≤ _
  nlinarith

lemma c0_common_last_pair {a : ℕ} (ha : 3 ≤ a) {q y : ℝ}
    (hq : 5 ≤ q) (hy0 : 0 ≤ y) (hy1 : y ≤ 1) {c g : ℕ → ℝ}
    (hc : IsSignVec a c) (hg : IsSignVec a g) (he : c a = g a)
    (hcprev : c (a - 1) = -c a) (hgprev : g (a - 1) = -g a) :
    psi a 3 q y c g > (q - 1 - y) * (2 * deltaK a 3 - DeltaC a 3 g) := by
  have hp := common_last_pair_gain ha hq hy0 hy1 hc hg he hcprev hgprev
  have hd := CodexPaper1.Prop31.delta_nonneg (p := (3 : ℝ)) (by norm_num) hg
  have hδ := delta_ratio a ha
  have hR : 0 < q - 1 - y := by linarith
  have hL : 0 < (3 : ℝ) ^ (a - 1) * (3 - 1) := by positivity
  have hm := mul_le_mul_of_nonneg_left hδ hR.le
  have hs := mul_pos hR hL
  have hD := mul_nonneg hR.le hd
  nlinarith

lemma c0_nonalt {a : ℕ} (ha : 3 ≤ a) {q y : ℝ} (hq : 5 ≤ q)
    (hy0 : 0 < y) (hy1 : y ≤ 1) {c g : ℕ → ℝ}
    (hc : IsSignVec a c) (hg : IsSignVec a g) (hcna : ¬ IsPmAlt a c)
    (hna : ¬ (∀ i ≤ a, c i = -g i)) :
    psi a 3 q y c g > (q - 1 - y) * (2 * deltaK a 3 - DeltaC a 3 g) := by
  classical
  by_cases hsum : 2 * deltaK a 3 ≤ DeltaC a 3 c + DeltaC a 3 g
  · exact c0_nonalt_sum_high ha hq hy0 hy1 hc hg hcna hsum
  have hdc := CodexPaper1.Prop31.delta_nonneg (p := (3 : ℝ)) (by norm_num) hc
  have hdg := CodexPaper1.Prop31.delta_nonneg (p := (3 : ℝ)) (by norm_num) hg
  have hcprev : c (a - 1) = -c a := by
    by_cases he : c (a - 1) = c a
    · have hh := terminal_repeat_high (by omega : 1 ≤ a) hc he
      exfalso; linarith
    · rcases hc (a - 1) (by omega) with h | h <;> rcases hc a le_rfl with h' | h' <;> simp_all
  have hgprev : g (a - 1) = -g a := by
    by_cases he : g (a - 1) = g a
    · have hh := terminal_repeat_high (by omega : 1 ≤ a) hg he
      exfalso; linarith
    · rcases hg (a - 1) (by omega) with h | h <;> rcases hg a le_rfl with h' | h' <;> simp_all
  by_cases he : c a = g a
  · exact c0_common_last_pair ha hq hy0.le hy1 hc hg he hcprev hgprev
  have hne : ((range (a + 1)).filter (fun i => c i = g i)).Nonempty := by
    by_contra hn
    apply hna
    intro i hi
    apply different_signs hc hg hi
    intro hh
    exact hn ⟨i, mem_filter.mpr ⟨mem_range.mpr (by omega), hh⟩⟩
  let S := (range (a + 1)).filter (fun i => c i = g i)
  let J := S.max' hne
  have hJ : J ∈ S := max'_mem _ _
  have hJa : J ≤ a := by have hh := mem_range.mp (mem_filter.mp hJ).1; omega
  have hJmatch : c J = g J := (mem_filter.mp hJ).2
  have hJlt : J < a := by
    by_contra hn
    have hEq : J = a := by omega
    apply he
    simpa only [hEq] using hJmatch
  have htail : ∀ l, J < l → l ≤ a → c l = -g l := by
    intro l hl hla
    apply different_signs hc hg hla
    intro hh
    have hlS : l ∈ S := mem_filter.mpr ⟨mem_range.mpr (by omega), hh⟩
    have hle := le_max' S l hlS
    change l ≤ J at hle
    omega
  exact c0_nonalt_match ha hJlt hq hy0 hy1 hc hg hcna hJmatch htail

end CodexPaper1.TaskE.FCProof
#print axioms CodexPaper1.TaskE.FCProof.c0_nonalt
#print axioms CodexPaper1.TaskE.FCProof.c0_common_last_pair
