import Research.TaskE.C0TailBudget
import Research.TaskE.C1AltBasis

set_option autoImplicit false
noncomputable section
namespace CodexPaper1.TaskE.FCProof
open Finset BackfillPaper1.Challenge

lemma zero_tail_budget_strict {a j : ℕ} (ha : 1 ≤ a) (hj : j < a) (hj1 : 1 ≤ j)
    {g : ℕ → ℝ} (hg : IsSignVec a g) (hv : |z 3 a g (j : ℤ)| < 1) :
    2 * deltaK a 3 <
      2 * (3 : ℝ) ^ a * (mu 3 (j : ℤ) * |z 3 a g (j : ℤ)| +
        2 * ∑ l ∈ (NA a g).filter (fun l => j < l), mu 3 (l : ℤ) * |z 3 a g (l : ℤ)|) +
      2 * (3 ^ (a - 1) * (3 - 1)) * (1 - |z 3 a g (j : ℤ)|) := by
  have hb := potential_tail_budget hg (a - (j + 1)) (j + 1) (by omega)
  rw [potential_tail_sum hj, ← CodexPaper1.Additional.mu_nat_eq_nu 3 j,
    ← CodexPaper1.Additional.z_nat_eq_Zp (by norm_num) a g j hj] at hb
  have hm := mu_three_positive_index hj1
  have hmul := mul_pos (show 0 < mu 3 (j : ℤ) - 1 / 3 by linarith)
    (show 0 < 1 - |z 3 a g (j : ℤ)| by linarith)
  have hp := mul_le_mul_of_nonneg_left hb (show 0 ≤ 2 * (3 : ℝ) ^ a by positivity)
  have hweighted := CodexPaper1.ClosedForms.weighted_nu_eq_deltaK (x := (3 : ℝ)) (by norm_num) a
  have hscale := length_scale ha
  have he := mul_pos (show 0 < 2 * (3 : ℝ) ^ a by positivity) hmul
  nlinarith

lemma alt_tail_NA_empty {a j : ℕ} {g : ℕ → ℝ}
    (htail : ∀ l, j < l → l ≤ a → g l = -sAlt l) :
    (NA a g).filter (fun l => j < l) = ∅ := by
  classical
  ext l
  constructor
  · intro hl
    exfalso
    have hla : l < a := mem_range.mp (mem_filter.mp (mem_filter.mp hl).1).1
    have hjl : j < l := (mem_filter.mp hl).2
    have hrep := (mem_filter.mp (mem_filter.mp hl).1).2
    rw [htail l hjl hla.le, htail (l + 1) (by omega) (by omega), alt_succ, neg_neg] at hrep
    rcases neg_one_pow_eq_or ℝ l with hs | hs <;> change sAlt l = _ at hs <;> rw [hs] at hrep <;> linarith
  · intro hl
    simp at hl

lemma alt_tail_match_repeat {a j : ℕ} (hj : j < a) {g : ℕ → ℝ} (he : g j = sAlt j)
    (htail : ∀ l, j < l → l ≤ a → g l = -sAlt l) : j ∈ NA a g := by
  apply mem_filter.mpr
  refine ⟨mem_range.mpr hj, ?_⟩
  rw [he, htail (j + 1) (by omega) (by omega), alt_succ, neg_neg]

lemma c0_alt_tail_strict {a j : ℕ} (ha : 3 ≤ a) (hj : j ≤ a - 2) (hj1 : 1 ≤ j)
    {q y : ℝ} (hq : 5 ≤ q) (hy0 : 0 ≤ y) (hy1 : y ≤ 1)
    {g : ℕ → ℝ} (hg : IsSignVec a g) (he : g j = sAlt j)
    (htail : ∀ l, j < l → l ≤ a → g l = -sAlt l) :
    psi a 3 q y sAlt g > (q - 1 - y) * (2 * deltaK a 3 - DeltaC a 3 g) := by
  have hja : j < a := by omega
  obtain ⟨hv0, hv1, _hd, hp⟩ := alt_tail_gain ha hj hq hy0 hy1
    (m := 1) (by norm_num) (by norm_num) hg he htail
  have hzabs : |z 3 a g (j : ℤ)| = |z 3 a sAlt (j : ℤ)| := by rw [negative_tail_z hja htail, abs_neg]
  have hv : |z 3 a g (j : ℤ)| < 1 := by rw [hzabs]; linarith
  have hb := zero_tail_budget_strict (by omega : 1 ≤ a) hja hj1 hg hv
  rw [alt_tail_NA_empty htail, sum_empty, mul_zero, add_zero] at hb
  have hd := deficit_pays_term (by omega : 1 ≤ a) hg (alt_tail_match_repeat hja he htail)
  have hR : 0 < q - 1 - y := by linarith
  have hγ : 2 * deltaK a 3 - DeltaC a 3 g <
      2 * (3 ^ (a - 1) * (3 - 1)) * (1 - |z 3 a sAlt (j : ℤ)|) := by
    rw [hzabs] at hb hd
    linarith
  have hr := mul_lt_mul_of_pos_left hγ hR
  simp only [one_mul, mul_one] at hp
  nlinarith only [hr, hp]

end CodexPaper1.TaskE.FCProof
#print axioms CodexPaper1.TaskE.FCProof.c0_alt_tail_strict
