import Research.TaskE.C0TailBudget

set_option autoImplicit false
noncomputable section
namespace CodexPaper1.TaskE.FCProof
open Finset BackfillPaper1.Challenge

lemma opposite_tail_z {a j : ℕ} (hj : j < a) {c g : ℕ → ℝ}
    (htail : ∀ l, j < l → l ≤ a → c l = -g l) :
    z 3 a c (j : ℤ) = -z 3 a g (j : ℤ) := by
  rw [CodexPaper1.Additional.z_nat_eq_Zp (by norm_num) a c j hj,
    CodexPaper1.Additional.z_nat_eq_Zp (by norm_num) a g j hj]
  unfold ICGGeneral.Zp ICGGeneral.Wp
  rw [← neg_div]
  congr 1
  rw [← sum_neg_distrib]
  apply sum_congr rfl
  intro l hl
  have hmem := mem_Ico.mp hl
  rw [htail l (by omega) (by omega)]
  ring

lemma deficit_tail_at {a j : ℕ} (ha : 1 ≤ a) (hj : j < a)
    {c : ℕ → ℝ} (hc : IsSignVec a c) :
    2 * (3 : ℝ) ^ a * ((if c j = c (j + 1) then
        mu 3 (j : ℤ) * |z 3 a c (j : ℤ)| else 0) +
      ∑ l ∈ (NA a c).filter (fun l => j < l), mu 3 (l : ℤ) * |z 3 a c (l : ℤ)|) ≤ DeltaC a 3 c := by
  classical
  have _ha_use : 0 < a := lt_of_lt_of_le (by norm_num : 0 < 1) ha
  let w : ℕ → ℝ := fun l => mu 3 (l : ℤ) * |z 3 a c (l : ℤ)|
  let T := (NA a c).filter (fun l => j < l)
  have hw (l : ℕ) : 0 ≤ w l := by
    dsimp [w]
    have hm := SProof.mu_lower (p := (3 : ℝ)) (by norm_num) l
    exact mul_nonneg (by norm_num at hm; linarith) (abs_nonneg _)
  rw [SProof.deficit_identity (by norm_num : (3 : ℝ) ≤ 3) hc]
  apply mul_le_mul_of_nonneg_left _ (by positivity : 0 ≤ 2 * (3 : ℝ) ^ a)
  change (if c j = c (j + 1) then w j else 0) + (∑ l ∈ T, w l) ≤ ∑ l ∈ NA a c, w l
  by_cases he : c j = c (j + 1)
  · rw [ite_eq_left he]
    have hsub : insert j T ⊆ NA a c := by
      intro l hl
      rcases mem_insert.mp hl with h | h
      · subst l; exact mem_filter.mpr ⟨mem_range.mpr hj, he⟩
      · exact (mem_filter.mp h).1
    have hs := sum_le_sum_of_subset_of_nonneg hsub (fun l _hl _hl' => hw l)
    have hjT : j ∉ T := by simp [T]
    simpa only [sum_insert hjT] using hs
  · rw [ite_eq_right he, zero_add]
    exact sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun l _hl _hl' => hw l)

lemma opposite_tail_NA {a j : ℕ} {c g : ℕ → ℝ}
    (htail : ∀ l, j < l → l ≤ a → c l = -g l) :
    (NA a c).filter (fun l => j < l) = (NA a g).filter (fun l => j < l) := by
  classical
  ext l
  by_cases hla : l < a
  · by_cases hjl : j < l
    · have h1 := htail l hjl hla.le
      have h2 := htail (l + 1) (by omega) (by omega)
      simp [NA, hla, hjl, h1, h2]
    · simp [NA, hjl]
  · simp [NA, hla]

lemma opposite_tail_deficit_sum {a j : ℕ} {c g : ℕ → ℝ}
    (htail : ∀ l, j < l → l ≤ a → c l = -g l) :
    (∑ l ∈ (NA a c).filter (fun l => j < l), mu 3 (l : ℤ) * |z 3 a c (l : ℤ)|) =
      ∑ l ∈ (NA a g).filter (fun l => j < l), mu 3 (l : ℤ) * |z 3 a g (l : ℤ)| := by
  rw [opposite_tail_NA htail]
  apply sum_congr rfl
  intro l hl
  have hla : l < a := mem_range.mp (mem_filter.mp (mem_filter.mp hl).1).1
  have hjl : j < l := (mem_filter.mp hl).2
  rw [opposite_tail_z hla (fun k hk hka => htail k (by omega) hka), abs_neg]

lemma pair_match_budget {a j : ℕ} (ha : 1 ≤ a) (hj : j < a) {c g : ℕ → ℝ}
    (hc : IsSignVec a c) (hg : IsSignVec a g) (he : c j = g j)
    (htail : ∀ l, j < l → l ≤ a → c l = -g l) :
    2 * deltaK a 3 ≤ DeltaC a 3 c + DeltaC a 3 g +
      2 * (3 ^ (a - 1) * (3 - 1)) * (1 - |z 3 a g (j : ℤ)|) := by
  classical
  have hδc := deficit_tail_at ha hj hc
  have hδg := deficit_tail_at ha hj hg
  rw [opposite_tail_deficit_sum htail] at hδc
  have hz : |z 3 a c (j : ℤ)| = |z 3 a g (j : ℤ)| := by rw [opposite_tail_z hj htail, abs_neg]
  rw [hz] at hδc
  have hcn := htail (j + 1) (by omega) (by omega)
  have hterms :
      (if c j = c (j + 1) then mu 3 (j : ℤ) * |z 3 a g (j : ℤ)| else 0) +
      (if g j = g (j + 1) then mu 3 (j : ℤ) * |z 3 a g (j : ℤ)| else 0) =
      mu 3 (j : ℤ) * |z 3 a g (j : ℤ)| := by
    rw [he, hcn]
    rcases hg j hj.le with h | h <;> rcases hg (j + 1) (by omega) with h' | h' <;> norm_num [h, h']
  have hb := zero_tail_budget a ha g hg j hj
  calc
    _ ≤ _ := hb
    _ = (2 * (3 : ℝ) ^ a * ((if c j = c (j + 1) then
          mu 3 (j : ℤ) * |z 3 a g (j : ℤ)| else 0) +
        ∑ l ∈ (NA a g).filter (fun l => j < l), mu 3 (l : ℤ) * |z 3 a g (l : ℤ)|)) +
      (2 * (3 : ℝ) ^ a * ((if g j = g (j + 1) then
          mu 3 (j : ℤ) * |z 3 a g (j : ℤ)| else 0) +
        ∑ l ∈ (NA a g).filter (fun l => j < l), mu 3 (l : ℤ) * |z 3 a g (l : ℤ)|)) +
        2 * (3 ^ (a - 1) * (3 - 1)) * (1 - |z 3 a g (j : ℤ)|) := by
      conv_lhs => rw [← hterms]
      ring
    _ ≤ _ := by linarith only [hδc, hδg]

end CodexPaper1.TaskE.FCProof
#print axioms CodexPaper1.TaskE.FCProof.pair_match_budget
