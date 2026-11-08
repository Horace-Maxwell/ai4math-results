import Research.Backfill.Paper1.Prop31Potential

/-! Static finite-index selection and sum bounds for Proposition31. -/
set_option autoImplicit false
noncomputable section
namespace CodexPaper1
open BackfillPaper1 Finset ICGGeneral
namespace Prop31

def TailChain (a b k : ℕ) (Y : ℕ → ℕ → ℝ) (g : ℕ → ℝ) : Prop :=
  ∀ l, 1 ≤ l → l ≤ k → ∀ i ≤ a, Y i (b - l) = (-1) ^ l * g i

lemma largest_deviation {a b : ℕ} {Y : ℕ → ℕ → ℝ}
    (hne : ¬ Challenge.MatEq a b Y Challenge.Yminus) :
    ∃ J ≤ b,
      (¬ ∀ i ≤ a, Y i J = Challenge.Yminus i J) ∧
      (∀ l, J < l → l ≤ b → ∀ i ≤ a, Y i l = (-1) ^ (l + 1) * Challenge.sAlt i) := by
  classical
  let bad := (range (b + 1)).filter (fun j => ¬ ∀ i ≤ a, Y i j = Challenge.Yminus i j)
  have hbad : bad.Nonempty := by
    by_contra hempty
    apply hne
    intro i hi j hj
    by_contra hij
    apply hempty
    exact ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), fun h => hij (h i hi)⟩⟩
  let J := bad.max' hbad
  have hmem : J ∈ bad := Finset.max'_mem bad hbad
  obtain ⟨hJ, hdev⟩ := Finset.mem_filter.mp hmem
  refine ⟨J, by simpa using Finset.mem_range.mp hJ, hdev, ?_⟩
  intro l hJl hl i hi
  have hsame : ∀ i ≤ a, Y i l = Challenge.Yminus i l := by
    by_contra hnot
    have hlbad : l ∈ bad := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hnot⟩
    have hle : l ≤ J := Finset.le_max' bad l hlbad
    omega
  rw [hsame i hi]
  unfold Challenge.Yminus Challenge.sAlt
  rw [pow_succ]
  ring

lemma longest_chain (a b : ℕ) (Y : ℕ → ℕ → ℝ) (g : ℕ → ℝ) :
    ∃ k ≤ b, TailChain a b k Y g ∧
      (k < b → ¬ ∀ i ≤ a, Y i (b - 1 - k) = (-1) ^ (k + 1) * g i) := by
  classical
  let good := (range (b + 1)).filter (fun k => TailChain a b k Y g)
  have hgood : good.Nonempty := by
    refine ⟨0, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), ?_⟩⟩
    intro l hl hl0
    omega
  let k := good.max' hgood
  obtain ⟨hkb, hchain⟩ := Finset.mem_filter.mp (Finset.max'_mem good hgood)
  refine ⟨k, Nat.le_of_lt_succ (Finset.mem_range.mp hkb), hchain, ?_⟩
  intro hk hnext
  have hchain' : TailChain a b (k + 1) Y g := by
    intro l hl hlk i hi
    by_cases hle : l ≤ k
    · exact hchain l hl hle i hi
    · have he : l = k + 1 := by omega
      subst l
      simpa only [show b - (k + 1) = b - 1 - k by omega] using hnext i hi
  have hm : k + 1 ∈ good := Finset.mem_filter.mpr
    ⟨Finset.mem_range.mpr (by omega), hchain'⟩
  have hle : k + 1 ≤ k := Finset.le_max' good (k + 1) hm
  omega

lemma chain_cases {b k : ℕ} (hk : k ≤ b) :
    (k < b ∧ k ≤ 4) ∨ (5 ≤ k ∧ k < b) ∨ k = b := by omega

lemma tail_sum_eq (f : ℕ → ℝ) {b k : ℕ} (hk : k ≤ b) :
    (∑ l ∈ Finset.Icc 1 k, f (b - l)) = ∑ j ∈ Finset.Ico (b - k) b, f j := by
  apply Finset.sum_bij (fun l _ => b - l)
  · intro l hl
    obtain ⟨hl1, hlk⟩ := Finset.mem_Icc.mp hl
    exact Finset.mem_Ico.mpr ⟨by omega, by omega⟩
  · intro l hl m hm he
    obtain ⟨hl1, hlk⟩ := Finset.mem_Icc.mp hl
    obtain ⟨hm1, hmk⟩ := Finset.mem_Icc.mp hm
    omega
  · intro j hj
    obtain ⟨hj0, hjb⟩ := Finset.mem_Ico.mp hj
    refine ⟨b - j, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, ?_⟩
    omega
  · intros; rfl

lemma tail_sum_le_total (f : ℕ → ℝ) {b k : ℕ} (hk : k ≤ b)
    (hnon : ∀ j < b, 0 ≤ f j) :
    (∑ l ∈ Finset.Icc 1 k, f (b - l)) ≤ ∑ j ∈ range b, f j := by
  rw [tail_sum_eq f hk]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro j hj
    exact Finset.mem_range.mpr (Finset.mem_Ico.mp hj).2
  · intro j hj _
    exact hnon j (Finset.mem_range.mp hj)

lemma tail_break_sum_le_total (f : ℕ → ℝ) {b k : ℕ} (hk : k < b)
    (hnon : ∀ j < b, 0 ≤ f j) :
    (∑ l ∈ Finset.Icc 1 k, f (b - l)) + f (b - 1 - k) ≤
      ∑ j ∈ range b, f j := by
  have hsum : (∑ l ∈ Finset.Icc 1 (k + 1), f (b - l)) =
      (∑ l ∈ Finset.Icc 1 k, f (b - l)) + f (b - 1 - k) := by
    rw [Finset.sum_Icc_succ_top (by omega)]
    rw [show b - (k + 1) = b - 1 - k by omega]
  rw [← hsum]
  exact tail_sum_le_total f (by omega) hnon

end Prop31
end CodexPaper1
