import Mathlib

/-! Two small convexity bounds for nonnegative degree excesses. No list of
partitions is generated or assumed. -/
set_option autoImplicit false
open scoped BigOperators

namespace Paper7IntroFour

theorem sum_sq_cap_thirteen_budget_fifteen {ι : Type*} (s : Finset ι) (y : ι → ℤ)
    (hy : ∀ i ∈ s, 0 ≤ y i) (hcap : ∀ i ∈ s, y i ≤ 13)
    (hsum : ∑ i ∈ s, y i ≤ 15) : ∑ i ∈ s, y i ^ 2 ≤ 173 := by
  classical
  by_cases hlarge : ∃ i ∈ s, 2 ≤ y i
  · obtain ⟨i, hi, htwo⟩ := hlarge
    have he := Finset.sum_erase_add s y hi
    have he2 := Finset.sum_erase_add s (fun j => y j ^ 2) hi
    have hnonneg : 0 ≤ ∑ j ∈ s.erase i, y j :=
      Finset.sum_nonneg (fun j hj => hy j (Finset.mem_of_mem_erase hj))
    have hsq := Finset.sum_sq_le_sq_sum_of_nonneg
      (s := s.erase i) (fun j hj => hy j (Finset.mem_of_mem_erase hj))
    have hc := hcap i hi
    have hp : 0 ≤ (15 - y i - ∑ j ∈ s.erase i, y j) *
        (15 - y i + ∑ j ∈ s.erase i, y j) :=
      mul_nonneg (by omega) (by omega)
    have hiq : 0 ≤ (y i - 2) * (13 - y i) :=
      mul_nonneg (by omega) (by omega)
    nlinarith
  · have hsmall (i : ι) (hi : i ∈ s) : y i ^ 2 ≤ 2 * y i := by
      have hn : y i < 2 := lt_of_not_ge (fun h => hlarge ⟨i, hi, h⟩)
      have hzero := hy i hi
      nlinarith
    calc
      _ ≤ ∑ i ∈ s, 2 * y i := Finset.sum_le_sum hsmall
      _ = 2 * ∑ i ∈ s, y i := (Finset.mul_sum _ _ _).symm
      _ ≤ 173 := by omega
#print axioms Paper7IntroFour.sum_sq_cap_thirteen_budget_fifteen

theorem sum_sq_cap_thirteen_budget_seventeen {ι : Type*} (s : Finset ι) (y : ι → ℤ)
    (hy : ∀ i ∈ s, 0 ≤ y i) (hcap : ∀ i ∈ s, y i ≤ 13)
    (hsum : ∑ i ∈ s, y i ≤ 17) : ∑ i ∈ s, y i ^ 2 ≤ 185 := by
  classical
  by_cases hlarge : ∃ i ∈ s, 4 ≤ y i
  · obtain ⟨i, hi, hfour⟩ := hlarge
    have he := Finset.sum_erase_add s y hi
    have he2 := Finset.sum_erase_add s (fun j => y j ^ 2) hi
    have hnonneg : 0 ≤ ∑ j ∈ s.erase i, y j :=
      Finset.sum_nonneg (fun j hj => hy j (Finset.mem_of_mem_erase hj))
    have hsq := Finset.sum_sq_le_sq_sum_of_nonneg
      (s := s.erase i) (fun j hj => hy j (Finset.mem_of_mem_erase hj))
    have hc := hcap i hi
    have hp : 0 ≤ (17 - y i - ∑ j ∈ s.erase i, y j) *
        (17 - y i + ∑ j ∈ s.erase i, y j) :=
      mul_nonneg (by omega) (by omega)
    have hiq : 0 ≤ (y i - 4) * (13 - y i) :=
      mul_nonneg (by omega) (by omega)
    nlinarith
  · have hsmall (i : ι) (hi : i ∈ s) : y i ^ 2 ≤ 4 * y i := by
      have hn : y i < 4 := lt_of_not_ge (fun h => hlarge ⟨i, hi, h⟩)
      have hzero := hy i hi
      nlinarith
    calc
      _ ≤ ∑ i ∈ s, 4 * y i := Finset.sum_le_sum hsmall
      _ = 4 * ∑ i ∈ s, y i := (Finset.mul_sum _ _ _).symm
      _ ≤ 185 := by omega
#print axioms Paper7IntroFour.sum_sq_cap_thirteen_budget_seventeen

end Paper7IntroFour
