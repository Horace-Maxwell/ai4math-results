import Research.Backfill.Paper1.PathAndSign
import Research.Backfill.Paper1.SupplementStatements

set_option autoImplicit false
noncomputable section
namespace CodexPaper1
open BackfillPaper1

theorem check_MuBounds : NarrowSupplement.MuBounds := by
  intro x hx
  have hx0 : 0 < x := by linarith
  have hn1 : ICGGeneral.nu x 1 = (x - 2) / x := by
    simp only [ICGGeneral.nu]; ring
  have hn2 : ICGGeneral.nu x 2 = ((x - 1) ^ 2 + 1) / x ^ 2 := by
    simp only [ICGGeneral.nu]
    field_simp [ne_of_gt hx0]
    ring
  have hl (j : ℕ) : ICGGeneral.nu x 1 ≤ ICGGeneral.nu x (j + 1) := by
    rw [hn1]
    exact (ICGGeneral.nu_bounds hx.le (j + 1)).1
  have hu (j : ℕ) : ICGGeneral.nu x (j + 1) ≤ ICGGeneral.nu x 2 := by
    cases j with
    | zero => exact hl 1
    | succ j =>
      change (x - 1 - ICGGeneral.nu x (j + 1)) / x ≤
        (x - 1 - ICGGeneral.nu x 1) / x
      exact div_le_div_of_nonneg_right (by linarith [hl j]) hx0.le
  have hm0 : Challenge.mu x 0 = ICGGeneral.nu x 1 := by
    simpa using Additional.mu_nat_eq_nu x 0
  have hm1 : Challenge.mu x 1 = ICGGeneral.nu x 2 := by
    simpa using Additional.mu_nat_eq_nu x 1
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro j _hj
    rw [Challenge.mu, Additional.muSeq_eq_nu]
    exact ICGGeneral.nu_bounds hx.le (j + 1).toNat
  · intro j
    rw [hm0, hm1]
    simp only [Additional.mu_nat_eq_nu]
    exact ⟨hl j, hu j⟩
  · rw [hm0, hn1]
  · rw [hm1, hn2]

theorem check_MuClosedParity : NarrowSupplement.MuClosedParity := by
  intro x hx j
  have hx0 : 0 < x := by linarith
  simp only [Additional.mu_nat_eq_nu]
  refine ⟨?_, ?_, ?_⟩
  · exact ICGEqualParity.nu_sub_L hx0 (j + 1)
  · intro hj
    have hpar : Even (j + 1) := by
      obtain ⟨k, hk⟩ := hj
      exact ⟨k + 1, by omega⟩
    exact ICGEqualParity.nu_even_gt (by linarith) hpar
  · intro hj
    have hpar : Odd (j + 1) := by
      obtain ⟨k, hk⟩ := hj
      exact ⟨k, by omega⟩
    exact ICGEqualParity.nu_odd_lt (by linarith) hpar

#print axioms check_MuBounds
#print axioms check_MuClosedParity
end CodexPaper1
