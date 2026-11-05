import Research.Backfill.Paper7.CycleThreeResidualPolynomials
import Research.Backfill.Paper7.CycleThreeFiniteReduction

/-! Monicity, exact degree and complete integer-factorization equivalences.
No residual factorization exclusion is assumed or asserted. -/
set_option autoImplicit false
noncomputable section
namespace Paper7CycleThree
open Polynomial BackfillPaper7.Challenge BackfillPaper7.Challenge.Legacy.Algebra

/-- Removing only proven factors with roots 0, 1 and -1 preserves the entire
integer factorization on the original window. -/
theorem triangle_strip_data (p q : Fin 3 → ℕ) (H : Polynomial ℤ) (u v : ℕ)
    (hid : trianglePolynomial p q = (X ^ u * (X ^ 2 - 1) ^ v) * H) :
    H.Monic ∧ u + 2 * v + H.natDegree = 12 ∧
      (IntegerFactorizationOn (trianglePolynomial p q) (integerWindow 9) ↔
        IntegerFactorizationOn H (integerWindow 9)) := by
  have hd := Paper7Cleared.monic_denominator_factor u v
  have hF := (triangle_monic_degree p q).1
  have hH : H.Monic := hd.of_mul_monic_left (hid ▸ hF)
  have hdeg := (triangle_monic_degree p q).2
  rw [hid, hd.natDegree_mul hH, Paper7Cleared.degree_denominator_factor] at hdeg
  refine ⟨hH, hdeg, ?_⟩
  constructor
  · intro hfactor
    apply Paper7SpectralWindow.integerFactorizationOn_of_monic_dvd hH hF.ne_zero
    · exact ⟨X ^ u * (X ^ 2 - 1) ^ v, hid.trans (mul_comm _ _)⟩
    · exact hfactor
  · intro hfactor
    rw [hid]
    exact Paper7SpectralWindow.integerFactorizationOn_mul
      (Paper7SpectralWindow.denominator_integerFactorization u v) hfactor
#print axioms Paper7CycleThree.triangle_strip_data

theorem triangle_noQ_residual_data (p q : Fin 3 → ℕ) (hq : ∀ i, q i = 0) :
    (triangleResidualNoQ p).Monic ∧ (triangleResidualNoQ p).natDegree = 6 ∧
      (IntegerFactorizationOn (trianglePolynomial p q) (integerWindow 9) ↔
        IntegerFactorizationOn (triangleResidualNoQ p) (integerWindow 9)) := by
  have h := triangle_strip_data p q (triangleResidualNoQ p) 0 3
    (by simpa only [pow_zero, one_mul] using triangle_noQ_factor p q hq)
  exact ⟨h.1, by omega, h.2.2⟩
#print axioms Paper7CycleThree.triangle_noQ_residual_data

theorem triangle_oneQ_residual_data (p q : Fin 3 → ℕ) (hq1 : q 1 = 0) (hq2 : q 2 = 0) :
    (triangleResidualOneQ p (q 0)).Monic ∧ (triangleResidualOneQ p (q 0)).natDegree = 8 ∧
      (IntegerFactorizationOn (trianglePolynomial p q) (integerWindow 9) ↔
        IntegerFactorizationOn (triangleResidualOneQ p (q 0)) (integerWindow 9)) := by
  have h := triangle_strip_data p q (triangleResidualOneQ p (q 0)) 0 2
    (by simpa only [pow_zero, one_mul] using triangle_oneQ_factor p q hq1 hq2)
  exact ⟨h.1, by omega, h.2.2⟩
#print axioms Paper7CycleThree.triangle_oneQ_residual_data

theorem triangle_offZero_residual_data (p q : Fin 3 → ℕ) (hp0 : p 0 = 0) (hq2 : q 2 = 0) :
    (triangleResidualOffZero (p 1) (p 2) (q 0) (q 1)).Monic ∧
      (triangleResidualOffZero (p 1) (p 2) (q 0) (q 1)).natDegree = 8 ∧
      (IntegerFactorizationOn (trianglePolynomial p q) (integerWindow 9) ↔
        IntegerFactorizationOn (triangleResidualOffZero (p 1) (p 2) (q 0) (q 1))
          (integerWindow 9)) := by
  have h := triangle_strip_data p q (triangleResidualOffZero (p 1) (p 2) (q 0) (q 1)) 2 1
    (by simpa only [pow_one] using triangle_offZero_factor p q hp0 hq2)
  exact ⟨h.1, by omega, h.2.2⟩
#print axioms Paper7CycleThree.triangle_offZero_residual_data

theorem triangle_atZero_residual_data (p q : Fin 3 → ℕ) (hp2 : p 2 = 0) (hq2 : q 2 = 0) :
    (triangleResidualAtZero (p 0) (p 1) (q 0) (q 1)).Monic ∧
      (triangleResidualAtZero (p 0) (p 1) (q 0) (q 1)).natDegree = 8 ∧
      (IntegerFactorizationOn (trianglePolynomial p q) (integerWindow 9) ↔
        IntegerFactorizationOn (triangleResidualAtZero (p 0) (p 1) (q 0) (q 1))
          (integerWindow 9)) := by
  have h := triangle_strip_data p q (triangleResidualAtZero (p 0) (p 1) (q 0) (q 1)) 2 1
    (by simpa only [pow_one] using triangle_atZero_factor p q hp2 hq2)
  exact ⟨h.1, by omega, h.2.2⟩
#print axioms Paper7CycleThree.triangle_atZero_residual_data

end Paper7CycleThree
