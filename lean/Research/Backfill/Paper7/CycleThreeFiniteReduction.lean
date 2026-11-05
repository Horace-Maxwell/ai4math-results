import Research.Backfill.Paper7.CycleThreeReduction
import Research.Backfill.Paper7.CycleThreePolynomial
import Research.Backfill.Paper7.SunSpectralWindowAndFactorization

/-! The remaining exclusion is an exact finite parameter assertion. This file
proves the reduction in both directions, but does not assert that exclusion. -/
set_option autoImplicit false
noncomputable section
namespace Paper7CycleThree
open Polynomial BackfillPaper7.Challenge BackfillPaper7.Challenge.Legacy.Algebra
open scoped BigOperators Classical

theorem triangle_factorization_implies_integral (p q : Fin 3 → ℕ)
    (hF : IntegerFactorizationOn (trianglePolynomial p q) (integerWindow 9)) :
    IsIntegralGraph (SG 3 p q) := by
  have hFm : (clearedF 3 p q).Monic :=
    (Paper7Cleared.check_ClearedCharacteristicPolynomial 3 p q (by omega)).2.1
  have hFmS : IntegerFactorizationOn (clearedF 3 p q) (integerWindow 9) := by
    rwa [triangle_clearedF]
  have hden := Paper7SpectralWindow.denominator_integerFactorization (totalP 3 p) (totalQ 3 q)
  have hfactor := Paper7SpectralWindow.integerFactorizationOn_mul hden hFmS
  have hnz : (X ^ totalP 3 p * (X ^ 2 - 1) ^ totalQ 3 q * clearedF 3 p q :
      Polynomial ℤ) ≠ 0 :=
    ((Paper7Cleared.monic_denominator_factor (totalP 3 p) (totalQ 3 q)).mul hFm).ne_zero
  have hdvd : graphPhi (SG 3 p q) ∣
      X ^ totalP 3 p * (X ^ 2 - 1) ^ totalQ 3 q * clearedF 3 p q := by
    refine ⟨X ^ 3 * (X ^ 2 - 1) ^ 3, ?_⟩
    exact (Paper7Cleared.cleared_identity 3 p q (by omega)).trans (mul_comm _ _)
  have hphiMonic : (graphPhi (SG 3 p q)).Monic := by
    unfold graphPhi
    exact Matrix.charpoly_monic _
  have hphi := Paper7SpectralWindow.integerFactorizationOn_of_monic_dvd
    hphiMonic hnz hdvd hfactor
  exact (Paper7Spectrum.integral_iff_integerFactorization (SG 3 p q)).mpr ⟨_, hphi⟩
#print axioms Paper7CycleThree.triangle_factorization_implies_integral

theorem triangle_integral_iff_factorization (p q : Fin 3 → ℕ)
    (hn : nOf 3 p q ≤ 49) : IsIntegralGraph (SG 3 p q) ↔
      IntegerFactorizationOn (trianglePolynomial p q) (integerWindow 9) := by
  constructor
  · intro hG
    have h := (Paper7SpectralWindow.check_SunSpectralWindowAndFactorization
      3 p q (by omega) hn).2 hG
    rw [triangle_clearedF] at h
    exact h.2
  · exact triangle_factorization_implies_integral p q
#print axioms Paper7CycleThree.triangle_integral_iff_factorization

/-- The exact remaining finite exclusion. Both parameter functions are bounded;
all zero entries and nonsymmetric configurations are retained. -/
def TriangleFiniteExclusion : Prop :=
  ∀ (p : Fin 3 → Fin 47) (q : Fin 3 → Fin 24),
    0 < ∑ k, ((p k).val + (q k).val) →
    nOf 3 (fun k => (p k).val) (fun k => (q k).val) ≤ 49 →
    ¬ IntegerFactorizationOn
      (trianglePolynomial (fun k => (p k).val) (fun k => (q k).val)) (integerWindow 9)
#print axioms Paper7CycleThree.TriangleFiniteExclusion

/-- No proof of TriangleFiniteExclusion is supplied by this equivalence. -/
theorem section6_cycle_three_iff_finite_exclusion :
    Section6CycleThree ↔ TriangleFiniteExclusion := by
  rw [section6_cycle_three_iff_bounded_pq]
  constructor
  · intro h p q hp hn hF
    exact h (fun k => (p k).val) (fun k => (q k).val) hp hn
      (triangle_factorization_implies_integral _ _ hF)
  · intro h p q hp hn hG
    have hb := triangle_parameter_bounds p q hn
    let pf : Fin 3 → Fin 47 := fun k => ⟨p k, by have := hb.1 k; omega⟩
    let qf : Fin 3 → Fin 24 := fun k => ⟨q k, by have := hb.2 k; omega⟩
    have hF := (triangle_integral_iff_factorization p q hn).mp hG
    exact h pf qf hp hn hF
#print axioms Paper7CycleThree.section6_cycle_three_iff_finite_exclusion

end Paper7CycleThree
