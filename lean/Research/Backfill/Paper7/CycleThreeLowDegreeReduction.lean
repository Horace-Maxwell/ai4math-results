import Research.Backfill.Paper7.CycleThreeResidualFactorization
import Research.Backfill.Paper7.CycleThreeSupportReduction

/-! Complete coverage of the remaining support strata by actual coordinate
permutations. The residual exclusions themselves remain open. -/
set_option autoImplicit false
noncomputable section
namespace Paper7CycleThree
open Polynomial BackfillPaper7.Challenge BackfillPaper7.Challenge.Legacy.Algebra
open scoped BigOperators Classical

theorem triangle_q2_shape_permutation (p q : Fin 3 → ℕ)
    (hG : IsIntegralGraph (SG 3 p q)) (hn : nOf 3 p q ≤ 49) (hq2 : q 2 = 0) :
    ∃ e : Equiv.Perm (Fin 3), e 2 = 2 ∧
      (q (e 1) = 0 ∨ p (e 0) = 0 ∨ p (e 2) = 0) := by
  by_cases hq1 : q 1 = 0
  · exact ⟨Equiv.refl _, rfl, Or.inl hq1⟩
  by_cases hq0 : q 0 = 0
  · refine ⟨Equiv.swap 0 1, ?_, Or.inl ?_⟩
    · decide
    · simpa using hq0
  have hpos : ∀ k : Fin 3, k ≠ 2 → 0 < q k := by
    intro k hk
    fin_cases k
    · exact Nat.pos_of_ne_zero hq0
    · exact Nat.pos_of_ne_zero hq1
    · exact (hk rfl).elim
  obtain ⟨j, hj⟩ := triangle_two_q_exists_zero_p p q hG hn 2 hq2 hpos
  fin_cases j
  · exact ⟨Equiv.refl _, rfl, Or.inr (Or.inl hj)⟩
  · refine ⟨Equiv.swap 0 1, ?_, Or.inr (Or.inl ?_)⟩
    · decide
    · simpa using hj
  · exact ⟨Equiv.refl _, rfl, Or.inr (Or.inr hj)⟩
#print axioms Paper7CycleThree.triangle_q2_shape_permutation

theorem triangle_residual_shape_permutation (p q : Fin 3 → ℕ)
    (hG : IsIntegralGraph (SG 3 p q)) (hn : nOf 3 p q ≤ 49) :
    ∃ e : Equiv.Perm (Fin 3), q (e 2) = 0 ∧
      (q (e 1) = 0 ∨ p (e 0) = 0 ∨ p (e 2) = 0) := by
  obtain ⟨j, hj⟩ := triangle_exists_zero_q p q hG hn
  let e : Equiv.Perm (Fin 3) := Equiv.swap 2 j
  let pp : Fin 3 → ℕ := fun i => p (e i)
  let qq : Fin 3 → ℕ := fun i => q (e i)
  have hq2 : qq 2 = 0 := by simpa only [qq, e, Equiv.swap_apply_left] using hj
  have hn' : nOf 3 pp qq ≤ 49 := by
    change nOf 3 (fun i => p (e i)) (fun i => q (e i)) ≤ 49
    rw [triangle_nOf_permute]
    exact hn
  have hF : IntegerFactorizationOn (trianglePolynomial pp qq) (integerWindow 9) := by
    change IntegerFactorizationOn
      (trianglePolynomial (fun i => p (e i)) (fun i => q (e i))) (integerWindow 9)
    rw [trianglePolynomial_permute]
    exact (triangle_integral_iff_factorization p q hn).mp hG
  have hG' := triangle_factorization_implies_integral pp qq hF
  obtain ⟨f, hf2, hfshape⟩ := triangle_q2_shape_permutation pp qq hG' hn' hq2
  refine ⟨f.trans e, ?_, ?_⟩
  · change q (e (f 2)) = 0
    rw [hf2]
    exact hq2
  · exact hfshape
#print axioms Paper7CycleThree.triangle_residual_shape_permutation

/-- Three four-parameter residual families, retaining all original positive
pendant and order conditions. No exclusion proof is bundled into this definition. -/
def TriangleLowDegreeExclusion : Prop :=
  ∀ p q : Fin 3 → ℕ, 0 < ∑ i, (p i + q i) → nOf 3 p q ≤ 49 → q 2 = 0 →
    (q 1 = 0 → ¬ IntegerFactorizationOn (triangleResidualOneQ p (q 0)) (integerWindow 9)) ∧
    (p 0 = 0 → ¬ IntegerFactorizationOn
      (triangleResidualOffZero (p 1) (p 2) (q 0) (q 1)) (integerWindow 9)) ∧
    (p 2 = 0 → ¬ IntegerFactorizationOn
      (triangleResidualAtZero (p 0) (p 1) (q 0) (q 1)) (integerWindow 9))
#print axioms Paper7CycleThree.TriangleLowDegreeExclusion

theorem section6_cycle_three_iff_low_degree_exclusion :
    Section6CycleThree ↔ TriangleLowDegreeExclusion := by
  constructor
  · intro h p q hpos hn hq2
    have hb := section6_cycle_three_iff_bounded_pq.mp h
    refine ⟨?_, ?_, ?_⟩
    · intro hq1 hF
      exact hb p q hpos hn (triangle_factorization_implies_integral p q
        ((triangle_oneQ_residual_data p q hq1 hq2).2.2.mpr hF))
    · intro hp0 hF
      exact hb p q hpos hn (triangle_factorization_implies_integral p q
        ((triangle_offZero_residual_data p q hp0 hq2).2.2.mpr hF))
    · intro hp2 hF
      exact hb p q hpos hn (triangle_factorization_implies_integral p q
        ((triangle_atZero_residual_data p q hp2 hq2).2.2.mpr hF))
  · intro h
    apply section6_cycle_three_iff_bounded_pq.mpr
    intro p q hpos hn hG
    obtain ⟨e, hq2, hshape⟩ := triangle_residual_shape_permutation p q hG hn
    let pp : Fin 3 → ℕ := fun i => p (e i)
    let qq : Fin 3 → ℕ := fun i => q (e i)
    have hpos' : 0 < ∑ i, (pp i + qq i) := by
      change 0 < ∑ i, (p (e i) + q (e i))
      rw [Equiv.sum_comp e (fun i => p i + q i)]
      exact hpos
    have hn' : nOf 3 pp qq ≤ 49 := by
      change nOf 3 (fun i => p (e i)) (fun i => q (e i)) ≤ 49
      rw [triangle_nOf_permute]
      exact hn
    have hF : IntegerFactorizationOn (trianglePolynomial pp qq) (integerWindow 9) := by
      change IntegerFactorizationOn
        (trianglePolynomial (fun i => p (e i)) (fun i => q (e i))) (integerWindow 9)
      rw [trianglePolynomial_permute]
      exact (triangle_integral_iff_factorization p q hn).mp hG
    have hex := h pp qq hpos' hn' hq2
    rcases hshape with hq1 | hp0 | hp2
    · exact hex.1 hq1 ((triangle_oneQ_residual_data pp qq hq1 hq2).2.2.mp hF)
    · exact hex.2.1 hp0 ((triangle_offZero_residual_data pp qq hp0 hq2).2.2.mp hF)
    · exact hex.2.2 hp2 ((triangle_atZero_residual_data pp qq hp2 hq2).2.2.mp hF)
#print axioms Paper7CycleThree.section6_cycle_three_iff_low_degree_exclusion

end Paper7CycleThree
