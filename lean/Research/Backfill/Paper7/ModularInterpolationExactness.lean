import Research.Backfill.Paper7.InterpolationForward
import Research.Backfill.Paper7.InterpolationDeterminant
import Research.Backfill.Paper7.LegacyModuliAndWindows

/-! Both conjuncts of the complete frozen interpolation contract. -/

set_option autoImplicit false

open BackfillPaper7.Challenge.Legacy.Algebra

theorem check_ModularInterpolationExactness :
    BackfillPaper7.Challenge.Legacy.Algebra.ModularInterpolationExactness := by
  constructor
  · intro ℓ _ d hd
    refine ⟨Paper7Interpolation.node_injOn ℓ d hd, ?_, ?_⟩
    · intro f hf
      exact Paper7Interpolation.reconstruction_exact ℓ d hd f hf
    · intro f g hf hg heval
      exact Paper7Interpolation.polynomial_unique ℓ d hd f g hf hg heval
  · intro ℓ _ hℓ b p q _ hb
    have hlarge : 216 < ℓ :=
      (Paper7Moduli.legacy_modulus_prime_and_large ℓ
        (Finset.mem_union_left _ (Finset.mem_union_left _ hℓ))).2
    have hdegree : 4 * b < ℓ := by omega
    constructor
    · exact Paper7Interpolation.determinantSample_eq_eval ℓ b p q
    · have hvalues : determinantSample ℓ b p q =
          fun i => (reducePolynomial ℓ (clearedF b p q)).eval (interpolationNode ℓ i) := by
        funext i
        exact Paper7Interpolation.determinantSample_eq_eval ℓ b p q i
      rw [hvalues]
      exact Paper7Interpolation.reconstruction_exact ℓ (4 * b) hdegree _
        (Paper7Interpolation.reduce_clearedF_natDegree_le ℓ b p q)

#print axioms check_ModularInterpolationExactness
