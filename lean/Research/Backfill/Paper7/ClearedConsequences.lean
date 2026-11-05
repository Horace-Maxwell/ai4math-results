import Research.Backfill.Paper7.SunPQCardinality

/-! This is a conditional consequence lemma, not the frozen main contract.
The graph-to-Schur polynomial identity remains a separate unresolved obligation. -/

set_option autoImplicit false
set_option maxRecDepth 4096

noncomputable section

namespace Paper7Cleared

open Polynomial BackfillPaper7.Challenge BackfillPaper7.Challenge.Legacy.Algebra

theorem monic_denominator_factor (u v : ℕ) :
    (X ^ u * (X ^ 2 - 1) ^ v : Polynomial ℤ).Monic :=
  (monic_X.pow u).mul ((monic_X_pow_sub_one (by decide)).pow v)

#print axioms Paper7Cleared.monic_denominator_factor

theorem degree_denominator_factor (u v : ℕ) :
    (X ^ u * (X ^ 2 - 1) ^ v : Polynomial ℤ).natDegree = u + 2 * v := by
  have hB : (X ^ 2 - 1 : Polynomial ℤ).Monic := monic_X_pow_sub_one (by decide)
  have hdegB : (X ^ 2 - 1 : Polynomial ℤ).natDegree = 2 := by compute_degree; norm_num
  rw [(monic_X.pow u).natDegree_mul (hB.pow v),
    Polynomial.natDegree_pow, Polynomial.natDegree_pow, Polynomial.natDegree_X, hdegB]
  omega

#print axioms Paper7Cleared.degree_denominator_factor

theorem monic_degree_of_cleared_identity (b : ℕ) (p q : Fin b → ℕ)
    (hidentity : X ^ totalP b p * (X ^ 2 - 1) ^ totalQ b q * clearedF b p q =
      X ^ b * (X ^ 2 - 1) ^ b * graphPhi (SG b p q)) :
    (clearedF b p q).Monic ∧ (clearedF b p q).natDegree = 4 * b := by
  classical
  have hG : (graphPhi (SG b p q)).Monic := by
    unfold graphPhi
    exact Matrix.charpoly_monic _
  have hR : (X ^ b * (X ^ 2 - 1) ^ b * graphPhi (SG b p q)).Monic :=
    (monic_denominator_factor b b).mul hG
  have hL : (X ^ totalP b p * (X ^ 2 - 1) ^ totalQ b q * clearedF b p q).Monic := by
    rw [hidentity]
    exact hR
  have hF : (clearedF b p q).Monic :=
    (monic_denominator_factor (totalP b p) (totalQ b q)).of_mul_monic_left hL
  have hGdeg : (graphPhi (SG b p q)).natDegree = b + totalP b p + 2 * totalQ b q := by
    unfold graphPhi
    rw [Matrix.charpoly_natDegree_eq_dim]
    exact card_sun_pq b p q
  have hdegree := congrArg Polynomial.natDegree hidentity
  rw [(monic_denominator_factor (totalP b p) (totalQ b q)).natDegree_mul hF,
    (monic_denominator_factor b b).natDegree_mul hG,
    degree_denominator_factor, degree_denominator_factor, hGdeg] at hdegree
  exact ⟨hF, by omega⟩

#print axioms Paper7Cleared.monic_degree_of_cleared_identity

end Paper7Cleared
