import Research.Backfill.Paper7.IntroFourExternalVector

/-! Exact weighted moments of all outside neighbors, with no restriction on
the root's number of outside edges or on the remaining graph. -/
set_option autoImplicit false
noncomputable section
open scoped Classical Matrix

namespace Paper7IntroFourExternal
open Matrix SimpleGraph BackfillPaper7.Challenge Paper7IntroPendantFour

theorem four_external_vector_moments
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hI : IsIntegralGraph G)
    (hbound : ∀ x ∈ spec G, |x| ≤ 3)
    (o a b u : V) (hab : a ≠ b) (hou : o ≠ u)
    (ho : ∀ j, G.Adj o j ↔ j = a ∨ j = b)
    (ha : ∀ j, G.Adj a j ↔ j = o ∨ j = u)
    (hb : ∀ j, G.Adj b j ↔ j = o ∨ j = u) :
    fourExternalVector G o u ⬝ᵥ (G.adjMatrix ℝ) ^ 2 *ᵥ fourExternalVector G o u =
      6 * ((G.degree u : ℝ) - 2) ∧
    fourExternalVector G o u ⬝ᵥ (G.adjMatrix ℝ) ^ 4 *ᵥ fourExternalVector G o u =
      51 * ((G.degree u : ℝ) - 2) := by
  let A := G.adjMatrix ℝ
  let z := fourExternalVector G o u
  let q : ℝ := (G.degree u : ℝ) - 2
  obtain ⟨hz, hza, hzb, hnorm, h2a, h2b⟩ :=
    four_external_vector_data G hI hbound o a b u hab hou ho ha hb
  change radiusThreeFactor A *ᵥ z = 0 at hz
  change z a = 0 at hza
  change z b = 0 at hzb
  change z ⬝ᵥ z = q at hnorm
  change A ^ 2 *ᵥ Pi.single a 1 = 2 • Pi.single a 1 + 2 • Pi.single b 1 + z at h2a
  change A ^ 2 *ᵥ Pi.single b 1 = 2 • Pi.single a 1 + 2 • Pi.single b 1 + z at h2b
  have h2za : (A ^ 2 *ᵥ z) a = q := by
    rw [symmetric_mulVec_coordinate (A ^ 2) (G.isSymm_adjMatrix.pow 2), h2a]
    simp only [add_dotProduct, smul_dotProduct, single_dotProduct,
      smul_eq_mul, hza, hzb, hnorm, mul_zero, zero_add]
  have h2zb : (A ^ 2 *ᵥ z) b = q := by
    rw [symmetric_mulVec_coordinate (A ^ 2) (G.isSymm_adjMatrix.pow 2), h2b]
    simp only [add_dotProduct, smul_dotProduct, single_dotProduct,
      smul_eq_mul, hza, hzb, hnorm, mul_zero, zero_add]
  have h4za : (A ^ 4 *ᵥ z) a = 4 * q + z ⬝ᵥ A ^ 2 *ᵥ z := by
    rw [show A ^ 4 = A ^ 2 * A ^ 2 from pow_add A 2 2,
      ← Matrix.mulVec_mulVec,
      symmetric_mulVec_coordinate (A ^ 2) (G.isSymm_adjMatrix.pow 2), h2a]
    simp only [add_dotProduct, smul_dotProduct, single_dotProduct, one_mul,
      smul_eq_mul, h2za, h2zb]
    ring
  have he : (A ^ 4 *ᵥ z) a - 10 * (A ^ 2 *ᵥ z) a + 9 * z a = 0 := by
    have h := congrFun hz a
    simpa only [radiusThreeFactor, Matrix.add_mulVec, Matrix.sub_mulVec,
      Matrix.smul_mulVec, Matrix.one_mulVec, Pi.add_apply, Pi.sub_apply,
      Pi.smul_apply, smul_eq_mul, Pi.zero_apply] using h
  have hmoment2 : z ⬝ᵥ A ^ 2 *ᵥ z = 6 * q := by
    rw [h4za, h2za, hza] at he
    linarith
  have hdot := congrArg (fun x : V → ℝ => z ⬝ᵥ x) hz
  have hscalar : z ⬝ᵥ A ^ 4 *ᵥ z - 10 * (z ⬝ᵥ A ^ 2 *ᵥ z) +
      9 * (z ⬝ᵥ z) = 0 := by
    simpa only [radiusThreeFactor, Matrix.add_mulVec, Matrix.sub_mulVec,
      Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_add, dotProduct_sub,
      dotProduct_smul, smul_eq_mul, dotProduct_zero] using hdot
  have hmoment4 : z ⬝ᵥ A ^ 4 *ᵥ z = 51 * q := by
    rw [hmoment2, hnorm] at hscalar
    change z ⬝ᵥ A ^ 4 *ᵥ z - 10 * (6 * q) + 9 * q = 0 at hscalar
    linarith
  exact ⟨hmoment2, hmoment4⟩
#print axioms Paper7IntroFourExternal.four_external_vector_moments

end Paper7IntroFourExternal
