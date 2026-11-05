import Research.Backfill.Paper7.IntroPendantFourMoments

/-! The actual vector of all outside neighbors of a bare C4 attachment root.
The root may have arbitrarily many outside neighbors and arbitrary branches. -/
set_option autoImplicit false
noncomputable section
open scoped Classical Matrix BigOperators

namespace Paper7IntroFourExternal
open Matrix SimpleGraph BackfillPaper7.Challenge Paper7IntroPendantFour

def fourExternalVector
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (o u : V) : V → ℝ :=
    G.adjMatrix ℝ *ᵥ Pi.single u 1 - G.adjMatrix ℝ *ᵥ Pi.single o 1
#print axioms Paper7IntroFourExternal.fourExternalVector

theorem symmetric_mulVec_coordinate
    {V : Type} [Fintype V] [DecidableEq V]
    (M : Matrix V V ℝ) (hM : M.IsSymm) (x : V → ℝ) (i : V) :
    (M *ᵥ x) i = (M *ᵥ Pi.single i 1) ⬝ᵥ x := by
  rw [Matrix.mulVec_single_one]
  change (∑ j, M i j * x j) = ∑ j, M j i * x j
  apply Finset.sum_congr rfl
  intro j _hj
  exact congrArg (fun t => t * x j) (hM.apply i j).symm
#print axioms Paper7IntroFourExternal.symmetric_mulVec_coordinate

theorem four_external_vector_data
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hI : IsIntegralGraph G)
    (hbound : ∀ x ∈ spec G, |x| ≤ 3)
    (o a b u : V) (hab : a ≠ b) (hou : o ≠ u)
    (ho : ∀ j, G.Adj o j ↔ j = a ∨ j = b)
    (ha : ∀ j, G.Adj a j ↔ j = o ∨ j = u)
    (hb : ∀ j, G.Adj b j ↔ j = o ∨ j = u) :
    radiusThreeFactor (G.adjMatrix ℝ) *ᵥ fourExternalVector G o u = 0 ∧
    fourExternalVector G o u a = 0 ∧ fourExternalVector G o u b = 0 ∧
    fourExternalVector G o u ⬝ᵥ fourExternalVector G o u = (G.degree u : ℝ) - 2 ∧
    (G.adjMatrix ℝ) ^ 2 *ᵥ Pi.single a 1 =
      (2 : ℝ) • Pi.single a 1 + (2 : ℝ) • Pi.single b 1 + fourExternalVector G o u ∧
    (G.adjMatrix ℝ) ^ 2 *ᵥ Pi.single b 1 =
      (2 : ℝ) • Pi.single a 1 + (2 : ℝ) • Pi.single b 1 + fourExternalVector G o u := by
  let A := G.adjMatrix ℝ
  let z := fourExternalVector G o u
  have hvo : A *ᵥ Pi.single o 1 = Pi.single a 1 + Pi.single b 1 :=
    adjacency_single_two G o a b hab ho
  have hva : A *ᵥ Pi.single a 1 = Pi.single o 1 + Pi.single u 1 :=
    adjacency_single_two G a o u hou ha
  have hvb : A *ᵥ Pi.single b 1 = Pi.single o 1 + Pi.single u 1 :=
    adjacency_single_two G b o u hou hb
  have hau : (A *ᵥ Pi.single u 1) a = 1 := by
    rw [Matrix.mulVec_single_one]
    change (if G.Adj a u then (1 : ℝ) else 0) = 1
    exact ite_eq_left ((ha u).mpr (Or.inr rfl))
  have hbu : (A *ᵥ Pi.single u 1) b = 1 := by
    rw [Matrix.mulVec_single_one]
    change (if G.Adj b u then (1 : ℝ) else 0) = 1
    exact ite_eq_left ((hb u).mpr (Or.inr rfl))
  have hza : z a = 0 := by
    change (A *ᵥ Pi.single u 1) a - (A *ᵥ Pi.single o 1) a = 0
    rw [hau, hvo]
    simp [hab]
  have hzb : z b = 0 := by
    change (A *ᵥ Pi.single u 1) b - (A *ᵥ Pi.single o 1) b = 0
    rw [hbu, hvo]
    simp [hab.symm]
  have h2o : A ^ 2 *ᵥ Pi.single o 1 =
      (2 : ℝ) • Pi.single o 1 + (2 : ℝ) • Pi.single u 1 := by
    rw [pow_two, ← Matrix.mulVec_mulVec, hvo, Matrix.mulVec_add, hva, hvb]
    funext i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hmove : (A * (A ^ 2 - (4 : ℝ) • 1)) *ᵥ Pi.single o 1 = (2 : ℝ) • z := by
    change (A * (A ^ 2 - (4 : ℝ) • 1)) *ᵥ Pi.single o 1 =
      (2 : ℝ) • (A *ᵥ Pi.single u 1 - A *ᵥ Pi.single o 1)
    rw [← Matrix.mulVec_mulVec, Matrix.sub_mulVec, Matrix.smul_mulVec,
      Matrix.one_mulVec, h2o, Matrix.mulVec_sub, Matrix.mulVec_add,
      Matrix.mulVec_smul, Matrix.mulVec_smul, Matrix.mulVec_smul]
    funext i
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hz : radiusThreeFactor A *ᵥ z = 0 := by
    have h := congrArg (fun M : Matrix V V ℝ => M *ᵥ Pi.single o 1)
      (integral_radius_three_matrix_annihilator G hI hbound)
    rw [Matrix.zero_mulVec] at h
    change (radiusThreeFactor A * A * (A ^ 2 - (4 : ℝ) • 1)) *ᵥ Pi.single o 1 = 0 at h
    rw [Matrix.mul_assoc, ← Matrix.mulVec_mulVec, hmove, Matrix.mulVec_smul] at h
    funext i
    have hi := congrFun h i
    change 2 * (radiusThreeFactor A *ᵥ z) i = 0 at hi
    change (radiusThreeFactor A *ᵥ z) i = 0
    linarith
  have hdu : (A *ᵥ Pi.single u 1) ⬝ᵥ (A *ᵥ Pi.single u 1) = (G.degree u : ℝ) := by
    rw [← symmetric_square_entry A G.isSymm_adjMatrix u u]
    simpa only [A, pow_two] using G.adjMatrix_mul_self_apply_self (α := ℝ) u
  have hnorm : z ⬝ᵥ z = (G.degree u : ℝ) - 2 := by
    change (A *ᵥ Pi.single u 1 - A *ᵥ Pi.single o 1) ⬝ᵥ z = _
    rw [sub_dotProduct, hvo, add_dotProduct, single_one_dotProduct,
      single_one_dotProduct, hza, hzb]
    change (A *ᵥ Pi.single u 1) ⬝ᵥ
      (A *ᵥ Pi.single u 1 - A *ᵥ Pi.single o 1) - (0 + 0) = _
    rw [dotProduct_sub, hvo, dotProduct_add, dotProduct_single_one,
      dotProduct_single_one, hdu, hau, hbu]
    ring
  have h2a : A ^ 2 *ᵥ Pi.single a 1 =
      (2 : ℝ) • Pi.single a 1 + (2 : ℝ) • Pi.single b 1 + z := by
    change A ^ 2 *ᵥ Pi.single a 1 = (2 : ℝ) • Pi.single a 1 +
      (2 : ℝ) • Pi.single b 1 + (A *ᵥ Pi.single u 1 - A *ᵥ Pi.single o 1)
    rw [pow_two, ← Matrix.mulVec_mulVec, hva, Matrix.mulVec_add, hvo]
    funext i
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have h2b : A ^ 2 *ᵥ Pi.single b 1 =
      (2 : ℝ) • Pi.single a 1 + (2 : ℝ) • Pi.single b 1 + z := by
    change A ^ 2 *ᵥ Pi.single b 1 = (2 : ℝ) • Pi.single a 1 +
      (2 : ℝ) • Pi.single b 1 + (A *ᵥ Pi.single u 1 - A *ᵥ Pi.single o 1)
    rw [pow_two, ← Matrix.mulVec_mulVec, hvb, Matrix.mulVec_add, hvo]
    funext i
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  exact ⟨hz, hza, hzb, hnorm, h2a, h2b⟩
#print axioms Paper7IntroFourExternal.four_external_vector_data

end Paper7IntroFourExternal
