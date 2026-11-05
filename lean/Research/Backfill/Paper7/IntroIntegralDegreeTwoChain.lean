import Research.Backfill.Paper7.IntroIntegralQuarticPSD

/-! Exact local walk moments from three actual two-neighbor rows. -/
set_option autoImplicit false
noncomputable section
open scoped Classical Matrix BigOperators

namespace Paper7IntroLocalQuartic
open Matrix SimpleGraph BackfillPaper7.Challenge

theorem symmetric_square_diagonal
    {V : Type} [Fintype V] [DecidableEq V]
    (A : Matrix V V ℝ) (hA : A.IsSymm) (i : V) :
    (A ^ 2) i i = (A *ᵥ Pi.single i 1) ⬝ᵥ (A *ᵥ Pi.single i 1) := by
  rw [pow_two, Matrix.mul_apply, Matrix.mulVec_single_one]
  change (∑ j, A i j * A j i) = ∑ j, A j i * A j i
  apply Finset.sum_congr rfl
  intro j _
  exact congrArg (fun x => x * A j i) (hA.apply i j).symm
#print axioms Paper7IntroLocalQuartic.symmetric_square_diagonal

theorem adjacency_single_of_two_neighbors
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (i a b : V) (hab : a ≠ b)
    (hN : ∀ j, G.Adj i j ↔ j = a ∨ j = b) :
    G.adjMatrix ℝ *ᵥ Pi.single i 1 = Pi.single a 1 + Pi.single b 1 := by
  rw [Matrix.mulVec_single_one]
  funext j
  change (if G.Adj j i then (1 : ℝ) else 0) = (Pi.single a (1 : ℝ) : V → ℝ) j + (Pi.single b (1 : ℝ) : V → ℝ) j
  by_cases hja : j = a
  · subst j
    have ha : G.Adj a i := ((hN a).mpr (Or.inl rfl)).symm
    rw [ite_eq_left ha, Pi.single_eq_same, Pi.single_eq_of_ne hab]
    norm_num
  · by_cases hjb : j = b
    · subst j
      have hb : G.Adj b i := ((hN b).mpr (Or.inr rfl)).symm
      rw [ite_eq_left hb, Pi.single_eq_of_ne hja, Pi.single_eq_same]
      norm_num
    · have hn : ¬G.Adj j i := by
        intro h
        exact ((hN j).mp h.symm).elim hja hjb
      rw [ite_eq_right hn, Pi.single_eq_of_ne hja, Pi.single_eq_of_ne hjb]
      norm_num
#print axioms Paper7IntroLocalQuartic.adjacency_single_of_two_neighbors

theorem two_step_chain_quartic_diagonal_zero
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (o a b c d : V)
    (hab : a ≠ b) (hoc : o ≠ c) (hod : o ≠ d) (hcd : c ≠ d)
    (ho : ∀ j, G.Adj o j ↔ j = a ∨ j = b)
    (ha : ∀ j, G.Adj a j ↔ j = o ∨ j = c)
    (hb : ∀ j, G.Adj b j ↔ j = o ∨ j = d) :
    quarticGap (G.adjMatrix ℝ) o o = 0 := by
  let A := G.adjMatrix ℝ
  have h1 : A *ᵥ Pi.single o 1 = Pi.single a 1 + Pi.single b 1 :=
    adjacency_single_of_two_neighbors G o a b hab ho
  have h2 : A ^ 2 *ᵥ Pi.single o 1 =
      (Pi.single o 1 + Pi.single c 1) + (Pi.single o 1 + Pi.single d 1) := by
    rw [pow_two, ← Matrix.mulVec_mulVec, h1, Matrix.mulVec_add]
    rw [adjacency_single_of_two_neighbors G a o c hoc ha,
      adjacency_single_of_two_neighbors G b o d hod hb]
  have hm2 : (A ^ 2) o o = 2 := by
    rw [symmetric_square_diagonal A G.isSymm_adjMatrix, h1]
    simp_all [dotProduct_add]
    norm_num
  have hm4 : (A ^ 4) o o = 6 := by
    rw [show A ^ 4 = (A ^ 2) ^ 2 from pow_mul A 2 2,
      symmetric_square_diagonal (A ^ 2) (G.isSymm_adjMatrix.pow 2), h2]
    simp_all [dotProduct_add]
    norm_num
  change (A ^ 4) o o - 5 * (A ^ 2) o o + 4 * (1 : Matrix V V ℝ) o o = 0
  rw [hm2, hm4, Matrix.one_apply_eq]
  norm_num
#print axioms Paper7IntroLocalQuartic.two_step_chain_quartic_diagonal_zero

theorem integral_connected_no_two_step_degree_two_chain
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : G.Connected) (hI : IsIntegralGraph G)
    (s : ℝ) (hs : s ∈ spec G) (hs2 : 2 < s)
    (o a b c d : V) (hab : a ≠ b) (hoc : o ≠ c) (hod : o ≠ d) (hcd : c ≠ d)
    (ho : ∀ j, G.Adj o j ↔ j = a ∨ j = b)
    (ha : ∀ j, G.Adj a j ↔ j = o ∨ j = c)
    (hb : ∀ j, G.Adj b j ↔ j = o ∨ j = d) : False := by
  have hp := integral_connected_quartic_diagonal_pos G hG hI s hs hs2 o
  rw [two_step_chain_quartic_diagonal_zero G o a b c d hab hoc hod hcd ho ha hb] at hp
  exact (lt_irrefl 0) hp
#print axioms Paper7IntroLocalQuartic.integral_connected_no_two_step_degree_two_chain

end Paper7IntroLocalQuartic
