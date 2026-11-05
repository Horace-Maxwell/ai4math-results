import Research.Backfill.Paper7.IntroAttachmentCubicColumn
import Research.Backfill.Paper7.IntroRadiusThreeProjectorAlgebra

/-! Local moments for a true finite leaf star attached through one other
neighbor c. The leaf set Y is an actual Finset of graph vertices. No spectral
bound, norm, degree(c) bound, or moment value is an input hypothesis. -/
set_option autoImplicit false
noncomputable section
open scoped Classical Matrix BigOperators

namespace Paper7IntroPureLeafMoments
open Matrix SimpleGraph Paper7IntroAttachmentMoments
open Paper7IntroLocalQuartic Paper7IntroFourExternal Paper7IntroProjectors

theorem pure_leaf_star_leaf_columns
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (a c : V)
    (Y : Finset V) (hc : c ∉ Y)
    (hNa : G.neighborFinset a = insert c Y)
    (hNl : ∀ y ∈ Y, ∀ z, G.Adj y z ↔ z = a)
    (l : V) (hl : l ∈ Y) :
    G.degree a = Y.card + 1 ∧
      (G.adjMatrix ℝ) ^ 2 *ᵥ Pi.single l 1 =
        Pi.single c 1 + ∑ y ∈ Y, Pi.single y 1 ∧
      (G.adjMatrix ℝ) ^ 3 *ᵥ Pi.single l 1 =
        G.adjMatrix ℝ *ᵥ Pi.single c 1 + (Y.card : ℝ) • Pi.single a 1 := by
  let A := G.adjMatrix ℝ
  have h1 : A *ᵥ Pi.single l 1 = Pi.single a 1 :=
    adjacency_single_one G l a (hNl l hl)
  have hsum : A *ᵥ Pi.single a 1 = Pi.single c 1 + ∑ y ∈ Y, Pi.single y 1 := by
    change G.adjMatrix ℝ *ᵥ Pi.single a 1 = _
    rw [adjacency_single_finset G a (insert c Y) hNa, Finset.sum_insert hc]
  have hY : A *ᵥ (∑ y ∈ Y, Pi.single y 1) = (Y.card : ℝ) • Pi.single a 1 := by
    rw [Matrix.mulVec_sum]
    calc
      (∑ y ∈ Y, A *ᵥ Pi.single y 1) = ∑ _y ∈ Y, (Pi.single a 1 : V → ℝ) := by
        apply Finset.sum_congr rfl
        intro y hy
        exact adjacency_single_one G y a (hNl y hy)
      _ = _ := by rw [Finset.sum_const, ← Nat.cast_smul_eq_nsmul ℝ]
  have h2 : A ^ 2 *ᵥ Pi.single l 1 = Pi.single c 1 + ∑ y ∈ Y, Pi.single y 1 := by
    rw [pow_two, ← Matrix.mulVec_mulVec, h1]
    exact hsum
  have h3 : A ^ 3 *ᵥ Pi.single l 1 = A *ᵥ Pi.single c 1 + (Y.card : ℝ) • Pi.single a 1 := by
    rw [pow_succ', ← Matrix.mulVec_mulVec, h2, Matrix.mulVec_add, hY]
  have hdeg : G.degree a = Y.card + 1 := by
    rw [← G.card_neighborFinset_eq_degree, hNa, Finset.card_insert_of_notMem hc]
  exact ⟨hdeg, h2, h3⟩
#print axioms Paper7IntroPureLeafMoments.pure_leaf_star_leaf_columns

theorem pure_leaf_star_leaf_even_moments
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (a c : V)
    (Y : Finset V) (hc : c ∉ Y)
    (hNa : G.neighborFinset a = insert c Y)
    (hNl : ∀ y ∈ Y, ∀ z, G.Adj y z ↔ z = a)
    (l : V) (hl : l ∈ Y) :
    ((G.adjMatrix ℝ) ^ 2) l l = 1 ∧
      ((G.adjMatrix ℝ) ^ 4) l l = (Y.card : ℝ) + 1 ∧
      ((G.adjMatrix ℝ) ^ 6) l l =
        (G.degree c : ℝ) + (Y.card : ℝ) ^ 2 + 2 * (Y.card : ℝ) := by
  let A := G.adjMatrix ℝ
  have hA : A.IsSymm := G.isSymm_adjMatrix
  have h1 : A *ᵥ Pi.single l 1 = Pi.single a 1 :=
    adjacency_single_one G l a (hNl l hl)
  obtain ⟨hdeg, _h2, h3⟩ := pure_leaf_star_leaf_columns G a c Y hc hNa hNl l hl
  have hdegR : (G.degree a : ℝ) = (Y.card : ℝ) + 1 := by exact_mod_cast hdeg
  have h2a : A ^ 2 *ᵥ Pi.single l 1 = A *ᵥ Pi.single a 1 := by
    rw [pow_two, ← Matrix.mulVec_mulVec, h1]
  have hm2 : (A ^ 2) l l = 1 := by
    rw [symmetric_square_diagonal A hA l, h1]
    simp only [single_dotProduct, one_mul, Pi.single_eq_same]
  have hm4 : (A ^ 4) l l = (Y.card : ℝ) + 1 := by
    rw [show A ^ 4 = (A ^ 2) ^ 2 from pow_mul A 2 2,
      symmetric_square_diagonal (A ^ 2) (hA.pow 2) l, h2a,
      ← symmetric_square_diagonal A hA a]
    change ((G.adjMatrix ℝ) ^ 2) a a = _
    rw [pow_two, G.adjMatrix_mul_self_apply_self, hdegR]
  have hnorm : (A *ᵥ Pi.single c 1) ⬝ᵥ (A *ᵥ Pi.single c 1) =
      (G.degree c : ℝ) := by
    rw [← symmetric_square_diagonal A hA c]
    change ((G.adjMatrix ℝ) ^ 2) c c = _
    rw [pow_two, G.adjMatrix_mul_self_apply_self]
  have hac : G.Adj a c := by
    apply (G.mem_neighborFinset a c).mp
    rw [hNa]
    exact Finset.mem_insert_self c Y
  have hentry : (A *ᵥ Pi.single c 1) a = 1 := by
    rw [Matrix.mulVec_single_one]
    exact ite_eq_left hac
  have hm6 : (A ^ 6) l l = (G.degree c : ℝ) + (Y.card : ℝ) ^ 2 + 2 * (Y.card : ℝ) := by
    rw [show A ^ 6 = (A ^ 3) ^ 2 from pow_mul A 3 2,
      symmetric_square_diagonal (A ^ 3) (hA.pow 3) l, h3]
    change (A *ᵥ Pi.single c 1 + (Y.card : ℝ) • Pi.single a 1) ⬝ᵥ
      (A *ᵥ Pi.single c 1 + (Y.card : ℝ) • Pi.single a 1) =
        (G.degree c : ℝ) + (Y.card : ℝ) ^ 2 + 2 * (Y.card : ℝ)
    simp only [add_dotProduct, dotProduct_add, smul_dotProduct, dotProduct_smul,
      dotProduct_single, single_dotProduct, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul, mul_one, Pi.single_eq_same, hnorm, hentry]
    ring
  exact ⟨hm2, hm4, hm6⟩
#print axioms Paper7IntroPureLeafMoments.pure_leaf_star_leaf_even_moments

theorem pure_leaf_star_leaf_S_diagonal
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (a c : V)
    (Y : Finset V) (hc : c ∉ Y)
    (hNa : G.neighborFinset a = insert c Y)
    (hNl : ∀ y ∈ Y, ∀ z, G.Adj y z ↔ z = a)
    (l : V) (hl : l ∈ Y) :
    radiusThreeS (G.adjMatrix ℝ) l l =
      (G.degree c : ℝ) + (Y.card : ℝ) ^ 2 - 3 * (Y.card : ℝ) - 1 := by
  obtain ⟨hm2, hm4, hm6⟩ := pure_leaf_star_leaf_even_moments G a c Y hc hNa hNl l hl
  simp only [radiusThreeS, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply,
    smul_eq_mul, hm2, hm4, hm6]
  ring
#print axioms Paper7IntroPureLeafMoments.pure_leaf_star_leaf_S_diagonal

theorem pure_three_leaf_star_leaf_moments
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (a c : V)
    (Y : Finset V) (hc : c ∉ Y) (hcard : Y.card = 3)
    (hNa : G.neighborFinset a = insert c Y)
    (hNl : ∀ y ∈ Y, ∀ z, G.Adj y z ↔ z = a)
    (l : V) (hl : l ∈ Y) :
    ((G.adjMatrix ℝ) ^ 2) l l = 1 ∧
      ((G.adjMatrix ℝ) ^ 4) l l = 4 ∧
      ((G.adjMatrix ℝ) ^ 6) l l = (G.degree c : ℝ) + 15 ∧
      radiusThreeS (G.adjMatrix ℝ) l l = (G.degree c : ℝ) - 1 := by
  obtain ⟨hm2, hm4, hm6⟩ := pure_leaf_star_leaf_even_moments G a c Y hc hNa hNl l hl
  have hS := pure_leaf_star_leaf_S_diagonal G a c Y hc hNa hNl l hl
  rw [hcard] at hm4 hm6 hS
  norm_num at hm4 hm6 hS
  exact ⟨hm2, hm4, by linarith, by linarith⟩
#print axioms Paper7IntroPureLeafMoments.pure_three_leaf_star_leaf_moments

end Paper7IntroPureLeafMoments
