import Research.Backfill.Paper7.IntroPureLeafStarAttachmentMoments

/-! Moments of the sum of all actual leaf basis vectors. The norm uses the
actual finite set, so distinct leaf zero modes are never identified. -/
set_option autoImplicit false
noncomputable section
open scoped Classical Matrix BigOperators

namespace Paper7IntroPureLeafMoments
open Matrix SimpleGraph Paper7IntroAttachmentMoments
open Paper7IntroLocalQuartic Paper7IntroFourExternal

theorem pure_leaf_star_leaf_sum_even_moments
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (a c : V)
    (Y : Finset V) (hc : c ∉ Y)
    (hNa : G.neighborFinset a = insert c Y)
    (hNl : ∀ y ∈ Y, ∀ z, G.Adj y z ↔ z = a) :
    let A := G.adjMatrix ℝ
    let L : V → ℝ := ∑ y ∈ Y, Pi.single y 1
    L ⬝ᵥ L = (Y.card : ℝ) ∧
      A *ᵥ L = (Y.card : ℝ) • Pi.single a 1 ∧
      L ⬝ᵥ A ^ 2 *ᵥ L = (Y.card : ℝ) ^ 2 ∧
      L ⬝ᵥ A ^ 4 *ᵥ L = (Y.card : ℝ) ^ 2 * ((Y.card : ℝ) + 1) ∧
      L ⬝ᵥ A ^ 6 *ᵥ L = (Y.card : ℝ) ^ 2 *
        ((Y.card : ℝ) ^ 2 + 2 * (Y.card : ℝ) + (G.degree c : ℝ)) := by
  let A := G.adjMatrix ℝ
  let L : V → ℝ := ∑ y ∈ Y, Pi.single y 1
  let m : ℝ := Y.card
  let d : ℝ := G.degree c
  have hA : A.IsSymm := G.isSymm_adjMatrix
  have hLv (y : V) (hy : y ∈ Y) : L y = 1 := by
    change (∑ z ∈ Y, Pi.single z (1 : ℝ)) y = 1
    rw [Finset.sum_apply, Finset.sum_pi_single, ite_eq_left hy]
  have hL0 : L ⬝ᵥ L = m := by
    change (∑ y ∈ Y, Pi.single y (1 : ℝ)) ⬝ᵥ L = m
    rw [sum_dotProduct]
    calc
      (∑ y ∈ Y, Pi.single y 1 ⬝ᵥ L) = ∑ _y ∈ Y, (1 : ℝ) := by
        apply Finset.sum_congr rfl
        intro y hy
        rw [single_dotProduct, one_mul, hLv y hy]
      _ = m := by simp [m]
  have hAL : A *ᵥ L = m • Pi.single a 1 := by
    change A *ᵥ (∑ y ∈ Y, Pi.single y 1) = (Y.card : ℝ) • Pi.single a 1
    rw [Matrix.mulVec_sum]
    calc
      (∑ y ∈ Y, A *ᵥ Pi.single y 1) = ∑ _y ∈ Y, (Pi.single a 1 : V → ℝ) := by
        apply Finset.sum_congr rfl
        intro y hy
        exact adjacency_single_one G y a (hNl y hy)
      _ = _ := by rw [Finset.sum_const, ← Nat.cast_smul_eq_nsmul ℝ]
  have hstep (k : ℕ) : A ^ (k + 1) *ᵥ L = m • (A ^ k *ᵥ Pi.single a 1) := by
    rw [pow_succ, ← Matrix.mulVec_mulVec, hAL, Matrix.mulVec_smul]
  have hnorm (k : ℕ) : L ⬝ᵥ A ^ (k + k) *ᵥ L =
      (A ^ k *ᵥ L) ⬝ᵥ (A ^ k *ᵥ L) := by
    rw [pow_add, ← Matrix.mulVec_mulVec]
    exact (hA.pow k).dotProduct_mulVec_comm
  obtain ⟨hdeg, _hcol2, _hcol3⟩ := pure_leaf_star_attachment_columns G a c Y hc hNa hNl
  have hdegR : (G.degree a : ℝ) = m + 1 := by
    change (G.degree a : ℝ) = (Y.card : ℝ) + 1
    exact_mod_cast hdeg
  obtain ⟨hm4a, _hm6a⟩ := pure_leaf_star_attachment_even_moments G a c Y hc hNa hNl
  have hea : (Pi.single a (1 : ℝ) : V → ℝ) ⬝ᵥ Pi.single a 1 = 1 := by
    simp only [single_dotProduct, one_mul, Pi.single_eq_same]
  have hAa : (A *ᵥ Pi.single a 1) ⬝ᵥ (A *ᵥ Pi.single a 1) = m + 1 := by
    rw [← symmetric_square_diagonal A hA a]
    change ((G.adjMatrix ℝ) ^ 2) a a = m + 1
    rw [pow_two, G.adjMatrix_mul_self_apply_self, hdegR]
  have hA2a : (A ^ 2 *ᵥ Pi.single a 1) ⬝ᵥ (A ^ 2 *ᵥ Pi.single a 1) =
      m ^ 2 + 2 * m + d := by
    calc
      _ = (A ^ 4) a a := symmetric_power_columns_dot A hA 2 2 a a
      _ = m ^ 2 + 2 * m + d := hm4a
  have hL2 : L ⬝ᵥ A ^ 2 *ᵥ L = m ^ 2 := by
    rw [hnorm 1, pow_one, hAL, smul_dotProduct, dotProduct_smul, hea]
    simp only [smul_eq_mul]
    ring
  have hL4 : L ⬝ᵥ A ^ 4 *ᵥ L = m ^ 2 * (m + 1) := by
    rw [hnorm 2, hstep 1, pow_one, smul_dotProduct, dotProduct_smul, hAa]
    simp only [smul_eq_mul]
    ring
  have hL6 : L ⬝ᵥ A ^ 6 *ᵥ L = m ^ 2 * (m ^ 2 + 2 * m + d) := by
    rw [hnorm 3, hstep 2, smul_dotProduct, dotProduct_smul, hA2a]
    simp only [smul_eq_mul]
    ring
  exact ⟨hL0, hAL, hL2, hL4, hL6⟩
#print axioms Paper7IntroPureLeafMoments.pure_leaf_star_leaf_sum_even_moments

end Paper7IntroPureLeafMoments
