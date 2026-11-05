import Research.Backfill.Paper7.IntroAttachmentEvenMoments

/-! Attachment moments of an actual pure leaf star. The finite leaf rows
give the square and cube columns, including when the leaf set is empty.
The cubic cross term is derived from these same columns, rather than assumed.
No subdivided-arm identity, spectral restriction, or numerical moment is used. -/
set_option autoImplicit false
noncomputable section
open scoped Classical Matrix BigOperators

namespace Paper7IntroPureLeafMoments
open Matrix SimpleGraph Paper7IntroAttachmentMoments
open Paper7IntroLocalQuartic Paper7IntroFourExternal

theorem pure_leaf_star_attachment_columns
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (a c : V)
    (Y : Finset V) (hc : c ∉ Y)
    (hNa : G.neighborFinset a = insert c Y)
    (hNl : ∀ y ∈ Y, ∀ z, G.Adj y z ↔ z = a) :
    G.degree a = Y.card + 1 ∧
      (G.adjMatrix ℝ) ^ 2 *ᵥ Pi.single a 1 =
        G.adjMatrix ℝ *ᵥ Pi.single c 1 + (Y.card : ℝ) • Pi.single a 1 ∧
      (G.adjMatrix ℝ) ^ 3 *ᵥ Pi.single a 1 =
        (G.adjMatrix ℝ) ^ 2 *ᵥ Pi.single c 1 +
          (Y.card : ℝ) • (G.adjMatrix ℝ *ᵥ Pi.single a 1) := by
  let A := G.adjMatrix ℝ
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
  have h2 : A ^ 2 *ᵥ Pi.single a 1 = A *ᵥ Pi.single c 1 + (Y.card : ℝ) • Pi.single a 1 := by
    rw [pow_two, ← Matrix.mulVec_mulVec, hsum, Matrix.mulVec_add, hY]
  have h3 : A ^ 3 *ᵥ Pi.single a 1 = A ^ 2 *ᵥ Pi.single c 1 +
      (Y.card : ℝ) • (A *ᵥ Pi.single a 1) := by
    rw [pow_succ', ← Matrix.mulVec_mulVec, h2, Matrix.mulVec_add, Matrix.mulVec_smul,
      Matrix.mulVec_mulVec, ← pow_two]
  have hdeg : G.degree a = Y.card + 1 := by
    rw [← G.card_neighborFinset_eq_degree, hNa, Finset.card_insert_of_notMem hc]
  exact ⟨hdeg, h2, h3⟩
#print axioms Paper7IntroPureLeafMoments.pure_leaf_star_attachment_columns

theorem pure_leaf_star_attachment_even_moments
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (a c : V)
    (Y : Finset V) (hc : c ∉ Y)
    (hNa : G.neighborFinset a = insert c Y)
    (hNl : ∀ y ∈ Y, ∀ z, G.Adj y z ↔ z = a) :
    ((G.adjMatrix ℝ) ^ 4) a a =
        (Y.card : ℝ) ^ 2 + 2 * (Y.card : ℝ) + (G.degree c : ℝ) ∧
      ((G.adjMatrix ℝ) ^ 6) a a = ((G.adjMatrix ℝ) ^ 4) c c +
        (Y.card : ℝ) ^ 3 + 3 * (Y.card : ℝ) ^ 2 +
          2 * (Y.card : ℝ) * (G.degree c : ℝ) := by
  let A := G.adjMatrix ℝ
  let ea : V → ℝ := Pi.single a 1
  let ec : V → ℝ := Pi.single c 1
  let u : V → ℝ := A *ᵥ ea
  let v : V → ℝ := A ^ 2 *ᵥ ec
  let m : ℝ := Y.card
  let d : ℝ := G.degree c
  have hA : A.IsSymm := G.isSymm_adjMatrix
  obtain ⟨hdeg, h2, h3⟩ := pure_leaf_star_attachment_columns G a c Y hc hNa hNl
  change A ^ 2 *ᵥ ea = A *ᵥ ec + m • ea at h2
  change A ^ 3 *ᵥ ea = v + m • u at h3
  have hdegR : (G.degree a : ℝ) = m + 1 := by
    change (G.degree a : ℝ) = (Y.card : ℝ) + 1
    exact_mod_cast hdeg
  have hac : G.Adj a c := by
    apply (G.mem_neighborFinset a c).mp
    rw [hNa]
    exact Finset.mem_insert_self c Y
  have hnormc : (A *ᵥ ec) ⬝ᵥ (A *ᵥ ec) = d := by
    change (A *ᵥ Pi.single c 1) ⬝ᵥ (A *ᵥ Pi.single c 1) = _
    rw [← symmetric_square_diagonal A hA c]
    change ((G.adjMatrix ℝ) ^ 2) c c = (G.degree c : ℝ)
    rw [pow_two, G.adjMatrix_mul_self_apply_self]
  have heaea : ea ⬝ᵥ ea = 1 := by
    simp only [ea, single_dotProduct, one_mul, Pi.single_eq_same]
  have hace : (A *ᵥ ec) ⬝ᵥ ea = 1 := by
    change (A *ᵥ Pi.single c 1) ⬝ᵥ Pi.single a 1 = 1
    rw [dotProduct_single, mul_one, Matrix.mulVec_single_one]
    exact ite_eq_left hac
  have heac : ea ⬝ᵥ (A *ᵥ ec) = 1 := by rw [dotProduct_comm]; exact hace
  have huu : u ⬝ᵥ u = m + 1 := by
    change (A *ᵥ Pi.single a 1) ⬝ᵥ (A *ᵥ Pi.single a 1) = _
    rw [← symmetric_square_diagonal A hA a]
    change ((G.adjMatrix ℝ) ^ 2) a a = m + 1
    rw [pow_two, G.adjMatrix_mul_self_apply_self, hdegR]
  have hvv : v ⬝ᵥ v = (A ^ 4) c c :=
    symmetric_power_columns_dot A hA 2 2 c c
  have huv : u ⬝ᵥ v = m + d := by
    calc
      u ⬝ᵥ v = (A ^ 3) a c := by
        simpa only [u, v, ea, ec, pow_one] using symmetric_power_columns_dot A hA 1 2 a c
      _ = (A ^ 2 *ᵥ ea) ⬝ᵥ (A *ᵥ ec) := by
        symm
        simpa only [ea, ec, pow_one] using symmetric_power_columns_dot A hA 2 1 a c
      _ = (A *ᵥ ec + m • ea) ⬝ᵥ (A *ᵥ ec) :=
        congrArg (fun z : V → ℝ => z ⬝ᵥ (A *ᵥ ec)) h2
      _ = m + d := by
        rw [add_dotProduct, smul_dotProduct, hnormc, heac]
        simp only [smul_eq_mul]
        ring
  have hvu : v ⬝ᵥ u = m + d := by rw [dotProduct_comm]; exact huv
  have hm4 : (A ^ 4) a a = m ^ 2 + 2 * m + d := by
    rw [show A ^ 4 = (A ^ 2) ^ 2 from pow_mul A 2 2,
      symmetric_square_diagonal (A ^ 2) (hA.pow 2) a]
    change (A ^ 2 *ᵥ ea) ⬝ᵥ (A ^ 2 *ᵥ ea) = m ^ 2 + 2 * m + d
    rw [h2]
    simp only [add_dotProduct, dotProduct_add, smul_dotProduct, dotProduct_smul, smul_eq_mul]
    rw [hnormc, hace, heac, heaea]
    ring
  have hm6 : (A ^ 6) a a = (A ^ 4) c c + m ^ 3 + 3 * m ^ 2 + 2 * m * d := by
    rw [show A ^ 6 = (A ^ 3) ^ 2 from pow_mul A 3 2,
      symmetric_square_diagonal (A ^ 3) (hA.pow 3) a]
    change (A ^ 3 *ᵥ ea) ⬝ᵥ (A ^ 3 *ᵥ ea) = _
    rw [h3]
    simp only [add_dotProduct, dotProduct_add, smul_dotProduct, dotProduct_smul, smul_eq_mul]
    rw [hvv, huu, huv, hvu]
    ring
  exact ⟨hm4, hm6⟩
#print axioms Paper7IntroPureLeafMoments.pure_leaf_star_attachment_even_moments

end Paper7IntroPureLeafMoments
