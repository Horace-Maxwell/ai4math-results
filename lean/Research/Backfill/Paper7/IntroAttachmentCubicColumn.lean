import Research.Backfill.Paper7.IntroSubdividedArmLeafMoments

/-! Finite sums of actual adjacency columns give the attachment cubic
column. Each middle-vertex square column is proved from its real two rows. -/
set_option autoImplicit false
noncomputable section
open scoped Classical Matrix BigOperators

namespace Paper7IntroAttachmentMoments
open Matrix SimpleGraph Paper7IntroLocalQuartic Paper7IntroFourExternal

theorem finite_single_sum_apply
    {V : Type} [DecidableEq V] (N : Finset V) (v : V) :
    (∑ x ∈ N, Pi.single x (1 : ℝ)) v = if v ∈ N then 1 else 0 := by
  rw [Finset.sum_apply]
  by_cases hv : v ∈ N
  · rw [ite_eq_left hv]
    calc
      (∑ x ∈ N, (Pi.single x (1 : ℝ) : V → ℝ) v) =
          (Pi.single v (1 : ℝ) : V → ℝ) v := by
        apply Finset.sum_eq_single v
        · intro x _hx hxv
          exact Pi.single_eq_of_ne (M := fun _ : V => ℝ) hxv.symm 1
        · intro hn
          exact (hn hv).elim
      _ = 1 := by simp only [Pi.single_eq_same]
  · rw [ite_eq_right hv]
    apply Finset.sum_eq_zero
    intro x hx
    have hvx : v ≠ x := by
      intro he
      exact hv (he.symm ▸ hx)
    exact Pi.single_eq_of_ne (M := fun _ : V => ℝ) hvx 1
#print axioms Paper7IntroAttachmentMoments.finite_single_sum_apply

theorem adjacency_single_finset
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (a : V) (N : Finset V)
    (hN : G.neighborFinset a = N) :
    G.adjMatrix ℝ *ᵥ Pi.single a 1 = ∑ y ∈ N, Pi.single y 1 := by
  rw [Matrix.mulVec_single_one]
  funext v
  change (if G.Adj v a then (1 : ℝ) else 0) = (∑ y ∈ N, Pi.single y (1 : ℝ)) v
  rw [finite_single_sum_apply]
  have hv : v ∈ N ↔ G.Adj v a := by
    rw [← hN, G.mem_neighborFinset]
    exact G.adj_comm a v
  by_cases hva : G.Adj v a
  · rw [ite_eq_left hva, ite_eq_left (hv.mpr hva)]
  · have hvN : v ∉ N := fun h => hva (hv.mp h)
    rw [ite_eq_right hva, ite_eq_right hvN]
#print axioms Paper7IntroAttachmentMoments.adjacency_single_finset

theorem subdivided_arm_middle_square_column
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (a y l : V)
    (hal : a ≠ l)
    (hy : ∀ z, G.Adj y z ↔ z = a ∨ z = l)
    (hl : ∀ z, G.Adj l z ↔ z = y) :
    (G.adjMatrix ℝ) ^ 2 *ᵥ Pi.single y 1 =
      G.adjMatrix ℝ *ᵥ Pi.single a 1 + Pi.single y 1 := by
  rw [pow_two, ← Matrix.mulVec_mulVec,
    adjacency_single_of_two_neighbors G y a l hal hy, Matrix.mulVec_add,
    adjacency_single_one G l y hl]
#print axioms Paper7IntroAttachmentMoments.subdivided_arm_middle_square_column

theorem subdivided_star_attachment_cubic_column
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (a c : V)
    (Y : Finset V) (leaf : Y → V) (hc : c ∉ Y)
    (hNa : G.neighborFinset a = insert c Y)
    (hal : ∀ i : Y, a ≠ leaf i)
    (hNy : ∀ (i : Y) z, G.Adj i.val z ↔ z = a ∨ z = leaf i)
    (hNl : ∀ (i : Y) z, G.Adj (leaf i) z ↔ z = i.val) :
    G.degree a = Y.card + 1 ∧
      (G.adjMatrix ℝ) ^ 3 *ᵥ Pi.single a 1 =
        (G.adjMatrix ℝ) ^ 2 *ᵥ Pi.single c 1 +
          ((Y.card : ℝ) + 1) • (G.adjMatrix ℝ *ᵥ Pi.single a 1) - Pi.single c 1 := by
  let A := G.adjMatrix ℝ
  let Z : V → ℝ := ∑ y ∈ Y, Pi.single y 1
  have hsum : A *ᵥ Pi.single a 1 = Pi.single c 1 + Z := by
    change G.adjMatrix ℝ *ᵥ Pi.single a 1 = _
    rw [adjacency_single_finset G a (insert c Y) hNa, Finset.sum_insert hc]
  have h2Z : A ^ 2 *ᵥ Z = (Y.card : ℝ) • (A *ᵥ Pi.single a 1) + Z := by
    change A ^ 2 *ᵥ (∑ y ∈ Y, Pi.single y 1) =
      (Y.card : ℝ) • (A *ᵥ Pi.single a 1) + ∑ y ∈ Y, Pi.single y 1
    rw [Matrix.mulVec_sum]
    calc
      (∑ y ∈ Y, A ^ 2 *ᵥ Pi.single y 1) =
          ∑ y ∈ Y, (A *ᵥ Pi.single a 1 + Pi.single y 1) := by
        apply Finset.sum_congr rfl
        intro y hyY
        exact subdivided_arm_middle_square_column G a y (leaf ⟨y, hyY⟩)
          (hal ⟨y, hyY⟩) (hNy ⟨y, hyY⟩) (hNl ⟨y, hyY⟩)
      _ = _ := by
        rw [Finset.sum_add_distrib, Finset.sum_const, ← Nat.cast_smul_eq_nsmul ℝ]
  have hZ : Z = A *ᵥ Pi.single a 1 - Pi.single c 1 := by
    rw [hsum]
    abel
  have h3 := congrArg (fun v : V → ℝ => A ^ 2 *ᵥ v) hsum
  rw [Matrix.mulVec_mulVec, ← pow_succ, Matrix.mulVec_add, h2Z, hZ] at h3
  have hdeg : G.degree a = Y.card + 1 := by
    rw [← G.card_neighborFinset_eq_degree, hNa, Finset.card_insert_of_notMem hc]
  refine ⟨hdeg, ?_⟩
  change A ^ 3 *ᵥ Pi.single a 1 = _
  rw [h3]
  funext v
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring
#print axioms Paper7IntroAttachmentMoments.subdivided_star_attachment_cubic_column

end Paper7IntroAttachmentMoments
