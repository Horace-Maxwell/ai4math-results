import Research.Backfill.Paper7.IntroIntegralRadiusThreeAnnihilator

/-! A pendant C4 forces exact second and fourth moments at its unique
outside neighbor. The outside graph is completely unrestricted. -/
set_option autoImplicit false
noncomputable section
open scoped Classical Matrix BigOperators

namespace Paper7IntroPendantFour
open Matrix SimpleGraph BackfillPaper7.Challenge

theorem adjacency_single_two
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (i a b : V) (hab : a ≠ b)
    (hN : ∀ j, G.Adj i j ↔ j = a ∨ j = b) :
    G.adjMatrix ℝ *ᵥ Pi.single i 1 = Pi.single a 1 + Pi.single b 1 := by
  rw [Matrix.mulVec_single_one]
  funext j
  change (if G.Adj j i then (1 : ℝ) else 0) =
    (Pi.single a (1 : ℝ) : V → ℝ) j + (Pi.single b (1 : ℝ) : V → ℝ) j
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
#print axioms Paper7IntroPendantFour.adjacency_single_two

theorem adjacency_single_three
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (i a b c : V)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hN : ∀ j, G.Adj i j ↔ j = a ∨ j = b ∨ j = c) :
    G.adjMatrix ℝ *ᵥ Pi.single i 1 =
      Pi.single a 1 + Pi.single b 1 + Pi.single c 1 := by
  rw [Matrix.mulVec_single_one]
  funext j
  change (if G.Adj j i then (1 : ℝ) else 0) =
    (Pi.single a (1 : ℝ) : V → ℝ) j + (Pi.single b (1 : ℝ) : V → ℝ) j +
      (Pi.single c (1 : ℝ) : V → ℝ) j
  have hj : G.Adj j i ↔ j = a ∨ j = b ∨ j = c :=
    (G.adj_comm j i).trans (hN j)
  simp only [hj]
  by_cases hja : j = a
  · subst j
    simp [ hab, hac]
  · by_cases hjb : j = b
    · subst j
      simp [ hja, hbc]
    · by_cases hjc : j = c
      · subst j
        simp [ hja, hjb]
      · simp [ hja, hjb, hjc]
#print axioms Paper7IntroPendantFour.adjacency_single_three

theorem symmetric_square_entry
    {V : Type} [Fintype V] [DecidableEq V]
    (A : Matrix V V ℝ) (hA : A.IsSymm) (i j : V) :
    (A ^ 2) i j = (A *ᵥ Pi.single i 1) ⬝ᵥ (A *ᵥ Pi.single j 1) := by
  rw [pow_two, Matrix.mul_apply, Matrix.mulVec_single_one, Matrix.mulVec_single_one]
  change (∑ k, A i k * A k j) = ∑ k, A k i * A k j
  apply Finset.sum_congr rfl
  intro k _
  exact congrArg (fun x => x * A k j) (hA.apply i k).symm
#print axioms Paper7IntroPendantFour.symmetric_square_entry

theorem pendant_four_local_moments
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hI : IsIntegralGraph G)
    (hbound : ∀ x ∈ spec G, |x| ≤ 3)
    (o a b u v : V) (hab : a ≠ b) (hou : o ≠ u) (hav : a ≠ v) (hbv : b ≠ v)
    (ho : ∀ j, G.Adj o j ↔ j = a ∨ j = b)
    (ha : ∀ j, G.Adj a j ↔ j = o ∨ j = u)
    (hb : ∀ j, G.Adj b j ↔ j = o ∨ j = u)
    (hu : ∀ j, G.Adj u j ↔ j = a ∨ j = b ∨ j = v) :
    G.degree v = 6 ∧ ((G.adjMatrix ℝ) ^ 4) v v = 51 := by
  let A := G.adjMatrix ℝ
  have hvo : A *ᵥ Pi.single o 1 = Pi.single a 1 + Pi.single b 1 :=
    adjacency_single_two G o a b hab ho
  have hva : A *ᵥ Pi.single a 1 = Pi.single o 1 + Pi.single u 1 :=
    adjacency_single_two G a o u hou ha
  have hvb : A *ᵥ Pi.single b 1 = Pi.single o 1 + Pi.single u 1 :=
    adjacency_single_two G b o u hou hb
  have hvu : A *ᵥ Pi.single u 1 = Pi.single a 1 + Pi.single b 1 + Pi.single v 1 :=
    adjacency_single_three G u a b v hab hav hbv hu
  have h2o : A ^ 2 *ᵥ Pi.single o 1 = (2 : ℝ) • Pi.single o 1 + (2 : ℝ) • Pi.single u 1 := by
    rw [pow_two, ← Matrix.mulVec_mulVec, hvo, Matrix.mulVec_add, hva, hvb]
    funext j
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have h2a : A ^ 2 *ᵥ Pi.single a 1 =
      (2 : ℝ) • Pi.single a 1 + (2 : ℝ) • Pi.single b 1 + Pi.single v 1 := by
    rw [pow_two, ← Matrix.mulVec_mulVec, hva, Matrix.mulVec_add, hvo, hvu]
    funext j
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have h2b : A ^ 2 *ᵥ Pi.single b 1 =
      (2 : ℝ) • Pi.single a 1 + (2 : ℝ) • Pi.single b 1 + Pi.single v 1 := by
    rw [pow_two, ← Matrix.mulVec_mulVec, hvb, Matrix.mulVec_add, hvo, hvu]
    funext j
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hmove : (A * (A ^ 2 - (4 : ℝ) • 1)) *ᵥ Pi.single o 1 =
      (2 : ℝ) • Pi.single v 1 := by
    rw [← Matrix.mulVec_mulVec, Matrix.sub_mulVec, Matrix.smul_mulVec,
      Matrix.one_mulVec, h2o, Matrix.mulVec_sub, Matrix.mulVec_add,
      Matrix.mulVec_smul, Matrix.mulVec_smul, Matrix.mulVec_smul, hvo, hvu]
    funext j
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hz : radiusThreeFactor A *ᵥ Pi.single v 1 = 0 := by
    have h := congrArg (fun M : Matrix V V ℝ => M *ᵥ Pi.single o 1)
      (integral_radius_three_matrix_annihilator G hI hbound)
    rw [Matrix.zero_mulVec] at h
    change (radiusThreeFactor A * A * (A ^ 2 - (4 : ℝ) • 1)) *ᵥ Pi.single o 1 = 0 at h
    rw [Matrix.mul_assoc, ← Matrix.mulVec_mulVec, hmove, Matrix.mulVec_smul] at h
    funext j
    have hj := congrFun h j
    change 2 * (radiusThreeFactor A *ᵥ Pi.single v 1) j = 0 at hj
    change (radiusThreeFactor A *ᵥ Pi.single v 1) j = 0
    linarith
  have h2av : (A ^ 2) a v = 1 := by
    rw [(G.isSymm_adjMatrix.pow 2).apply v a]
    simpa [Matrix.mulVec_single_one, hav.symm, hbv.symm] using congrFun h2a v
  have h2bv : (A ^ 2) b v = 1 := by
    rw [(G.isSymm_adjMatrix.pow 2).apply v b]
    simpa [Matrix.mulVec_single_one, hav.symm, hbv.symm] using congrFun h2b v
  have h2vv : (A ^ 2) v v = (G.degree v : ℝ) := by
    simpa only [A, pow_two] using (G.adjMatrix_mul_self_apply_self (α := ℝ) v)
  have h4av : (A ^ 4) a v = (G.degree v : ℝ) + 4 := by
    rw [show A ^ 4 = (A ^ 2) ^ 2 from pow_mul A 2 2,
      symmetric_square_entry (A ^ 2) (G.isSymm_adjMatrix.pow 2), h2a]
    simp only [add_dotProduct, smul_dotProduct, single_dotProduct, one_mul,
      Matrix.mulVec_single_one, Matrix.col_apply, h2av, h2bv, h2vv]
    ring
  have he (j : V) : (A ^ 4) j v - 10 * (A ^ 2) j v +
      9 * (1 : Matrix V V ℝ) j v = 0 := by
    have h := congrFun hz j
    simpa only [Matrix.mulVec_single_one, Matrix.col_apply, radiusThreeFactor,
      Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
      Pi.zero_apply] using h
  have hdR : (G.degree v : ℝ) = 6 := by
    have h := he a
    rw [h4av, h2av, Matrix.one_apply_ne hav] at h
    linarith
  have hd : G.degree v = 6 := by exact_mod_cast hdR
  refine ⟨hd, ?_⟩
  have h := he v
  rw [h2vv, hdR, Matrix.one_apply_eq] at h
  linarith
#print axioms Paper7IntroPendantFour.pendant_four_local_moments

end Paper7IntroPendantFour
