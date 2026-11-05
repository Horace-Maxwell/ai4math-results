import Research.Backfill.Paper7.IntroDegreeThreshold

/-! A genuine two-regular induced subgraph has no boundary at spectral cap two. -/
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators Matrix

namespace Paper7IntroHighBranch
open SimpleGraph Matrix BackfillPaper7.Challenge Paper7Comparison Paper7Admissible

theorem Ngt_two_zero_two_regular_no_boundary
    {V W : Type} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hzero : Ngt G 2 = 0)
    (H : SimpleGraph W) [DecidableRel H.Adj] (f : W → V)
    (hf : Function.Injective f) (hAdj : ∀ i j, H.Adj i j ↔ G.Adj (f i) (f j))
    (hd : ∀ i, H.degree i = 2) (z : V) (hz : ∀ i, z ≠ f i) (w : W) :
    ¬G.Adj z (f w) := by
  let I := coordinateInclusion f
  let u : W → ℝ := fun _ => 1
  let y : V → ℝ := I *ᵥ u
  have hI : Iᵀ * (1 : Matrix V V ℝ) * I = 1 := by
    rw [coordinateInclusion_congruence, Matrix.submatrix_one f hf]
  have hnorm : u ⬝ᵥ u = y ⬝ᵥ y := by
    have h := quadratic_rectangular_congruence (1 : Matrix V V ℝ) I u
    simpa only [hI, Paper7Inertia.quadratic_apply, Matrix.one_mulVec] using h
  have hsub : (G.adjMatrix ℝ).submatrix f f = H.adjMatrix ℝ := by
    apply Matrix.ext
    intro i j
    simp only [Matrix.submatrix_apply, SimpleGraph.adjMatrix_apply, hAdj]
  have heH : H.adjMatrix ℝ *ᵥ u = (2 : ℝ) • u := by
    funext i
    change (H.adjMatrix ℝ *ᵥ (fun _ : W => (1 : ℝ))) i = 2 * 1
    rw [SimpleGraph.adjMatrix_mulVec_apply]
    simp only [Finset.sum_const, SimpleGraph.card_neighborFinset_eq_degree,
      nsmul_eq_mul, hd i, Nat.cast_ofNat]
  have hquad : (G.adjMatrix ℝ).toQuadraticForm' y = 2 * (y ⬝ᵥ y) := by
    have h := quadratic_rectangular_congruence (G.adjMatrix ℝ) I u
    rw [coordinateInclusion_congruence, hsub] at h
    rw [← h, Paper7Inertia.quadratic_apply, heH, dotProduct_smul, smul_eq_mul, hnorm]
  have hA := Paper7Spectrum.realAdjHermitian G
  have hupper (a : V → ℝ) :
      (G.adjMatrix ℝ).toQuadraticForm' a ≤ 2 * (a ⬝ᵥ a) := by
    exact hermitian_quadratic_upper (G.adjMatrix ℝ) hA 2
      (fun i => Ngt_zero_spectrum_le G 2 hzero (hA.eigenvalues i)
        (eigenvalue_mem_eigs (G.adjMatrix ℝ) hA i)) a
  have heG : G.adjMatrix ℝ *ᵥ y = (2 : ℝ) • y :=
    eigen_of_quadratic_equality (G.adjMatrix ℝ) hA 2 hupper y hquad
  have hy : ∀ i, 0 ≤ y i := by
    intro i
    change 0 ≤ ∑ j, coordinateInclusion f i j * (1 : ℝ)
    apply Finset.sum_nonneg
    intro j _hj
    change 0 ≤ (if i = f j then (1 : ℝ) else 0) * 1
    split_ifs <;> norm_num
  have hyz : y z = 0 := by
    change (∑ j, coordinateInclusion f z j * (1 : ℝ)) = 0
    apply Finset.sum_eq_zero
    intro j _hj
    change (if z = f j then (1 : ℝ) else 0) * 1 = 0
    rw [ite_eq_right (hz j), zero_mul]
  have hyw : y (f w) = 1 := coordinateInclusion_apply f hf u w
  intro hzw
  have hrow : (G.adjMatrix ℝ *ᵥ y) z = 0 := by
    rw [heG]
    change 2 * y z = 0
    rw [hyz, mul_zero]
  have h := graph_nonnegative_neighbor_zero G y hy z (f w) hzw hrow
  rw [hyw] at h
  norm_num at h
#print axioms Paper7IntroHighBranch.Ngt_two_zero_two_regular_no_boundary

end Paper7IntroHighBranch
