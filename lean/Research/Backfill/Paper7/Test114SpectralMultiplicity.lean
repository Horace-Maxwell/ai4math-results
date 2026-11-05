import Mathlib

/-! The spectral multiplicity bridge is proved before any concrete SunV type is
imported. The finite type, its Fintype instance and its cardinal remain abstract. -/
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 200000
noncomputable section
namespace Paper7Test114Generic

theorem count_map_univ {ι β : Type*} [Fintype ι] [DecidableEq β]
    (f : ι → β) (μ : β) :
    (Finset.univ.val.map f).count μ =
      (Finset.univ.filter (fun i : ι => f i = μ)).card := by
  classical
  simp only [Multiset.count_map, Finset.card, Finset.filter_val, eq_comm]
#print axioms Paper7Test114Generic.count_map_univ

/-- For every finite real Hermitian matrix, algebraic multiplicity equals the
finite dimension of the corresponding eigenspace of its Euclidean linear map. -/
theorem realHermitian_count_roots {ι : Type*} [Fintype ι] [DecidableEq ι]
    (B : Matrix ι ι ℝ) (hB : B.IsHermitian) (μ : ℝ) :
    B.charpoly.roots.count μ =
      Module.finrank ℝ (Module.End.eigenspace (Matrix.toEuclideanLin B) μ) := by
  classical
  rw [hB.roots_charpoly_eq_eigenvalues₀, count_map_univ]
  simpa only [Function.comp_apply, RCLike.ofReal_real_eq_id, id_eq,
    Matrix.IsHermitian.eigenvalues₀] using!
      (Matrix.isSymmetric_toEuclideanLin_iff.mpr hB).card_filter_eigenvalues_eq
        (finrank_euclideanSpace (𝕜 := ℝ) (ι := ι)) μ
#print axioms Paper7Test114Generic.realHermitian_count_roots

end Paper7Test114Generic
