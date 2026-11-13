import Research.TaskG.Data

/-! Explicit spectral coordinates and the tight four-eigenvalue fusion law over F₁₁.
All finite certificates below are checked by the Lean kernel. -/
set_option autoImplicit false

namespace TaskG.Proof
open AxialMSZ.Challenge

private def eigenMatrix (i : Fin 4) : Matrix (Fin 4) (Fin 4) K :=
  fun k r => eig i r k

private def coordMatrix (i : Fin 4) : Matrix (Fin 4) (Fin 4) K :=
  ![ ![ ![1,0,0,0], ![0,7,6,7], ![0,10,5,10], ![0,5,0,6]],
     ![ ![0,1,0,0], ![5,0,5,9], ![6,0,6,3], ![5,0,6,0]],
     ![ ![0,0,1,0], ![6,7,0,7], ![5,10,0,10], ![0,5,0,6]],
     ![ ![0,0,0,1], ![7,6,7,0], ![10,5,10,0], ![5,0,6,0]] ] i

private def leftMatrix (i : Fin 4) : Matrix (Fin 4) (Fin 4) K :=
  fun k j => T i j k

private def fromEig (i : Fin 4) : V →ₗ[K] V := Matrix.toLin' (eigenMatrix i)
private def toEig (i : Fin 4) : V →ₗ[K] V := Matrix.toLin' (coordMatrix i)

private theorem inverse_certificate :
    ∀ i : Fin 4, eigenMatrix i * coordMatrix i = 1 := by
  decide +kernel

private theorem diagonal_certificate :
    ∀ i : Fin 4, coordMatrix i * leftMatrix i = Matrix.diagonal ev * coordMatrix i := by
  decide +kernel

private theorem eigen_certificate :
    ∀ i r : Fin 4, μ (e i) (eig i r) = ev r • eig i r := by
  decide +kernel

private theorem first_certificate : ∀ i : Fin 4, eig i 0 = e i := by
  decide +kernel

private theorem idempotent_certificate : ∀ i : Fin 4, μ (e i) (e i) = e i := by
  decide +kernel

private theorem value_injective : Function.Injective ev := by
  decide +kernel

private instance decStar (l m x : K) : Decidable (x ∈ F.star l m) := by
  dsimp only [F]
  split_ifs <;> infer_instance

private instance decCarrier (x : K) : Decidable (x ∈ F.carrier) := by
  change Decidable (x = 1 ∨ x = 5 ∨ x = 7 ∨ x = 10)
  infer_instance

private theorem carrier_certificate :
    ∀ l : K, l ∈ F.carrier ↔ ∃ r : Fin 4, ev r = l := by
  simp only [F, Set.mem_insert_iff, Set.mem_singleton_iff]
  decide +kernel

private theorem fusion_certificate : ∀ i r s t : Fin 4,
    toEig i (μ (eig i r) (eig i s)) t ≠ 0 → ev t ∈ F.star (ev r) (ev s) := by
  decide +kernel

private theorem matrix_left (i : Fin 4) : μ (e i) = Matrix.toLin' (leftMatrix i) := by
  ext j k
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    norm_num [μ_apply, e, Pi.single_apply, Matrix.toLin'_apply, Matrix.mulVec,
      dotProduct, leftMatrix, T]

private theorem from_to (i : Fin 4) (u : V) : fromEig i (toEig i u) = u := by
  rw [fromEig, toEig, ← Matrix.toLin'_mul_apply, inverse_certificate,
    Matrix.toLin'_one]
  rfl

private theorem from_formula (i : Fin 4) (u : V) :
    fromEig i u = ∑ r : Fin 4, u r • eig i r := by
  ext k
  simp [fromEig, Matrix.toLin'_apply, Matrix.mulVec, dotProduct, eigenMatrix,
    Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mul_comm]

private theorem from_basis (i r : Fin 4) : fromEig i (e r) = eig i r := by
  rw [from_formula]
  simp [e, Pi.single_apply]

private theorem spectral_coordinates (i : Fin 4) (u : V) (r : Fin 4) :
    toEig i (μ (e i) u) r = ev r * toEig i u r := by
  rw [matrix_left]
  change (Matrix.toLin' (coordMatrix i) (Matrix.toLin' (leftMatrix i) u)) r = _
  rw [← Matrix.toLin'_mul_apply, diagonal_certificate, Matrix.toLin'_mul_apply]
  simp [Matrix.toLin'_apply, toEig, Matrix.mulVec_diagonal]

private theorem eigenspace_coordinates (i r : Fin 4) (u : V) :
    u ∈ eigsp μ (e i) (ev r) ↔ ∃ c : K, c • eig i r = u := by
  rw [eigsp, Module.End.mem_eigenspace_iff]
  constructor
  · intro h
    have hz : ∀ s : Fin 4, s ≠ r → toEig i u s = 0 := by
      intro s hs
      have hh := congrFun (congrArg (toEig i) h) s
      rw [spectral_coordinates, map_smul] at hh
      change ev s * toEig i u s = ev r * toEig i u s at hh
      have he : (ev s - ev r) * toEig i u s = 0 := by
        rw [sub_mul, hh, sub_self]
      exact (mul_eq_zero.mp he).resolve_left (sub_ne_zero.mpr (value_injective.ne hs))
    have hc : toEig i u = toEig i u r • e r := by
      ext s
      by_cases hs : s = r
      · subst s; simp
      · simp [e_apply, hs, hz s hs]
    refine ⟨toEig i u r, ?_⟩
    calc
      toEig i u r • eig i r = fromEig i (toEig i u r • e r) := by
        rw [map_smul, from_basis]
      _ = fromEig i (toEig i u) := congrArg (fromEig i) hc.symm
      _ = u := from_to i u
  · rintro ⟨c, rfl⟩
    rw [map_smul, eigen_certificate]
    simp [smul_smul, mul_comm]

private theorem eigen_mem_sum (i : Fin 4) {l : K} {S : Set K}
    (hl : l ∈ S) {u : V} (hu : u ∈ eigsp μ (e i) l) :
    u ∈ eigspSet μ (e i) S := by
  exact (le_iSup_of_le l (le_iSup_of_le hl le_rfl) :
    eigsp μ (e i) l ≤ eigspSet μ (e i) S) hu

private theorem basis_eigen_mem (i r : Fin 4) : eig i r ∈ eigsp μ (e i) (ev r) := by
  rw [eigsp, Module.End.mem_eigenspace_iff]
  exact eigen_certificate i r

private theorem carrier_eigen_mem (r : Fin 4) : ev r ∈ F.carrier :=
  (carrier_certificate (ev r)).mpr ⟨r, rfl⟩

private theorem spectral_top (i : Fin 4) : eigspSet μ (e i) F.carrier = ⊤ := by
  apply top_unique
  intro u _
  rw [← from_to i u, from_formula]
  apply Submodule.sum_mem
  intro r _
  exact Submodule.smul_mem _ _
    (eigen_mem_sum i (carrier_eigen_mem r) (basis_eigen_mem i r))

private theorem fusion_basis (i r s : Fin 4) :
    μ (eig i r) (eig i s) ∈ eigspSet μ (e i) (F.star (ev r) (ev s)) := by
  rw [← from_to i (μ (eig i r) (eig i s)), from_formula]
  apply Submodule.sum_mem
  intro t _
  by_cases hc : toEig i (μ (eig i r) (eig i s)) t = 0
  · simp [hc]
  · exact Submodule.smul_mem _ _
      (eigen_mem_sum i (fusion_certificate i r s t hc) (basis_eigen_mem i t))

private theorem fusion_all (i : Fin 4) :
    ∀ l ∈ F.carrier, ∀ m ∈ F.carrier,
      ∀ u ∈ eigsp μ (e i) l, ∀ v ∈ eigsp μ (e i) m,
        μ u v ∈ eigspSet μ (e i) (F.star l m) := by
  intro l hl m hm u hu v hv
  obtain ⟨r, rfl⟩ := (carrier_certificate l).mp hl
  obtain ⟨s, rfl⟩ := (carrier_certificate m).mp hm
  obtain ⟨c, rfl⟩ := (eigenspace_coordinates i r u).mp hu
  obtain ⟨d, rfl⟩ := (eigenspace_coordinates i s v).mp hv
  simpa [smul_smul, mul_comm] using
    Submodule.smul_mem _ c (Submodule.smul_mem _ d (fusion_basis i r s))

private theorem primitive_one (i : Fin 4) :
    eigsp μ (e i) 1 = Submodule.span K {e i} := by
  ext u
  change (u ∈ eigsp μ (e i) (ev 0)) ↔ _
  rw [eigenspace_coordinates, first_certificate, Submodule.mem_span_singleton]

private theorem axis_nonzero (i : Fin 4) : e i ≠ 0 := by
  intro h
  have hh := congrFun h i
  simp at hh

/-- Each standard basis vector is a primitive axis for the same explicit fusion law. -/
theorem primitive_basis_axis (i : Fin 4) : IsPrimitiveAxis F μ (e i) := by
  exact ⟨⟨axis_nonzero i, idempotent_certificate i, spectral_top i, fusion_all i⟩,
    primitive_one i⟩

/-- The fusion table is finite, symmetric and closed on its four labels. -/
theorem fusion_finite_symmetric : F.IsFiniteSymmetric := by
  refine ⟨Set.toFinite _, ?_, ?_⟩
  · have hh : ∀ l m x : K, x ∈ F.star l m ↔ x ∈ F.star m l := by
      decide +kernel
    intro l m
    exact Set.ext (hh l m)
  · have hh : ∀ l m x : K,
        l ∈ F.carrier → m ∈ F.carrier → x ∈ F.star l m → x ∈ F.carrier := by
      decide +kernel
    intro l hl m hm x hx
    exact hh l m x hl hm hx

/-- The axes span the vector space, hence generate the algebra. -/
theorem basis_generates : gen μ X = ⊤ := by
  apply top_unique
  intro u _
  rw [← basis_sum u]
  apply Submodule.sum_mem
  intro i _
  apply Submodule.smul_mem
  exact Submodule.mem_sInf.mpr fun S hS => hS.1 ⟨i, rfl⟩

/-- Full original primitive axial-algebra predicate, with no added eigenvector assumptions. -/
theorem primitive_axial : IsPrimitiveAxialAlgebra F μ X := by
  refine ⟨μ_comm, ?_, basis_generates⟩
  rintro _ ⟨i, rfl⟩
  exact primitive_basis_axis i

#print axioms TaskG.Proof.primitive_basis_axis
#print axioms TaskG.Proof.fusion_finite_symmetric
#print axioms TaskG.Proof.basis_generates
#print axioms TaskG.Proof.primitive_axial

end TaskG.Proof
