import Research.Backfill.Paper8.Challenge
import Research.Backfill.Paper8.Proof.Basic
import Research.SwitchingWalkProfile

/-!
# Paper 8 back-fill (agent `lin`): eigen-components of a vector and Krylov spans

For a real symmetric matrix `A` (as `IsHermitian`): the finset `eigSet` of its eigenvalues, the
component `comp hA s θ ∈ E_θ` of a vector `s` (grouping the expansion of `s` in
`IsHermitian.eigenvectorBasis` by eigenvalue), `s = ∑_θ comp θ`, `P_θ s ≠ 0 ↔ comp θ ≠ 0`, and the
Krylov span: `span {A^j s : j < d'} = span {comp θ}` for `d' ≥ |eigSet|` (Lagrange basis), whose
dimension is the number of `θ` with `P_θ s ≠ 0`.
-/

set_option autoImplicit false

open BackfillPaper8.Challenge Matrix Polynomial

namespace P8Lin

section Spectral

variable {ι : Type} [Fintype ι] [DecidableEq ι] {A : Matrix ι ι ℝ}

/-- The eigenvalues of a real symmetric matrix, as a finset. -/
noncomputable def eigSet (hA : A.IsHermitian) : Finset ℝ := Finset.univ.image hA.eigenvalues

theorem mem_eigSet (hA : A.IsHermitian) (θ : ℝ) : θ ∈ eigSet hA ↔ IsEigenvalue A θ := by
  unfold eigSet IsEigenvalue
  rw [Module.End.hasEigenvalue_iff_mem_spectrum, Matrix.spectrum_toLin',
    hA.spectrum_real_eq_range_eigenvalues]
  simp

theorem eigSet_coe (hA : A.IsHermitian) : {θ : ℝ | IsEigenvalue A θ} = ↑(eigSet hA) := by
  ext θ
  simp [mem_eigSet]

theorem card_eigSet (hA : A.IsHermitian) :
    (eigSet hA).card = {θ : ℝ | IsEigenvalue A θ}.ncard := by
  rw [eigSet_coe hA, Set.ncard_coe_finset]

/-- The component of `s` in the eigenspace `E_θ`. -/
noncomputable def comp (hA : A.IsHermitian) (s : ι → ℝ) (θ : ℝ) : ι → ℝ :=
  ∑ k ∈ Finset.univ.filter (fun k => hA.eigenvalues k = θ),
    hA.eigenvectorBasis.repr (WithLp.toLp 2 s) k • ⇑(hA.eigenvectorBasis k)

theorem comp_eig (hA : A.IsHermitian) (s : ι → ℝ) (θ : ℝ) :
    A *ᵥ comp hA s θ = θ • comp hA s θ := by
  unfold comp
  rw [mulVec_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl (fun k hk => ?_)
  rw [Finset.mem_filter] at hk
  rw [mulVec_smul, hA.mulVec_eigenvectorBasis, hk.2, smul_comm]

theorem sum_comp (hA : A.IsHermitian) (s : ι → ℝ) :
    ∑ θ ∈ eigSet hA, comp hA s θ = s := by
  unfold comp
  rw [Finset.sum_fiberwise_of_maps_to (s := Finset.univ) (t := eigSet hA) (g := hA.eigenvalues)
    (fun k _ => Finset.mem_image_of_mem _ (Finset.mem_univ k))]
  have h := congrArg WithLp.ofLp (hA.eigenvectorBasis.sum_repr (WithLp.toLp 2 s))
  simpa [WithLp.ofLp_sum] using h

theorem comp_eq_zero_of_notMem (hA : A.IsHermitian) (s : ι → ℝ) {θ : ℝ}
    (hθ : θ ∉ eigSet hA) : comp hA s θ = 0 := by
  unfold comp
  apply Finset.sum_eq_zero
  intro k hk
  rw [Finset.mem_filter] at hk
  exact absurd (hk.2 ▸ Finset.mem_image_of_mem _ (Finset.mem_univ k)) hθ

omit [DecidableEq ι] in
/-- Eigenvectors of a symmetric matrix for distinct eigenvalues are orthogonal. -/
theorem dot_eq_zero_of_eig (hA : A.IsSymm) {θ θ' : ℝ} (hne : θ ≠ θ') {x y : ι → ℝ}
    (hx : A *ᵥ x = θ • x) (hy : A *ᵥ y = θ' • y) : x ⬝ᵥ y = 0 := by
  have h1 : x ⬝ᵥ (A *ᵥ y) = (A *ᵥ x) ⬝ᵥ y := by
    rw [dotProduct_mulVec, ← mulVec_transpose, hA.eq]
  rw [hx, hy, dotProduct_smul, smul_dotProduct, smul_eq_mul, smul_eq_mul] at h1
  have h2 : (θ' - θ) * (x ⬝ᵥ y) = 0 := by linarith
  rcases mul_eq_zero.1 h2 with h | h
  · exact absurd (sub_eq_zero.1 h).symm hne
  · exact h

/-- For a `θ`-eigenvector `x`, `x ⬝ s = x ⬝ comp θ`. -/
theorem dot_comp (hA : A.IsHermitian) (s : ι → ℝ) {θ : ℝ} {x : ι → ℝ}
    (hx : A *ᵥ x = θ • x) : x ⬝ᵥ s = x ⬝ᵥ comp hA s θ := by
  conv_lhs => rw [← sum_comp hA s]
  rw [dotProduct_sum]
  by_cases hθ : θ ∈ eigSet hA
  · rw [Finset.sum_eq_single θ]
    · intro θ' _ hne
      exact dot_eq_zero_of_eig hA.isSymm hne.symm hx (comp_eig hA s θ')
    · intro h
      exact absurd hθ h
  · rw [comp_eq_zero_of_notMem hA s hθ, dotProduct_zero]
    apply Finset.sum_eq_zero
    intro θ' hθ'
    have hne : θ ≠ θ' := by
      rintro rfl
      exact hθ hθ'
    exact dot_eq_zero_of_eig hA.isSymm hne hx (comp_eig hA s θ')

/-- `P_θ s ≠ 0` iff the component of `s` in `E_θ` is nonzero. -/
theorem projNe_iff_comp (hA : A.IsHermitian) (s : ι → ℝ) (θ : ℝ) :
    ProjNe A θ s ↔ comp hA s θ ≠ 0 := by
  rw [P8Basic.projNe_iff]
  constructor
  · rintro ⟨x, hx, hxs⟩ h0
    rw [dot_comp hA s hx, h0, dotProduct_zero] at hxs
    exact hxs rfl
  · intro h
    refine ⟨comp hA s θ, comp_eig hA s θ, ?_⟩
    rw [dot_comp hA s (comp_eig hA s θ)]
    exact fun h0 => h (dotProduct_self_eq_zero.1 h0)

/-- `q(A) s = ∑_θ q(θ) comp θ`. -/
theorem aeval_mulVec_eq_sum (hA : A.IsHermitian) (s : ι → ℝ) (q : ℝ[X]) :
    aeval A q *ᵥ s = ∑ θ ∈ eigSet hA, q.eval θ • comp hA s θ := by
  conv_lhs => rw [← sum_comp hA s]
  rw [mulVec_sum]
  refine Finset.sum_congr rfl (fun θ _ => ?_)
  exact SwitchingWalkProfile.aeval_mulVec_of_eigen A θ _ (comp_eig hA s θ) q

/-- The Krylov span `span {A^j s : j < d'}` is the span of the eigen-components of `s`, as soon
as `d'` is at least the number of eigenvalues. -/
theorem span_krylov (hA : A.IsHermitian) (s : ι → ℝ) (d' : ℕ) (hd : (eigSet hA).card ≤ d') :
    Submodule.span ℝ (Set.range (fun j : Fin d' => (A ^ (j : ℕ)) *ᵥ s)) =
      Submodule.span ℝ (Set.range (fun θ : eigSet hA => comp hA s θ)) := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    simp only [SetLike.mem_coe]
    have hj : A ^ (j : ℕ) *ᵥ s = ∑ θ ∈ eigSet hA, (θ ^ (j : ℕ)) • comp hA s θ := by
      have := aeval_mulVec_eq_sum hA s (X ^ (j : ℕ))
      simpa using this
    rw [hj]
    apply Submodule.sum_mem
    intro θ hθ
    apply Submodule.smul_mem
    exact Submodule.subset_span ⟨⟨θ, hθ⟩, rfl⟩
  · rw [Submodule.span_le]
    rintro _ ⟨⟨θ, hθ⟩, rfl⟩
    simp only [SetLike.mem_coe]
    have hinj : Set.InjOn (id : ℝ → ℝ) (eigSet hA) := Set.injOn_id _
    have hq1 : aeval A (Lagrange.basis (eigSet hA) id θ) *ᵥ s = comp hA s θ := by
      rw [aeval_mulVec_eq_sum hA s, Finset.sum_eq_single θ]
      · have := Lagrange.eval_basis_self hinj hθ
        simp only [id] at this
        rw [this, one_smul]
      · intro θ' hθ' hne
        have := Lagrange.eval_basis_of_ne (v := id) (s := eigSet hA) hne.symm hθ'
        simp only [id] at this
        rw [this, zero_smul]
      · intro h
        exact absurd hθ h
    have hdeg : (Lagrange.basis (eigSet hA) id θ).natDegree < d' := by
      rw [Lagrange.natDegree_basis hinj hθ]
      have : 0 < (eigSet hA).card := Finset.card_pos.2 ⟨θ, hθ⟩
      omega
    rw [← hq1, aeval_eq_sum_range' hdeg, sum_mulVec]
    apply Submodule.sum_mem
    intro i hi
    rw [smul_mulVec]
    apply Submodule.smul_mem
    exact Submodule.subset_span ⟨⟨i, Finset.mem_range.1 hi⟩, rfl⟩

/-- The span of the eigen-components has dimension the number of nonzero components. -/
theorem finrank_span_comp (hA : A.IsHermitian) (s : ι → ℝ) :
    Module.finrank ℝ (Submodule.span ℝ (Set.range (fun θ : eigSet hA => comp hA s θ))) =
      ((eigSet hA).filter (fun θ => comp hA s θ ≠ 0)).card := by
  set S := (eigSet hA).filter (fun θ => comp hA s θ ≠ 0) with hS
  have hspan : Submodule.span ℝ (Set.range (fun θ : eigSet hA => comp hA s θ)) =
      Submodule.span ℝ (Set.range (fun θ : S => comp hA s θ)) := by
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨⟨θ, hθ⟩, rfl⟩
      by_cases h0 : comp hA s θ = 0
      · simp only
        rw [h0]
        exact Submodule.zero_mem _
      · exact Submodule.subset_span ⟨⟨θ, Finset.mem_filter.2 ⟨hθ, h0⟩⟩, rfl⟩
    · rw [Submodule.span_le]
      rintro _ ⟨⟨θ, hθ⟩, rfl⟩
      exact Submodule.subset_span ⟨⟨θ, (Finset.mem_filter.1 hθ).1⟩, rfl⟩
  have hli : LinearIndependent ℝ (fun θ : S => comp hA s θ) := by
    apply Module.End.eigenvectors_linearIndependent' (Matrix.toLin' A) (fun θ : S => (θ : ℝ))
      Subtype.val_injective
    intro θ
    rw [Module.End.hasEigenvector_iff]
    exact ⟨(P8Basic.mem_eigenspace_iff A θ _).2 (comp_eig hA s θ), (Finset.mem_filter.1 θ.2).2⟩
  rw [hspan, finrank_span_eq_card hli, Fintype.card_coe]

open Classical in
/-- The dimension of the Krylov span is the number of eigenvalues `θ` with `P_θ s ≠ 0`. -/
theorem finrank_span_krylov (hA : A.IsHermitian) (s : ι → ℝ) (d' : ℕ)
    (hd : (eigSet hA).card ≤ d') :
    Module.finrank ℝ (Submodule.span ℝ (Set.range (fun j : Fin d' => (A ^ (j : ℕ)) *ᵥ s))) =
      ((eigSet hA).filter (fun θ => ProjNe A θ s)).card := by
  rw [span_krylov hA s d' hd, finrank_span_comp]
  congr 1
  apply Finset.filter_congr
  intro θ _
  exact (projNe_iff_comp hA s θ).symm

end Spectral

end P8Lin
