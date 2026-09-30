import Research.Backfill.Paper8.Challenge

/-!
# Paper 8 back-fill: shared facts about `T(a)`, eigenspaces and goodness

Written by the coordinator for all proof agents (namespace `P8Basic`). Contents: adjacency of
`treeT a` case by case, the formula for `A x` (paper, equation (3.1)), sums over the vertex type
`TV a`, symmetry of `adjT a`, eigenvalues and eigenspaces of `Matrix.toLin'` through `mulVec`, and
`ProjNe`/`IsGood` in terms of dot products with eigenvectors.
-/

set_option autoImplicit false

open BackfillPaper8.Challenge Matrix

namespace P8Basic

section Tree

variable {k : ℕ} (a : Fin k → ℕ)

/-- Sum over the vertices of `T(a)`: centre, then branch by branch. -/
theorem sum_TV {M : Type*} [AddCommMonoid M] (f : TV a → M) :
    ∑ v, f v = f none + ∑ i, (f (some ⟨i, none⟩) + ∑ j, f (some ⟨i, some j⟩)) := by
  rw [Fintype.sum_option, Fintype.sum_sigma]
  congr 1
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Fintype.sum_option]

@[simp] theorem adj_c_c : ¬ (treeT a).Adj none none := (treeT a).loopless.irrefl _

@[simp] theorem adj_c_v (i : Fin k) : (treeT a).Adj none (some ⟨i, none⟩) := by
  simp [treeT, parentB]

@[simp] theorem adj_c_l (i : Fin k) (j : Fin (a i)) :
    ¬ (treeT a).Adj none (some ⟨i, some j⟩) := by
  simp [treeT, parentB]

@[simp] theorem adj_v_c (i : Fin k) : (treeT a).Adj (some ⟨i, none⟩) none :=
  (adj_c_v a i).symm

@[simp] theorem adj_v_v (i i' : Fin k) :
    ¬ (treeT a).Adj (some ⟨i, none⟩) (some ⟨i', none⟩) := by
  simp [treeT, parentB]

@[simp] theorem adj_v_l (i i' : Fin k) (j : Fin (a i')) :
    (treeT a).Adj (some ⟨i, none⟩) (some ⟨i', some j⟩) ↔ i = i' := by
  constructor
  · intro h
    rw [treeT, SimpleGraph.fromRel_adj] at h
    rcases h.2 with h' | h'
    · simpa [parentB] using h'
    · simp [parentB] at h'
  · rintro rfl
    rw [treeT, SimpleGraph.fromRel_adj]
    refine ⟨?_, Or.inl (by simp [parentB])⟩
    intro h
    simp at h

@[simp] theorem adj_l_c (i : Fin k) (j : Fin (a i)) :
    ¬ (treeT a).Adj (some ⟨i, some j⟩) none := fun h => adj_c_l a i j h.symm

@[simp] theorem adj_l_v (i : Fin k) (j : Fin (a i)) (i' : Fin k) :
    (treeT a).Adj (some ⟨i, some j⟩) (some ⟨i', none⟩) ↔ i' = i := by
  rw [SimpleGraph.adj_comm]
  exact adj_v_l a i' i j

@[simp] theorem adj_l_l (i : Fin k) (j : Fin (a i)) (i' : Fin k) (j' : Fin (a i')) :
    ¬ (treeT a).Adj (some ⟨i, some j⟩) (some ⟨i', some j'⟩) := by
  simp [treeT, parentB]

theorem adjT_apply (x y : TV a) : adjT a x y = if (treeT a).Adj x y then 1 else 0 :=
  SimpleGraph.adjMatrix_apply _ _ _

theorem adjT_isSymm : (adjT a).IsSymm :=
  SimpleGraph.isSymm_adjMatrix _

/-- `(A x)_c = ∑_i x_{v_i}`. -/
theorem mulVec_c (x : TV a → ℝ) : (adjT a *ᵥ x) none = ∑ i, x (some ⟨i, none⟩) := by
  simp only [mulVec, dotProduct, adjT_apply]
  rw [sum_TV]
  simp

/-- `(A x)_{v_i} = x_c + ∑_{ℓ ∈ L_i} x_ℓ`. -/
theorem mulVec_v (x : TV a → ℝ) (i : Fin k) :
    (adjT a *ᵥ x) (some ⟨i, none⟩) = x none + ∑ j, x (some ⟨i, some j⟩) := by
  simp only [mulVec, dotProduct, adjT_apply]
  rw [sum_TV]
  simp only [adj_v_c, adj_v_v, adj_v_l, ite_true, ite_false, one_mul, zero_mul, zero_add]
  congr 1
  rw [Finset.sum_eq_single i]
  · simp
  · intro i' _ hi'
    simp [Ne.symm hi']
  · simp

/-- `(A x)_ℓ = x_{v_i}` for `ℓ ∈ L_i`. -/
theorem mulVec_l (x : TV a → ℝ) (i : Fin k) (j : Fin (a i)) :
    (adjT a *ᵥ x) (some ⟨i, some j⟩) = x (some ⟨i, none⟩) := by
  simp only [mulVec, dotProduct, adjT_apply]
  rw [sum_TV]
  simp only [adj_l_c, adj_l_v, adj_l_l, ite_false, zero_mul, zero_add, Finset.sum_const_zero,
    add_zero]
  rw [Finset.sum_eq_single i]
  · simp
  · intro i' _ hi'
    simp [hi']
  · simp

/-- `A x = θ x` for `T(a)`, coordinatewise (equation (3.1) of the paper). -/
theorem mulVec_eq_smul_iff (x : TV a → ℝ) (θ : ℝ) :
    adjT a *ᵥ x = θ • x ↔
      θ * x none = ∑ i, x (some ⟨i, none⟩) ∧
      (∀ i, θ * x (some ⟨i, none⟩) = x none + ∑ j, x (some ⟨i, some j⟩)) ∧
      (∀ i j, θ * x (some ⟨i, some j⟩) = x (some ⟨i, none⟩)) := by
  constructor
  · intro h
    refine ⟨?_, fun i => ?_, fun i j => ?_⟩
    · have := congrFun h none
      rw [mulVec_c] at this
      simp [this]
    · have := congrFun h (some ⟨i, none⟩)
      rw [mulVec_v] at this
      simp [this]
    · have := congrFun h (some ⟨i, some j⟩)
      rw [mulVec_l] at this
      simp [this]
  · rintro ⟨h0, h1, h2⟩
    funext v
    rcases v with _ | ⟨i, _ | j⟩
    · rw [mulVec_c]; simp [h0]
    · rw [mulVec_v]; simp [h1 i]
    · rw [mulVec_l]; simp [h2 i j]

theorem card_TV : Fintype.card (TV a) = 1 + k + ∑ i, a i := by
  simp only [TV, Fintype.card_option, Fintype.card_sigma]
  rw [Finset.sum_add_distrib]
  simp
  ring

end Tree

section Spectral

variable {n : Type} [Fintype n] [DecidableEq n]

theorem mem_eigenspace_iff (M : Matrix n n ℝ) (θ : ℝ) (x : n → ℝ) :
    x ∈ Module.End.eigenspace (Matrix.toLin' M) θ ↔ M *ᵥ x = θ • x := by
  rw [Module.End.mem_eigenspace_iff, Matrix.toLin'_apply]

theorem isEigenvalue_iff (M : Matrix n n ℝ) (θ : ℝ) :
    IsEigenvalue M θ ↔ ∃ x : n → ℝ, x ≠ 0 ∧ M *ᵥ x = θ • x := by
  unfold IsEigenvalue
  rw [Module.End.hasEigenvalue_iff]
  constructor
  · intro h
    obtain ⟨x, hx, hne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h
    exact ⟨x, hne, (mem_eigenspace_iff M θ x).1 hx⟩
  · rintro ⟨x, hne, hx⟩ hbot
    have hmem : x ∈ Module.End.eigenspace (Matrix.toLin' M) θ := (mem_eigenspace_iff M θ x).2 hx
    rw [hbot] at hmem
    exact hne ((Submodule.mem_bot ℝ).1 hmem)

theorem mem_eigenspace_euclidean_iff (M : Matrix n n ℝ) (θ : ℝ) (x : EuclideanSpace ℝ n) :
    x ∈ Module.End.eigenspace (Matrix.toEuclideanLin M) θ ↔
      M *ᵥ (WithLp.ofLp x) = θ • WithLp.ofLp x := by
  rw [Module.End.mem_eigenspace_iff, Matrix.toLpLin_apply]
  constructor
  · intro h
    have := congrArg WithLp.ofLp h
    simpa using this
  · intro h
    apply (WithLp.linearEquiv 2 ℝ (n → ℝ)).injective
    simpa using h

/-- `P_θ s ≠ 0` iff some eigenvector `x` of `θ` (with `A x = θ x`) has `x ⬝ s ≠ 0`. -/
theorem projNe_iff (A : Matrix n n ℝ) (θ : ℝ) (s : n → ℝ) :
    ProjNe A θ s ↔ ∃ x : n → ℝ, A *ᵥ x = θ • x ∧ x ⬝ᵥ s ≠ 0 := by
  unfold ProjNe
  rw [Ne, Submodule.starProjection_apply_eq_zero_iff, Submodule.mem_orthogonal]
  push Not
  constructor
  · rintro ⟨u, hu, hne⟩
    refine ⟨WithLp.ofLp u, (mem_eigenspace_euclidean_iff A θ u).1 hu, ?_⟩
    intro h0
    apply hne
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    simpa [dotProduct_comm] using h0
  · rintro ⟨x, hx, hne⟩
    refine ⟨WithLp.toLp 2 x, (mem_eigenspace_euclidean_iff A θ _).2 (by simpa using hx), ?_⟩
    intro h0
    apply hne
    rw [EuclideanSpace.inner_eq_star_dotProduct] at h0
    simpa [dotProduct_comm] using h0

/-- `s` is good iff for every eigenvalue some eigenvector has nonzero dot product with `s`. -/
theorem isGood_iff (A : Matrix n n ℝ) (s : n → ℝ) :
    IsGood A s ↔ ∀ θ : ℝ, IsEigenvalue A θ → ∃ x : n → ℝ, A *ᵥ x = θ • x ∧ x ⬝ᵥ s ≠ 0 := by
  unfold IsGood
  exact forall_congr' fun θ => imp_congr_right fun _ => projNe_iff A θ s

end Spectral

end P8Basic
