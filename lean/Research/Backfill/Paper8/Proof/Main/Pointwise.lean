import Research.Backfill.Paper8.Proof.Main.Eigen

/-!
# Paper 8, agent `main`: per-eigenvalue form of condition (S) (`Lemma_3_2_pointwise`)

For a switching `s`, `D_s² = 1`, so `x` is an eigenvector of `D_s A D_s` iff `y = s ⊙ x` is one of
`A`, and `∑ x = y ⬝ s` (proved directly, without `Lemma_2_1`). For a secular `θ` of `T(a)` every
eigenvector `y` has `y ⬝ s = y_c G_s(θ)`, and `x^θ` (with `x^θ_c = 1`) is one; hence `θ` is a main
eigenvalue of `D_s A D_s` iff `G_s(θ) ≠ 0`.
-/

set_option autoImplicit false

open BackfillPaper8.Challenge Matrix

namespace P8Main

theorem mul_self_of_switching {n : Type} {s : n → ℝ} (hs : IsSwitching s) (i : n) :
    s i * s i = 1 := by
  rcases hs i with h | h <;> rw [h] <;> norm_num

section Switch

variable {n : Type} [Fintype n] [DecidableEq n]

/-- `(D_s A D_s x)_i = s_i (A (s ⊙ x))_i`. -/
theorem switchMatrix_mulVec_apply (A : Matrix n n ℝ) (s x : n → ℝ) (i : n) :
    (switchMatrix A s *ᵥ x) i = s i * (A *ᵥ (fun j => s j * x j)) i := by
  have hD : diagonal s *ᵥ x = fun j => s j * x j := funext (mulVec_diagonal s x)
  rw [switchMatrix, ← mulVec_mulVec, ← mulVec_mulVec, mulVec_diagonal, hD]

/-- `D_s A D_s x = θ x ↔ A (s ⊙ x) = θ (s ⊙ x)`. -/
theorem switchMatrix_eigen_iff (A : Matrix n n ℝ) {s : n → ℝ} (hs : IsSwitching s) (θ : ℝ)
    (x : n → ℝ) :
    switchMatrix A s *ᵥ x = θ • x ↔
      A *ᵥ (fun j => s j * x j) = θ • (fun j => s j * x j) := by
  constructor
  · intro h
    funext i
    have hi := congrFun h i
    rw [switchMatrix_mulVec_apply, Pi.smul_apply, smul_eq_mul] at hi
    rw [Pi.smul_apply, smul_eq_mul]
    linear_combination s i * hi -
      (A *ᵥ (fun j => s j * x j)) i * mul_self_of_switching hs i
  · intro h
    funext i
    rw [switchMatrix_mulVec_apply, h, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul]
    linear_combination (θ * x i) * mul_self_of_switching hs i

/-- `θ` is a main eigenvalue of `D_s A D_s` iff some eigenvector `y` of `A` for `θ` has
`y ⬝ s ≠ 0`. -/
theorem isMainEigenvalue_switch_iff (A : Matrix n n ℝ) {s : n → ℝ} (hs : IsSwitching s)
    (θ : ℝ) :
    IsMainEigenvalue (switchMatrix A s) θ ↔ ∃ y : n → ℝ, A *ᵥ y = θ • y ∧ y ⬝ᵥ s ≠ 0 := by
  constructor
  · rintro ⟨_, x, hx, hsum⟩
    rw [P8Basic.mem_eigenspace_iff, switchMatrix_eigen_iff A hs] at hx
    refine ⟨_, hx, ?_⟩
    have hdot : (fun j => s j * x j) ⬝ᵥ s = ∑ i, x i := by
      simp only [dotProduct]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      linear_combination x i * mul_self_of_switching hs i
    rw [hdot]
    exact hsum
  · rintro ⟨y, hy, hys⟩
    set x : n → ℝ := fun j => s j * y j with hxdef
    have hsx : (fun j => s j * x j) = y := by
      funext j
      simp only [hxdef]
      linear_combination y j * mul_self_of_switching hs j
    have hx : switchMatrix A s *ᵥ x = θ • x := by
      rw [switchMatrix_eigen_iff A hs, hsx]
      exact hy
    have hsum : ∑ i, x i ≠ 0 := by
      intro h0
      apply hys
      rw [← h0]
      simp only [dotProduct, hxdef]
      exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)
    have hx0 : x ≠ 0 := by
      intro h0
      apply hsum
      rw [h0]
      simp
    exact ⟨(P8Basic.isEigenvalue_iff _ _).2 ⟨x, hx0, hx⟩, x,
      (P8Basic.mem_eigenspace_iff _ _ _).2 hx, hsum⟩

end Switch

/-- Per-eigenvalue form of (S): a secular `θ` is a main eigenvalue of `D_s A D_s` iff
`G_s(θ) ≠ 0`. -/
theorem lemma_3_2_pointwise {k : ℕ} (a : Fin k → ℕ) (s : TV a → ℝ) (hs : IsSwitching s)
    (θ : ℝ) (hθ : IsSecular (branchMS a) θ) :
    IsMainEigenvalue (switchMatrix (adjT a) s) θ ↔ Gs a s θ ≠ 0 := by
  have hθ0 := ne_zero_of_isSecular a hθ
  obtain ⟨hne, hF⟩ := (isSecular_iff a θ).1 hθ
  rw [isMainEigenvalue_switch_iff _ hs]
  constructor
  · rintro ⟨y, hy, hys⟩ hG
    apply hys
    rw [dot_secular a hy hθ0 hne hF, hG, mul_zero]
  · intro hG
    refine ⟨secVec a θ, secVec_eigen a hne hF, ?_⟩
    rw [dot_secular a (secVec_eigen a hne hF) hθ0 hne hF]
    simpa [secVec] using hG

end P8Main
