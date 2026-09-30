import Research.Backfill.Paper8.Challenge
import Research.Backfill.Paper8.Proof.Basic
import Research.SwitchingWalkProfile

/-!
# Paper 8 back-fill (agent `lin`): switchings and projections

Lemma 2.1 and its consequence `Lemma_2_1_good` (a switching `s` is good for `A` iff every
eigenvalue of `D_s A D_s` is main), the fact that `-s` is good when `s` is (`GoodNeg`), and
Remark 8.3, bridged from `SwitchingWalkProfile.eigen_nonorth`. The proofs use `D_s² = 1`:
`x ↦ D_s x` maps the `θ`-eigenvectors of `D_s A D_s` onto those of `A`, and `𝟏 ⬝ (D_s y) = s ⬝ y`.
-/

set_option autoImplicit false

open BackfillPaper8.Challenge Matrix

namespace P8Lin

section Switch

variable {n : Type} [Fintype n] [DecidableEq n]

/-- `D_s² = 1` for a switching `s`. -/
theorem diag_mul_diag_of_switching {s : n → ℝ} (hs : IsSwitching s) :
    diagonal s * diagonal s = 1 := by
  rw [diagonal_mul_diagonal, ← diagonal_one]
  congr 1
  funext i
  rcases hs i with h | h <;> simp [h]

theorem diag_mulVec_diag_mulVec {s : n → ℝ} (hs : IsSwitching s) (x : n → ℝ) :
    diagonal s *ᵥ (diagonal s *ᵥ x) = x := by
  rw [mulVec_mulVec, diag_mul_diag_of_switching hs, one_mulVec]

/-- `x` is a `θ`-eigenvector of `D_s A D_s` iff `D_s x` is a `θ`-eigenvector of `A`. -/
theorem switch_eig_iff (A : Matrix n n ℝ) {s : n → ℝ} (hs : IsSwitching s) (θ : ℝ)
    (x : n → ℝ) :
    switchMatrix A s *ᵥ x = θ • x ↔ A *ᵥ (diagonal s *ᵥ x) = θ • (diagonal s *ᵥ x) := by
  have hDD := diag_mul_diag_of_switching hs
  unfold switchMatrix
  constructor
  · intro h
    calc A *ᵥ (diagonal s *ᵥ x) = (diagonal s * diagonal s) *ᵥ (A *ᵥ (diagonal s *ᵥ x)) := by
          rw [hDD, one_mulVec]
      _ = diagonal s *ᵥ ((diagonal s * A * diagonal s) *ᵥ x) := by
          simp only [mulVec_mulVec, Matrix.mul_assoc]
      _ = diagonal s *ᵥ (θ • x) := by rw [h]
      _ = θ • (diagonal s *ᵥ x) := mulVec_smul _ _ _
  · intro h
    calc (diagonal s * A * diagonal s) *ᵥ x = diagonal s *ᵥ (A *ᵥ (diagonal s *ᵥ x)) := by
          simp only [mulVec_mulVec, Matrix.mul_assoc]
      _ = diagonal s *ᵥ (θ • (diagonal s *ᵥ x)) := by rw [h]
      _ = θ • x := by rw [mulVec_smul, diag_mulVec_diag_mulVec hs]

/-- `𝟏 ⬝ (D_s y) = y ⬝ s`. -/
theorem sum_diag_mulVec (s y : n → ℝ) : ∑ i, (diagonal s *ᵥ y) i = y ⬝ᵥ s := by
  simp only [mulVec_diagonal, dotProduct]
  exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)

/-- `θ` is an eigenvalue of `A` iff it is one of `D_s A D_s`. -/
theorem isEigenvalue_switch_iff (A : Matrix n n ℝ) {s : n → ℝ} (hs : IsSwitching s) (θ : ℝ) :
    IsEigenvalue (switchMatrix A s) θ ↔ IsEigenvalue A θ := by
  rw [P8Basic.isEigenvalue_iff, P8Basic.isEigenvalue_iff]
  constructor
  · rintro ⟨x, hx0, hx⟩
    refine ⟨diagonal s *ᵥ x, fun h0 => hx0 ?_, (switch_eig_iff A hs θ x).1 hx⟩
    rw [← diag_mulVec_diag_mulVec hs x, h0, mulVec_zero]
  · rintro ⟨y, hy0, hy⟩
    refine ⟨diagonal s *ᵥ y, fun h0 => hy0 ?_, ?_⟩
    · rw [← diag_mulVec_diag_mulVec hs y, h0, mulVec_zero]
    · rw [switch_eig_iff A hs θ, diag_mulVec_diag_mulVec hs]
      exact hy

/-- The body of **Lemma 2.1**: `θ` is a main eigenvalue of `D_s A D_s` iff `P_θ s ≠ 0`
(symmetry of `A` and `θ` being an eigenvalue of `A` are not needed). -/
theorem isMain_switch_iff (A : Matrix n n ℝ) {s : n → ℝ} (hs : IsSwitching s) (θ : ℝ) :
    IsMainEigenvalue (switchMatrix A s) θ ↔ ProjNe A θ s := by
  rw [P8Basic.projNe_iff]
  constructor
  · rintro ⟨_, x, hx, hsum⟩
    rw [P8Basic.mem_eigenspace_iff] at hx
    refine ⟨diagonal s *ᵥ x, (switch_eig_iff A hs θ x).1 hx, ?_⟩
    rwa [← sum_diag_mulVec, diag_mulVec_diag_mulVec hs]
  · rintro ⟨y, hy, hys⟩
    have hx : switchMatrix A s *ᵥ (diagonal s *ᵥ y) = θ • (diagonal s *ᵥ y) := by
      rw [switch_eig_iff A hs θ, diag_mulVec_diag_mulVec hs]
      exact hy
    have hsum : ∑ i, (diagonal s *ᵥ y) i ≠ 0 := by rwa [sum_diag_mulVec]
    refine ⟨(P8Basic.isEigenvalue_iff _ θ).2 ⟨diagonal s *ᵥ y, ?_, hx⟩, diagonal s *ᵥ y,
      (P8Basic.mem_eigenspace_iff _ θ _).2 hx, hsum⟩
    intro h0
    apply hsum
    simp [h0]

end Switch

/-- **Lemma 2.1** (`lem:good`). -/
theorem lemma_2_1 : Lemma_2_1 := by
  intro n _ _ A _ s hs θ _
  exact isMain_switch_iff A hs θ

/-- The consequence of Lemma 2.1: `s` is good iff every eigenvalue of `D_s A D_s` is main. -/
theorem lemma_2_1_good : Lemma_2_1_good := by
  intro n _ _ A _ s hs
  constructor
  · intro hgood θ hθ
    exact (isMain_switch_iff A hs θ).2 (hgood θ ((isEigenvalue_switch_iff A hs θ).1 hθ))
  · intro hmain θ hθ
    exact (isMain_switch_iff A hs θ).1 (hmain θ ((isEigenvalue_switch_iff A hs θ).2 hθ))

/-- The body of `GoodNeg` (§2): if `s` is good for `A`, so is `-s`. -/
theorem goodNeg_body : ∀ (n : Type) [Fintype n] [DecidableEq n] (A : Matrix n n ℝ)
    (s : n → ℝ), IsGood A s → IsGood A (-s) := by
  intro n _ _ A s hs
  rw [P8Basic.isGood_iff] at hs ⊢
  intro θ hθ
  obtain ⟨x, hx, hxs⟩ := hs θ hθ
  exact ⟨x, hx, by rw [dotProduct_neg]; exact neg_ne_zero.2 hxs⟩

/-- **Remark 8.3** (`rem:regular`), from `SwitchingWalkProfile.eigen_nonorth`. -/
theorem remark_8_3 : Remark_8_3 := by
  intro ι _ _ A hA c hc hn v w hw hprof
  rw [P8Basic.isGood_iff]
  intro θ hθ
  obtain ⟨x, hx0, hx⟩ := (P8Basic.isEigenvalue_iff A θ).1 hθ
  obtain ⟨y, hy, hys⟩ :=
    SwitchingWalkProfile.eigen_nonorth A hA c hc hn v w hw hprof θ x hx0 hx
  refine ⟨y, hy, ?_⟩
  rw [dotProduct_comm]
  exact hys

end P8Lin
