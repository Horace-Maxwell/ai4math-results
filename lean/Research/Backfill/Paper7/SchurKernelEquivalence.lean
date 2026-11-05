import Research.Backfill.Paper7.ChallengeV3

set_option autoImplicit false
set_option maxRecDepth 4096

noncomputable section

namespace Paper7Reduced

open BackfillPaper7.Challenge.Legacy.Algebra
open scoped Matrix

theorem block_mulVec_zero_iff {K : Type*} [Field K]
    {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (A : Matrix m m K) (B : Matrix m n K) (C : Matrix n m K) (D : Matrix n n K)
    (v : m ⊕ n → K) :
    Matrix.fromBlocks A B C D *ᵥ v = 0 ↔
      A *ᵥ (v ∘ Sum.inl) + B *ᵥ (v ∘ Sum.inr) = 0 ∧
      C *ᵥ (v ∘ Sum.inl) + D *ᵥ (v ∘ Sum.inr) = 0 := by
  rw [Matrix.fromBlocks_mulVec]
  constructor
  · intro h
    constructor
    · funext i
      exact congrFun h (Sum.inl i)
    · funext j
      exact congrFun h (Sum.inr j)
  · rintro ⟨h₁, h₂⟩
    rw [h₁, h₂]
    funext z
    cases z <;> rfl

#print axioms Paper7Reduced.block_mulVec_zero_iff

theorem schur_mulVec_zero_iff {K : Type*} [Field K]
    {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (A : Matrix m m K) (B : Matrix m n K) (C : Matrix n m K) (D : Matrix n n K)
    [Invertible D] (v : m ⊕ n → K) :
    Matrix.fromBlocks A B C D *ᵥ v = 0 ↔
      (A - (B * D⁻¹ : Matrix m n K) * C) *ᵥ (v ∘ Sum.inl) = 0 ∧
      v ∘ Sum.inr = -(D⁻¹ *ᵥ (C *ᵥ (v ∘ Sum.inl))) := by
  rw [block_mulVec_zero_iff]
  constructor
  · rintro ⟨h₁, h₂⟩
    have hD : D *ᵥ (v ∘ Sum.inr) = -(C *ᵥ (v ∘ Sum.inl)) := by
      calc
        D *ᵥ (v ∘ Sum.inr) =
            (C *ᵥ (v ∘ Sum.inl) + D *ᵥ (v ∘ Sum.inr)) - C *ᵥ (v ∘ Sum.inl) := by abel
        _ = _ := by rw [h₂]; simp
    have hout : v ∘ Sum.inr = -(D⁻¹ *ᵥ (C *ᵥ (v ∘ Sum.inl))) := by
      calc
        v ∘ Sum.inr = D⁻¹ *ᵥ (D *ᵥ (v ∘ Sum.inr)) := by
          rw [Matrix.mulVec_mulVec, Matrix.inv_mul_of_invertible, Matrix.one_mulVec]
        _ = _ := by rw [hD, Matrix.mulVec_neg]
    refine ⟨?_, hout⟩
    rw [Matrix.sub_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    simpa only [hout, Matrix.mulVec_neg, sub_eq_add_neg] using h₁
  · rintro ⟨hS, hout⟩
    constructor
    · rw [hout, Matrix.mulVec_neg]
      rw [Matrix.sub_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec] at hS
      simpa only [sub_eq_add_neg] using hS
    · rw [hout, Matrix.mulVec_neg, Matrix.mulVec_mulVec,
        Matrix.mul_inv_of_invertible, Matrix.one_mulVec]
      simp

#print axioms Paper7Reduced.schur_mulVec_zero_iff

def schurKernelEquiv {K : Type*} [Field K]
    {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (A : Matrix m m K) (B : Matrix m n K) (C : Matrix n m K) (D : Matrix n n K)
    [Invertible D] :
    LinearMap.ker (Matrix.toLin' (Matrix.fromBlocks A B C D)) ≃ₗ[K]
      LinearMap.ker (Matrix.toLin' (A - (B * D⁻¹ : Matrix m n K) * C)) where
  toFun v := ⟨v.1 ∘ Sum.inl, by
    change (A - (B * D⁻¹ : Matrix m n K) * C) *ᵥ (v.1 ∘ Sum.inl) = 0
    exact ((schur_mulVec_zero_iff A B C D v.1).mp v.2).1⟩
  invFun y := ⟨Sum.elim y.1 (-(D⁻¹ *ᵥ (C *ᵥ y.1))), by
    apply (schur_mulVec_zero_iff A B C D _).mpr
    constructor
    · change (A - (B * D⁻¹ : Matrix m n K) * C) *ᵥ y.1 = 0
      exact y.2
    · rfl⟩
  left_inv v := by
    apply Subtype.ext
    funext z
    rcases z with i | j
    · rfl
    · exact (congrFun ((schur_mulVec_zero_iff A B C D v.1).mp v.2).2 j).symm
  right_inv y := by
    apply Subtype.ext
    rfl
  map_add' u v := by
    apply Subtype.ext
    rfl
  map_smul' c v := by
    apply Subtype.ext
    rfl

#print axioms Paper7Reduced.schurKernelEquiv

theorem nullity_fromBlocks_eq_schur {K : Type} [Field K]
    {m n : Type} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (A : Matrix m m K) (B : Matrix m n K) (C : Matrix n m K) (D : Matrix n n K)
    [Invertible D] :
    matrixNullity (Matrix.fromBlocks A B C D) =
      matrixNullity (A - (B * D⁻¹ : Matrix m n K) * C) := by
  simpa only [matrixNullity] using! (schurKernelEquiv A B C D).finrank_eq

#print axioms Paper7Reduced.nullity_fromBlocks_eq_schur

theorem nullity_smul_of_ne_zero {K : Type} [Field K]
    {n : Type} [Fintype n] [DecidableEq n] (A : Matrix n n K)
    (c : K) (hc : c ≠ 0) : matrixNullity (c • A) = matrixNullity A := by
  have hker : LinearMap.ker (Matrix.toLin' (c • A)) = LinearMap.ker (Matrix.toLin' A) := by
    ext v
    simp only [LinearMap.mem_ker, Matrix.toLin'_apply, Matrix.smul_mulVec]
    simp [hc]
  exact congrArg (fun S : Submodule K (n → K) => Module.finrank K S) hker

#print axioms Paper7Reduced.nullity_smul_of_ne_zero

end Paper7Reduced
