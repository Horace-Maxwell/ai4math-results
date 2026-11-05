import Research.Backfill.Paper7.ZeroSumBundles

set_option autoImplicit false
set_option maxRecDepth 4096

noncomputable section

namespace Paper7Reduced

open BackfillPaper7.Challenge.Legacy.Algebra
open scoped Matrix

variable {κ : Type} [Fintype κ] [DecidableEq κ]

def bundleReduced (A : Matrix κ κ ℚ) (J : κ → Type) [∀ k, Fintype (J k)] :
    Matrix κ κ ℚ := fun k j =>
  if 0 < Fintype.card (J k) then (if j = k then 1 else 0) else A k j

#print axioms Paper7Reduced.bundleReduced

def bundleParam (A : Matrix κ κ ℚ) (J : κ → Type) [∀ k, Fintype (J k)] :
    Submodule ℚ ((κ → ℚ) × (∀ k, J k → ℚ)) where
  carrier := {z | (∀ k, 0 < Fintype.card (J k) → z.1 k = 0) ∧
    ∀ k, (A *ᵥ z.1) k + ∑ j, z.2 k j = 0}
  zero_mem' := by simp
  add_mem' := by
    rintro x y ⟨hxp, hxs⟩ ⟨hyp, hys⟩
    constructor
    · intro k hk
      change x.1 k + y.1 k = 0
      rw [hxp k hk, hyp k hk, add_zero]
    · intro k
      change (A *ᵥ (x.1 + y.1)) k + ∑ j, (x.2 k j + y.2 k j) = 0
      rw [Matrix.mulVec_add, Finset.sum_add_distrib]
      have hx := hxs k
      have hy := hys k
      change (A *ᵥ x.1) k + (A *ᵥ y.1) k +
        ((∑ j, x.2 k j) + ∑ j, y.2 k j) = 0
      linarith
  smul_mem' := by
    rintro c x ⟨hxp, hxs⟩
    constructor
    · intro k hk
      change c * x.1 k = 0
      rw [hxp k hk, mul_zero]
    · intro k
      change (A *ᵥ (c • x.1)) k + ∑ j, c * x.2 k j = 0
      rw [Matrix.mulVec_smul, ← Finset.mul_sum]
      change c * (A *ᵥ x.1) k + c * (∑ j, x.2 k j) = 0
      rw [← mul_add, hxs k, mul_zero]

#print axioms Paper7Reduced.bundleParam

theorem bundleReduced_kernel_iff (A : Matrix κ κ ℚ) (J : κ → Type)
    [∀ k, Fintype (J k)] (y : κ → ℚ) :
    y ∈ LinearMap.ker (Matrix.toLin' (bundleReduced A J)) ↔
      (∀ k, 0 < Fintype.card (J k) → y k = 0) ∧
      (∀ k, Fintype.card (J k) = 0 → (A *ᵥ y) k = 0) := by
  classical
  change bundleReduced A J *ᵥ y = 0 ↔ _
  constructor
  · intro h
    constructor
    · intro k hk
      simpa [bundleReduced, Matrix.mulVec, dotProduct, hk] using congrFun h k
    · intro k hk
      simpa [bundleReduced, Matrix.mulVec, dotProduct, hk] using congrFun h k
  · rintro ⟨hp, hz⟩
    funext k
    by_cases hk : 0 < Fintype.card (J k)
    · simpa [bundleReduced, Matrix.mulVec, dotProduct, hk] using hp k hk
    · have hzcard : Fintype.card (J k) = 0 := by omega
      simpa [bundleReduced, Matrix.mulVec, dotProduct, hk] using hz k hzcard

#print axioms Paper7Reduced.bundleReduced_kernel_iff

def bundleRoot (A : Matrix κ κ ℚ) (J : κ → Type) [∀ k, Fintype (J k)]
    (z : bundleParam A J) : LinearMap.ker (Matrix.toLin' (bundleReduced A J)) :=
  ⟨z.1.1, (bundleReduced_kernel_iff A J z.1.1).mpr ⟨z.2.1, by
    intro k hk
    let : IsEmpty (J k) := Fintype.card_eq_zero_iff.mp hk
    simpa using z.2.2 k⟩⟩

#print axioms Paper7Reduced.bundleRoot

theorem bundle_mean_sum (A : Matrix κ κ ℚ) (J : κ → Type)
    [∀ k, Fintype (J k)]
    (y : LinearMap.ker (Matrix.toLin' (bundleReduced A J))) (k : κ) :
    (∑ _j : J k, (A *ᵥ y.1) k / (Fintype.card (J k) : ℚ)) = (A *ᵥ y.1) k := by
  by_cases hz : Fintype.card (J k) = 0
  · let : IsEmpty (J k) := Fintype.card_eq_zero_iff.mp hz
    have hy := ((bundleReduced_kernel_iff A J y.1).mp y.2).2 k hz
    simp [hy]
  · have hc : (Fintype.card (J k) : ℚ) ≠ 0 := by exact_mod_cast hz
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    field_simp [hc]

#print axioms Paper7Reduced.bundle_mean_sum

def bundleParamEquiv (A : Matrix κ κ ℚ) (J : κ → Type) [∀ k, Fintype (J k)] :
    bundleParam A J ≃ₗ[ℚ]
      (LinearMap.ker (Matrix.toLin' (bundleReduced A J)) ×
        (∀ k, LinearMap.ker (sumCoordinates ℚ (J k)))) where
  toFun z := (bundleRoot A J z, fun k =>
    ⟨fun j => z.1.2 k j + (A *ᵥ z.1.1) k / (Fintype.card (J k) : ℚ), by
      change (∑ j, (z.1.2 k j + (A *ᵥ z.1.1) k / (Fintype.card (J k) : ℚ))) = 0
      rw [Finset.sum_add_distrib]
      have hmean := bundle_mean_sum A J (bundleRoot A J z) k
      change (∑ _j : J k, (A *ᵥ z.1.1) k / (Fintype.card (J k) : ℚ)) =
        (A *ᵥ z.1.1) k at hmean
      rw [hmean, add_comm]
      exact z.2.2 k⟩)
  invFun yz := ⟨(yz.1.1,
      fun k j => (yz.2 k).1 j - (A *ᵥ yz.1.1) k / (Fintype.card (J k) : ℚ)), by
    constructor
    · exact ((bundleReduced_kernel_iff A J yz.1.1).mp yz.1.2).1
    · intro k
      change (A *ᵥ yz.1.1) k +
        ∑ j, ((yz.2 k).1 j - (A *ᵥ yz.1.1) k / (Fintype.card (J k) : ℚ)) = 0
      rw [Finset.sum_sub_distrib, bundle_mean_sum A J yz.1 k]
      have hz := (yz.2 k).2
      change (∑ j, (yz.2 k).1 j) = 0 at hz
      rw [hz]
      ring⟩
  left_inv z := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · funext k j
      change (z.1.2 k j + (A *ᵥ z.1.1) k / (Fintype.card (J k) : ℚ)) -
        (A *ᵥ z.1.1) k / (Fintype.card (J k) : ℚ) = z.1.2 k j
      ring
  right_inv yz := by
    apply Prod.ext
    · apply Subtype.ext
      rfl
    · funext k
      apply Subtype.ext
      funext j
      change ((yz.2 k).1 j - (A *ᵥ yz.1.1) k / (Fintype.card (J k) : ℚ)) +
        (A *ᵥ yz.1.1) k / (Fintype.card (J k) : ℚ) = (yz.2 k).1 j
      ring
  map_add' z w := by
    apply Prod.ext
    · apply Subtype.ext
      rfl
    · funext k
      apply Subtype.ext
      funext j
      change (z.1.2 k j + w.1.2 k j) +
        (A *ᵥ (z.1.1 + w.1.1)) k / (Fintype.card (J k) : ℚ) =
        (z.1.2 k j + (A *ᵥ z.1.1) k / (Fintype.card (J k) : ℚ)) +
        (w.1.2 k j + (A *ᵥ w.1.1) k / (Fintype.card (J k) : ℚ))
      rw [Matrix.mulVec_add]
      change _ + ((A *ᵥ z.1.1) k + (A *ᵥ w.1.1) k) / _ = _
      ring
  map_smul' c z := by
    apply Prod.ext
    · apply Subtype.ext
      rfl
    · funext k
      apply Subtype.ext
      funext j
      change c * z.1.2 k j + (A *ᵥ (c • z.1.1)) k / (Fintype.card (J k) : ℚ) =
        c * (z.1.2 k j + (A *ᵥ z.1.1) k / (Fintype.card (J k) : ℚ))
      rw [Matrix.mulVec_smul]
      change _ + (c * (A *ᵥ z.1.1) k) / _ = _
      ring

#print axioms Paper7Reduced.bundleParamEquiv

theorem finrank_bundleParam (A : Matrix κ κ ℚ) (J : κ → Type)
    [∀ k, Fintype (J k)] :
    Module.finrank ℚ (bundleParam A J) =
      (∑ k, (Fintype.card (J k) - 1)) + matrixNullity (bundleReduced A J) := by
  rw [(bundleParamEquiv A J).finrank_eq, Module.finrank_prod, finrank_zeroSumBundles]
  exact Nat.add_comm _ _

#print axioms Paper7Reduced.finrank_bundleParam

end Paper7Reduced
