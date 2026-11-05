import Research.Backfill.Paper7.PQArmCoordinates
import Research.Backfill.Paper7.ExceptionalPathSolutions
import Research.Backfill.Paper7.BundleReduction
import Research.Backfill.Paper7.FreeArmOffsets
import Research.Backfill.Paper7.OrdinaryReducedMultiplicity

set_option autoImplicit false
set_option maxRecDepth 4096

noncomputable section

namespace Paper7Reduced

open BackfillPaper7.Challenge BackfillPaper7.Challenge.Legacy.Algebra
open Paper7Cleared
open scoped Matrix

def zeroLift (b : ℕ) (p q : Fin b → ℕ)
    (z : (Fin b → ℚ) × (∀ k, PQArmIndex b p q 1 k → ℚ)) :
    SunV b (pq b p q) → ℚ
  | Sum.inl k => z.1 k
  | Sum.inr ⟨k, j, a⟩ =>
      if h : (pq b p q k).get j = 1 then z.2 k ⟨j, h⟩
      else if a.val = 0 then 0 else -z.1 k

#print axioms Paper7Reduced.zeroLift

def zeroExtract (b : ℕ) (p q : Fin b → ℕ) (v : SunV b (pq b p q) → ℚ) :
    (Fin b → ℚ) × (∀ k, PQArmIndex b p q 1 k → ℚ) :=
  (v ∘ Sum.inl, fun k j => v (Sum.inr ⟨k, j.1, armFirst b p q k j.1⟩))

#print axioms Paper7Reduced.zeroExtract

theorem zeroLift_endpoint_sum (b : ℕ) (p q : Fin b → ℕ)
    (z : (Fin b → ℚ) × (∀ k, PQArmIndex b p q 1 k → ℚ)) (k : Fin b) :
    (∑ j : Fin (pq b p q k).length,
      zeroLift b p q z (Sum.inr ⟨k, j, armFirst b p q k j⟩)) = ∑ j, z.2 k j := by
  change (∑ j : Fin (pq b p q k).length,
    if h : (pq b p q k).get j = 1 then z.2 k ⟨j, h⟩ else 0) = ∑ j, z.2 k j
  exact sum_subtype_extend _ _

#print axioms Paper7Reduced.zeroLift_endpoint_sum

theorem zeroLift_in_kernel (b : ℕ) (p q : Fin b → ℕ) (hb : 3 ≤ b)
    (z : bundleParam ((SimpleGraph.cycleGraph b).adjMatrix ℚ) (PQArmIndex b p q 1)) :
    ((0 : ℚ) • (1 : Matrix (SunV b (pq b p q)) (SunV b (pq b p q)) ℚ) -
      (SG b p q).adjMatrix ℚ) *ᵥ zeroLift b p q z.1 = 0 := by
  apply (sun_kernel_rows b p q hb 0 _).mpr
  constructor
  · intro k
    rw [zeroLift_endpoint_sum]
    change 0 * z.1.1 k - ((SimpleGraph.cycleGraph b).adjMatrix ℚ *ᵥ z.1.1) k -
      ∑ j, z.1.2 k j = 0
    have h := z.2.2 k
    linarith
  · intro k j
    apply (zero_path_iff ((pq b p q k).get j) (pq_length_one_or_two b p q k j)
      (armFirst b p q k j) rfl
      (fun a => zeroLift b p q z.1 (Sum.inr ⟨k, j, a⟩)) (z.1.1 k)).mpr
    constructor
    · intro hj
      have hc : 0 < Fintype.card (PQArmIndex b p q 1 k) :=
        Fintype.card_pos_iff.mpr ⟨⟨j, hj⟩⟩
      exact z.2.1 k hc
    · intro a
      by_cases hj : (pq b p q k).get j = 1
      · change (pq b p q k)[j.val] = 1 at hj
        simp [zeroLift, hj]
      · change ¬(pq b p q k)[j.val] = 1 at hj
        simp [zeroLift, hj]

#print axioms Paper7Reduced.zeroLift_in_kernel

theorem zero_kernel_extract (b : ℕ) (p q : Fin b → ℕ) (hb : 3 ≤ b)
    (v : SunV b (pq b p q) → ℚ)
    (hv : ((0 : ℚ) • (1 : Matrix (SunV b (pq b p q)) (SunV b (pq b p q)) ℚ) -
      (SG b p q).adjMatrix ℚ) *ᵥ v = 0) :
    zeroExtract b p q v ∈
      bundleParam ((SimpleGraph.cycleGraph b).adjMatrix ℚ) (PQArmIndex b p q 1) ∧
      zeroLift b p q (zeroExtract b p q v) = v := by
  classical
  obtain ⟨hr, ha⟩ := (sun_kernel_rows b p q hb 0 v).mp hv
  have hpath (k : Fin b) (j : Fin (pq b p q k).length) :=
    (zero_path_iff ((pq b p q k).get j) (pq_length_one_or_two b p q k j)
      (armFirst b p q k j) rfl (fun a => v (Sum.inr ⟨k, j, a⟩))
      (v (Sum.inl k))).mp (ha k j)
  have hlift : zeroLift b p q (zeroExtract b p q v) = v := by
    funext a
    rcases a with k | ⟨k, j, a⟩
    · rfl
    · by_cases hj : (pq b p q k).get j = 1
      · simpa only [zeroLift, zeroExtract, hj, dite_true, ite_true] using
          ((hpath k j).2 a).symm
      · simpa only [zeroLift, zeroExtract, hj, dite_false, ite_false,
          Function.comp_apply] using ((hpath k j).2 a).symm
  refine ⟨⟨?_, ?_⟩, hlift⟩
  · intro k hk
    have hn := Fintype.card_pos_iff.mp hk
    rcases hn with ⟨j⟩
    exact (hpath k j.1).1 j.2
  · intro k
    have hs : (∑ j : Fin (pq b p q k).length,
        v (Sum.inr ⟨k, j, armFirst b p q k j⟩)) =
        ∑ j, (zeroExtract b p q v).2 k j := by
      have he := congrArg (fun f : SunV b (pq b p q) → ℚ =>
        ∑ j : Fin (pq b p q k).length, f (Sum.inr ⟨k, j, armFirst b p q k j⟩)) hlift
      exact he.symm.trans (zeroLift_endpoint_sum b p q (zeroExtract b p q v) k)
    have h := hr k
    rw [hs] at h
    change ((SimpleGraph.cycleGraph b).adjMatrix ℚ *ᵥ (v ∘ Sum.inl)) k +
      ∑ j, (zeroExtract b p q v).2 k j = 0
    linarith

#print axioms Paper7Reduced.zero_kernel_extract

def zeroKernelEquiv (b : ℕ) (p q : Fin b → ℕ) (hb : 3 ≤ b) :
    LinearMap.ker (Matrix.toLin'
      ((0 : ℚ) • (1 : Matrix (SunV b (pq b p q)) (SunV b (pq b p q)) ℚ) -
        (SG b p q).adjMatrix ℚ)) ≃ₗ[ℚ]
      bundleParam ((SimpleGraph.cycleGraph b).adjMatrix ℚ) (PQArmIndex b p q 1) where
  toFun v := ⟨zeroExtract b p q v.1, (zero_kernel_extract b p q hb v.1 v.2).1⟩
  invFun z := ⟨zeroLift b p q z.1, zeroLift_in_kernel b p q hb z⟩
  left_inv v := by
    apply Subtype.ext
    exact (zero_kernel_extract b p q hb v.1 v.2).2
  right_inv z := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · funext k j
      have hj := j.property
      change (pq b p q k)[j.1.val] = 1 at hj
      simp [zeroExtract, zeroLift, hj]
  map_add' v w := by
    apply Subtype.ext
    rfl
  map_smul' c v := by
    apply Subtype.ext
    rfl

#print axioms Paper7Reduced.zeroKernelEquiv

theorem zeroSystem_eq_bundleReduced (b : ℕ) (p q : Fin b → ℕ) :
    overQ (zeroSystem b p) =
      bundleReduced ((SimpleGraph.cycleGraph b).adjMatrix ℚ) (PQArmIndex b p q 1) := by
  classical
  ext k j
  by_cases hp : 0 < p k <;> by_cases hj : j = k <;>
    simp [overQ, zeroSystem, bundleReduced, card_PQArmIndex_one,
      cycleAdjZ, Matrix.map_apply, SimpleGraph.adjMatrix_apply, hp, hj]

#print axioms Paper7Reduced.zeroSystem_eq_bundleReduced

theorem zero_reduced_multiplicity (b : ℕ) (p q : Fin b → ℕ) (hb : 3 ≤ b) :
    mult (SG b p q) 0 = freeP b p + matrixNullity (overQ (zeroSystem b p)) := by
  have hm : mult (SG b p q) 0 =
      matrixNullity ((0 : ℚ) • (1 : Matrix (SunV b (pq b p q))
        (SunV b (pq b p q)) ℚ) - (SG b p q).adjMatrix ℚ) := by
    simpa only [Int.cast_zero] using mult_eq_shift_nullity (SG b p q) (0 : ℤ)
  rw [hm, matrixNullity, (zeroKernelEquiv b p q hb).finrank_eq,
    finrank_bundleParam, ← zeroSystem_eq_bundleReduced]
  congr 1
  simp only [card_PQArmIndex_one]
  exact (positive_pred_sum_filter p).symm

#print axioms Paper7Reduced.zero_reduced_multiplicity

end Paper7Reduced
