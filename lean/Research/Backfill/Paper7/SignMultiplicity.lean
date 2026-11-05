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

def signBase (b : ℕ) (p : Fin b → ℕ) (ε : ℚ) : Matrix (Fin b) (Fin b) ℚ :=
  (SimpleGraph.cycleGraph b).adjMatrix ℚ +
    Matrix.diagonal (fun k => ε * ((p k : ℚ) - 1))

#print axioms Paper7Reduced.signBase

theorem signBase_mulVec_entry (b : ℕ) (p : Fin b → ℕ) (ε : ℚ)
    (y : Fin b → ℚ) (k : Fin b) :
    (signBase b p ε *ᵥ y) k =
      ((SimpleGraph.cycleGraph b).adjMatrix ℚ *ᵥ y) k + ε * ((p k : ℚ) - 1) * y k := by
  simp only [signBase, Matrix.add_mulVec, Pi.add_apply, Matrix.mulVec_diagonal]

#print axioms Paper7Reduced.signBase_mulVec_entry

def signLift (b : ℕ) (p q : Fin b → ℕ) (ε : ℚ)
    (z : (Fin b → ℚ) × (∀ k, PQArmIndex b p q 2 k → ℚ)) :
    SunV b (pq b p q) → ℚ
  | Sum.inl k => z.1 k
  | Sum.inr ⟨k, j, a⟩ =>
      if h : (pq b p q k).get j = 2 then
        if a.val = 0 then z.2 k ⟨j, h⟩ else ε * z.2 k ⟨j, h⟩
      else ε * z.1 k

#print axioms Paper7Reduced.signLift

def signExtract (b : ℕ) (p q : Fin b → ℕ) (v : SunV b (pq b p q) → ℚ) :
    (Fin b → ℚ) × (∀ k, PQArmIndex b p q 2 k → ℚ) :=
  (v ∘ Sum.inl, fun k j => v (Sum.inr ⟨k, j.1, armFirst b p q k j.1⟩))

#print axioms Paper7Reduced.signExtract

theorem signLift_endpoint_sum (b : ℕ) (p q : Fin b → ℕ) (ε : ℚ)
    (z : (Fin b → ℚ) × (∀ k, PQArmIndex b p q 2 k → ℚ)) (k : Fin b) :
    (∑ j : Fin (pq b p q k).length,
      signLift b p q ε z (Sum.inr ⟨k, j, armFirst b p q k j⟩)) =
      (∑ j, z.2 k j) + (p k : ℚ) * (ε * z.1 k) := by
  have hpoint (j : Fin (pq b p q k).length) :
      signLift b p q ε z (Sum.inr ⟨k, j, armFirst b p q k j⟩) =
        (if h : (pq b p q k).get j = 2 then z.2 k ⟨j, h⟩ else 0) +
        (if (pq b p q k).get j = 1 then ε * z.1 k else 0) := by
    change (if h : (pq b p q k)[j.val] = 2 then z.2 k ⟨j, h⟩ else ε * z.1 k) =
      (if h : (pq b p q k)[j.val] = 2 then z.2 k ⟨j, h⟩ else 0) +
      (if (pq b p q k)[j.val] = 1 then ε * z.1 k else 0)
    rcases pq_length_one_or_two b p q k j with hj | hj
    · change (pq b p q k)[j.val] = 1 at hj
      simp [hj]
    · change (pq b p q k)[j.val] = 2 at hj
      simp [hj]
  simp_rw [hpoint]
  rw [Finset.sum_add_distrib, sum_subtype_extend]
  congr 1
  simpa using pq_sum_lengths_apply b p q k
    (fun t => if t = 1 then ε * z.1 k else 0)

#print axioms Paper7Reduced.signLift_endpoint_sum

theorem signLift_in_kernel (b : ℕ) (p q : Fin b → ℕ) (hb : 3 ≤ b)
    (ε : ℚ) (hε : ε ^ 2 = 1)
    (z : bundleParam (signBase b p ε) (PQArmIndex b p q 2)) :
    (ε • (1 : Matrix (SunV b (pq b p q)) (SunV b (pq b p q)) ℚ) -
      (SG b p q).adjMatrix ℚ) *ᵥ signLift b p q ε z.1 = 0 := by
  apply (sun_kernel_rows b p q hb ε _).mpr
  constructor
  · intro k
    rw [signLift_endpoint_sum]
    change ε * z.1.1 k - ((SimpleGraph.cycleGraph b).adjMatrix ℚ *ᵥ z.1.1) k -
      ((∑ j, z.1.2 k j) + (p k : ℚ) * (ε * z.1.1 k)) = 0
    have h := z.2.2 k
    rw [signBase_mulVec_entry] at h
    linear_combination -h
  · intro k j
    apply (sign_path_iff ε hε ((pq b p q k).get j) (pq_length_one_or_two b p q k j)
      (armFirst b p q k j) rfl
      (fun a => signLift b p q ε z.1 (Sum.inr ⟨k, j, a⟩)) (z.1.1 k)).mpr
    constructor
    · intro hj
      have hc : 0 < Fintype.card (PQArmIndex b p q 2 k) :=
        Fintype.card_pos_iff.mpr ⟨⟨j, hj⟩⟩
      exact z.2.1 k hc
    · intro a
      change
        (if h : (pq b p q k)[j.val] = 2 then
          if a.val = 0 then z.1.2 k ⟨j, h⟩ else ε * z.1.2 k ⟨j, h⟩
        else ε * z.1.1 k) =
        if (pq b p q k)[j.val] = 1 then ε * z.1.1 k
        else if a.val = 0 then
          (if h : (pq b p q k)[j.val] = 2 then z.1.2 k ⟨j, h⟩ else ε * z.1.1 k)
        else ε * (if h : (pq b p q k)[j.val] = 2 then z.1.2 k ⟨j, h⟩ else ε * z.1.1 k)
      rcases pq_length_one_or_two b p q k j with hj | hj
      · change (pq b p q k)[j.val] = 1 at hj
        simp [hj]
      · change (pq b p q k)[j.val] = 2 at hj
        simp [hj]

#print axioms Paper7Reduced.signLift_in_kernel

theorem sign_kernel_extract (b : ℕ) (p q : Fin b → ℕ) (hb : 3 ≤ b)
    (ε : ℚ) (hε : ε ^ 2 = 1) (v : SunV b (pq b p q) → ℚ)
    (hv : (ε • (1 : Matrix (SunV b (pq b p q)) (SunV b (pq b p q)) ℚ) -
      (SG b p q).adjMatrix ℚ) *ᵥ v = 0) :
    signExtract b p q v ∈ bundleParam (signBase b p ε) (PQArmIndex b p q 2) ∧
      signLift b p q ε (signExtract b p q v) = v := by
  classical
  obtain ⟨hr, ha⟩ := (sun_kernel_rows b p q hb ε v).mp hv
  have hpath (k : Fin b) (j : Fin (pq b p q k).length) :=
    (sign_path_iff ε hε ((pq b p q k).get j) (pq_length_one_or_two b p q k j)
      (armFirst b p q k j) rfl (fun a => v (Sum.inr ⟨k, j, a⟩))
      (v (Sum.inl k))).mp (ha k j)
  have hlift : signLift b p q ε (signExtract b p q v) = v := by
    funext a
    rcases a with k | ⟨k, j, a⟩
    · rfl
    · rcases pq_length_one_or_two b p q k j with hj | hj
      · change (pq b p q k)[j.val] = 1 at hj
        simpa [signLift, signExtract, hj] using ((hpath k j).2 a).symm
      · change (pq b p q k)[j.val] = 2 at hj
        simpa [signLift, signExtract, hj] using ((hpath k j).2 a).symm
  refine ⟨⟨?_, ?_⟩, hlift⟩
  · intro k hk
    have hn := Fintype.card_pos_iff.mp hk
    rcases hn with ⟨j⟩
    exact (hpath k j.1).1 j.2
  · intro k
    have hs : (∑ j : Fin (pq b p q k).length,
        v (Sum.inr ⟨k, j, armFirst b p q k j⟩)) =
        (∑ j, (signExtract b p q v).2 k j) +
          (p k : ℚ) * (ε * v (Sum.inl k)) := by
      have he := congrArg (fun f : SunV b (pq b p q) → ℚ =>
        ∑ j : Fin (pq b p q k).length, f (Sum.inr ⟨k, j, armFirst b p q k j⟩)) hlift
      exact he.symm.trans (signLift_endpoint_sum b p q ε (signExtract b p q v) k)
    have h := hr k
    rw [hs] at h
    change (signBase b p ε *ᵥ (v ∘ Sum.inl)) k +
      ∑ j, (signExtract b p q v).2 k j = 0
    rw [signBase_mulVec_entry]
    change ((SimpleGraph.cycleGraph b).adjMatrix ℚ *ᵥ (v ∘ Sum.inl)) k +
      ε * ((p k : ℚ) - 1) * v (Sum.inl k) +
      ∑ j, (signExtract b p q v).2 k j = 0
    linear_combination -h

#print axioms Paper7Reduced.sign_kernel_extract

def signKernelEquiv (b : ℕ) (p q : Fin b → ℕ) (hb : 3 ≤ b)
    (ε : ℚ) (hε : ε ^ 2 = 1) :
    LinearMap.ker (Matrix.toLin'
      (ε • (1 : Matrix (SunV b (pq b p q)) (SunV b (pq b p q)) ℚ) -
        (SG b p q).adjMatrix ℚ)) ≃ₗ[ℚ]
      bundleParam (signBase b p ε) (PQArmIndex b p q 2) where
  toFun v := ⟨signExtract b p q v.1, (sign_kernel_extract b p q hb ε hε v.1 v.2).1⟩
  invFun z := ⟨signLift b p q ε z.1, signLift_in_kernel b p q hb ε hε z⟩
  left_inv v := by
    apply Subtype.ext
    exact (sign_kernel_extract b p q hb ε hε v.1 v.2).2
  right_inv z := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · funext k j
      have hj := j.property
      change (pq b p q k)[j.1.val] = 2 at hj
      change (if h : (pq b p q k)[j.1.val] = 2 then z.1.2 k ⟨j.1, h⟩
        else ε * z.1.1 k) = z.1.2 k j
      simp [hj]
  map_add' v w := by
    apply Subtype.ext
    rfl
  map_smul' c v := by
    apply Subtype.ext
    rfl

#print axioms Paper7Reduced.signKernelEquiv

theorem signSystem_eq_bundleReduced (b : ℕ) (p q : Fin b → ℕ) (ε : ℤ) :
    overQ (signSystem b p q ε) = bundleReduced (signBase b p (ε : ℚ)) (PQArmIndex b p q 2) := by
  classical
  ext k j
  by_cases hq : 0 < q k <;> by_cases hj : k = j <;>
    simp [overQ, signSystem, bundleReduced, card_PQArmIndex_two, signBase,
      cycleAdjZ, Matrix.map_apply, Matrix.add_apply, SimpleGraph.adjMatrix_apply,
      hq, hj, eq_comm]

#print axioms Paper7Reduced.signSystem_eq_bundleReduced

theorem sign_reduced_multiplicity (b : ℕ) (p q : Fin b → ℕ) (hb : 3 ≤ b)
    (ε : ℤ) (hε : ε = 1 ∨ ε = -1) :
    mult (SG b p q) (ε : ℝ) =
      freeQ b q + matrixNullity (overQ (signSystem b p q ε)) := by
  have hsquare : (ε : ℚ) ^ 2 = 1 := by rcases hε with rfl | rfl <;> norm_num
  rw [mult_eq_shift_nullity, matrixNullity, (signKernelEquiv b p q hb (ε : ℚ) hsquare).finrank_eq,
    finrank_bundleParam, ← signSystem_eq_bundleReduced]
  congr 1
  simp only [card_PQArmIndex_two]
  exact (positive_pred_sum_filter q).symm

#print axioms Paper7Reduced.sign_reduced_multiplicity

end Paper7Reduced
