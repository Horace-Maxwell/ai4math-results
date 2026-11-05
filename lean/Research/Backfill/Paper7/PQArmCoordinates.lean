import Research.Backfill.Paper7.SunPendantAssembly
import Research.Backfill.Paper7.SunGraphBlocks
import Research.Backfill.Paper7.SchurKernelEquivalence

set_option autoImplicit false
set_option maxRecDepth 4096

noncomputable section

namespace Paper7Reduced

open BackfillPaper7.Challenge BackfillPaper7.Challenge.Legacy.Algebra
open Paper7Cleared
open scoped Matrix

abbrev PQArmIndex (b : ℕ) (p q : Fin b → ℕ) (t : ℕ) (k : Fin b) :=
  {j : Fin (pq b p q k).length // (pq b p q k).get j = t}

#print axioms Paper7Reduced.PQArmIndex

def armFirst (b : ℕ) (p q : Fin b → ℕ) (k : Fin b)
    (j : Fin (pq b p q k).length) : Fin ((pq b p q k).get j) :=
  ⟨0, by have h := pq_length_one_or_two b p q k j; omega⟩

#print axioms Paper7Reduced.armFirst

theorem pq_sum_lengths_apply {K : Type*} [Semiring K]
    (b : ℕ) (p q : Fin b → ℕ) (k : Fin b) (f : ℕ → K) :
    (∑ j : Fin (pq b p q k).length, f ((pq b p q k).get j)) =
      (p k : K) * f 1 + (q k : K) * f 2 := by
  calc
    _ = ((pq b p q k).map f).sum := by
      exact Fin.sum_univ_fun_getElem (M := K) (pq b p q k) f
    _ = _ := by simp [pq, nsmul_eq_mul]

#print axioms Paper7Reduced.pq_sum_lengths_apply

theorem card_PQArmIndex_one (b : ℕ) (p q : Fin b → ℕ) (k : Fin b) :
    Fintype.card (PQArmIndex b p q 1 k) = p k := by
  classical
  have h := pq_sum_lengths_apply b p q k (fun t => if t = 1 then (1 : ℕ) else 0)
  simpa [PQArmIndex, Fintype.card_subtype, Finset.sum_boole] using h

#print axioms Paper7Reduced.card_PQArmIndex_one

theorem card_PQArmIndex_two (b : ℕ) (p q : Fin b → ℕ) (k : Fin b) :
    Fintype.card (PQArmIndex b p q 2 k) = q k := by
  classical
  have h := pq_sum_lengths_apply b p q k (fun t => if t = 2 then (1 : ℕ) else 0)
  simpa [PQArmIndex, Fintype.card_subtype, Finset.sum_boole] using h

#print axioms Paper7Reduced.card_PQArmIndex_two

theorem sum_subtype_extend {ι : Type*} [Fintype ι] (P : ι → Prop)
    [DecidablePred P] (u : {i // P i} → ℚ) :
    (∑ i, if h : P i then u ⟨i, h⟩ else 0) = ∑ i, u i := by
  symm
  apply Fintype.sum_of_injective Subtype.val Subtype.val_injective
  · intro i hi
    have hn : ¬P i := by
      intro hp
      exact hi ⟨⟨i, hp⟩, rfl⟩
    simp [hn]
  · intro i
    simp [i.property]

#print axioms Paper7Reduced.sum_subtype_extend

theorem blockDiagonal_mulVec {K : Type*} [Semiring K]
    {ι : Type*} [Fintype ι] [DecidableEq ι] {ν : ι → Type*}
    [∀ k, Fintype (ν k)] (A : ∀ k, Matrix (ν k) (ν k) K)
    (v : (Σ k, ν k) → K) (k : ι) (i : ν k) :
    (Matrix.blockDiagonal' A *ᵥ v) ⟨k, i⟩ =
      (A k *ᵥ (fun j => v ⟨k, j⟩)) i := by
  classical
  simp only [Matrix.mulVec, dotProduct, Fintype.sum_sigma]
  rw [Fintype.sum_eq_single k]
  · simp only [Matrix.blockDiagonal'_apply_eq]
  · intro k' hk'
    apply Finset.sum_eq_zero
    intro j _hj
    rw [Matrix.blockDiagonal'_apply_ne _ _ _ (Ne.symm hk'), zero_mul]

#print axioms Paper7Reduced.blockDiagonal_mulVec

theorem pendant_mulVec_entry (b : ℕ) (p q : Fin b → ℕ) (x : ℚ)
    (z : ArmV b (pq b p q) → ℚ) (k : Fin b)
    (j : Fin (pq b p q k).length) (a : Fin ((pq b p q k).get j)) :
    (pendantShift b (pq b p q) x *ᵥ z) ⟨k, j, a⟩ =
      (pathShift x ((pq b p q k).get j) *ᵥ (fun c => z ⟨k, j, c⟩)) a := by
  unfold pendantShift
  rw [blockDiagonal_mulVec, blockDiagonal_mulVec]

#print axioms Paper7Reduced.pendant_mulVec_entry

theorem attachment_mulVec_entry (b : ℕ) (p q : Fin b → ℕ)
    (z : ArmV b (pq b p q) → ℚ) (k : Fin b) :
    (attachment b (pq b p q) *ᵥ z) k =
      -(∑ j : Fin (pq b p q k).length, z ⟨k, j, armFirst b p q k j⟩) := by
  classical
  simp only [Matrix.mulVec, dotProduct, Fintype.sum_sigma]
  rw [Fintype.sum_eq_single k, ← Finset.sum_neg_distrib]
  · apply Finset.sum_congr rfl
    intro j _hj
    rw [Fintype.sum_eq_single (armFirst b p q k j)]
    · simp [attachment, armFirst]
    · intro a ha
      have hn : a.val ≠ 0 := by
        intro h
        apply ha
        exact Fin.ext h
      simp [attachment, hn]
  · intro k' hk'
    apply Finset.sum_eq_zero
    intro j _hj
    apply Finset.sum_eq_zero
    intro a _ha
    simp [attachment, hk']

#print axioms Paper7Reduced.attachment_mulVec_entry

theorem attachment_transpose_mulVec_entry (b : ℕ) (p q : Fin b → ℕ)
    (y : Fin b → ℚ) (k : Fin b) (j : Fin (pq b p q k).length)
    (a : Fin ((pq b p q k).get j)) :
    ((attachment (K := ℚ) b (pq b p q)).transpose *ᵥ y) ⟨k, j, a⟩ =
      -(if a.val = 0 then y k else 0) := by
  classical
  by_cases ha : a.val = 0 <;>
    simp [Matrix.mulVec, dotProduct, Matrix.transpose_apply, attachment, ha]

#print axioms Paper7Reduced.attachment_transpose_mulVec_entry

theorem cycleShift_mulVec_entry (b : ℕ) (x : ℚ) (y : Fin b → ℚ) (k : Fin b) :
    (cycleShift b x *ᵥ y) k = x * y k - ((SimpleGraph.cycleGraph b).adjMatrix ℚ *ᵥ y) k := by
  rw [cycleShift, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]
  rfl

#print axioms Paper7Reduced.cycleShift_mulVec_entry

theorem sun_kernel_rows (b : ℕ) (p q : Fin b → ℕ) (hb : 3 ≤ b)
    (x : ℚ) (v : SunV b (pq b p q) → ℚ) :
    (x • (1 : Matrix (SunV b (pq b p q)) (SunV b (pq b p q)) ℚ) -
      (SG b p q).adjMatrix ℚ) *ᵥ v = 0 ↔
    (∀ k, x * v (Sum.inl k) -
      ((SimpleGraph.cycleGraph b).adjMatrix ℚ *ᵥ (v ∘ Sum.inl)) k -
      (∑ j : Fin (pq b p q k).length,
        v (Sum.inr ⟨k, j, armFirst b p q k j⟩)) = 0) ∧
    (∀ k j a, (pathShift x ((pq b p q k).get j) *ᵥ
      (fun c => v (Sum.inr ⟨k, j, c⟩))) a -
      (if a.val = 0 then v (Sum.inl k) else 0) = 0) := by
  rw [sun_shift_fromBlocks b (pq b p q) hb x, block_mulVec_zero_iff]
  constructor
  · rintro ⟨hr, ha⟩
    constructor
    · intro k
      have h := congrFun hr k
      simpa only [Pi.add_apply, Pi.zero_apply, cycleShift_mulVec_entry,
        attachment_mulVec_entry, Function.comp_apply, sub_eq_add_neg] using h
    · intro k j a
      have h := congrFun ha ⟨k, j, a⟩
      simpa only [Pi.add_apply, Pi.zero_apply, pendant_mulVec_entry,
        attachment_transpose_mulVec_entry, Function.comp_apply, sub_eq_add_neg,
        add_comm] using h
  · rintro ⟨hr, ha⟩
    constructor
    · funext k
      simpa only [Pi.add_apply, Pi.zero_apply, cycleShift_mulVec_entry,
        attachment_mulVec_entry, Function.comp_apply, sub_eq_add_neg] using hr k
    · funext a
      rcases a with ⟨k, j, a⟩
      simpa only [Pi.add_apply, Pi.zero_apply, pendant_mulVec_entry,
        attachment_transpose_mulVec_entry, Function.comp_apply, sub_eq_add_neg,
        add_comm] using ha k j a

#print axioms Paper7Reduced.sun_kernel_rows

end Paper7Reduced
