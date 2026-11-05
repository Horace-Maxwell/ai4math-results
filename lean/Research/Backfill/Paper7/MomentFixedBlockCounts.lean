import Research.Backfill.Paper7.DihedralGroupCard
import Research.Backfill.Paper7.FixedCycleBlockWords
import Research.Backfill.Paper7.MomentWordFibres

/-!
Source-only candidate by /root/paper6_tree_actual_final_review/p6_binding_spotcheck.
The imported Stage 01, Stage 02 and Stage 03 proof sources remain pending.
This module has not been compiled or accepted. It retains the literal CandB1
predicate on decoded finite words and on full cycle-block words. Inverse
reindexing in the actual action is explicitly converted to forward word
invariance. No concrete fixed-word or numerical moment count is assumed.
-/
set_option autoImplicit false
noncomputable section

namespace Paper7MomentCounts

open BackfillPaper7.Challenge BackfillPaper7.Challenge.Legacy
open scoped BigOperators Classical

theorem moment_decodeWord_injective (b N : ℕ) :
    Function.Injective (decodeWord (b := b) (N := N)) := by
  intro w v h
  funext i
  apply Prod.ext
  · apply Fin.ext
    exact congrArg (fun x : PQ b => x.1 i) h
  · apply Fin.ext
    exact congrArg (fun x : PQ b => x.2 i) h

#print axioms Paper7MomentCounts.moment_decodeWord_injective

/-- Fixing inverse reindexing is equivalent to forward invariance of the whole letter. -/
theorem reindex_inv_decode_eq_iff (b N : ℕ) (σ : Equiv.Perm (Fin b))
    (w : Fin b → MomentLetter b N) :
    reindex (σ⁻¹ : Equiv.Perm (Fin b)) (decodeWord w) = decodeWord w ↔ ∀ i, w (σ i) = w i := by
  constructor
  · intro h
    change decodeWord (w ∘ σ.symm) = decodeWord w at h
    have he : w ∘ σ.symm = w := moment_decodeWord_injective b N h
    intro i
    have hi := congrFun he (σ i)
    change w (σ.symm (σ i)) = w (σ i) at hi
    simpa only [σ.symm_apply_apply] using hi.symm
  · intro h
    have he : w ∘ σ.symm = w := by
      funext i
      change w (σ.symm i) = w i
      have hi := h (σ.symm i)
      simpa only [σ.apply_symm_apply] using hi.symm
    change decodeWord (w ∘ σ.symm) = decodeWord w
    exact congrArg (decodeWord (b := b) (N := N)) he

#print axioms Paper7MomentCounts.reindex_inv_decode_eq_iff

/-- The fixed points of the actual candidate action, with its action instance explicit. -/
abbrev CandB1FixedBy (b N : ℕ) (hb : 3 ≤ b) (σ : dihedralSubgroup b hb) :=
  ↥(@MulAction.fixedBy (dihedralSubgroup b hb) ↥(CandB1 b N) _
    (candB1DihedralAction b N hb) σ)

#print axioms Paper7MomentCounts.CandB1FixedBy

def candB1FixedPQEquiv (b N : ℕ) (hb : 3 ≤ b) (σ : dihedralSubgroup b hb) :
    CandB1FixedBy b N hb σ ≃
      {x : PQ b // x ∈ CandB1 b N ∧ reindex (σ⁻¹ : dihedralSubgroup b hb).val x = x} where
  toFun x := ⟨x.val.val, x.val.property, by
    exact congrArg Subtype.val x.property⟩
  invFun x := ⟨⟨x.val, x.property.1⟩, by
    apply Subtype.ext
    exact x.property.2⟩
  left_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  right_inv x := by
    apply Subtype.ext
    rfl

#print axioms Paper7MomentCounts.candB1FixedPQEquiv

/-- Budget is supplied by the original candidate predicate before finite encoding. -/
def candB1FixedWordEquiv (b N : ℕ) (hb : 3 ≤ b) (σ : dihedralSubgroup b hb) :
    CandB1FixedBy b N hb σ ≃
      {w : Fin b → MomentLetter b N //
        decodeWord w ∈ CandB1 b N ∧ ∀ i, w (σ.val i) = w i} :=
  (candB1FixedPQEquiv b N hb σ).trans
    ((predicateWordEquiv b N
      (fun x => x ∈ CandB1 b N ∧ reindex (σ⁻¹ : dihedralSubgroup b hb).val x = x)
      (fun _ hx => hx.1.1)).trans
      (Equiv.subtypeEquivRight (fun w => by
        change (decodeWord w ∈ CandB1 b N ∧ reindex (σ.val⁻¹ : Equiv.Perm (Fin b)) (decodeWord w) = decodeWord w) ↔
          (decodeWord w ∈ CandB1 b N ∧ ∀ i, w (σ.val i) = w i)
        exact and_congr_right' (reindex_inv_decode_eq_iff b N σ.val w))))

#print axioms Paper7MomentCounts.candB1FixedWordEquiv

def candB1FixedWordSubtypeEquiv (b N : ℕ) (hb : 3 ≤ b) (σ : dihedralSubgroup b hb) :
    {w : Fin b → MomentLetter b N //
      decodeWord w ∈ CandB1 b N ∧ ∀ i, w (σ.val i) = w i} ≃
      {w : FixedCycleWords σ.val (MomentLetter b N) // decodeWord w.val ∈ CandB1 b N} where
  toFun w := ⟨⟨w.val, w.property.2⟩, w.property.1⟩
  invFun w := ⟨w.val.val, w.property, w.val.property⟩
  left_inv w := by
    apply Subtype.ext
    rfl
  right_inv w := by
    apply Subtype.ext
    apply Subtype.ext
    rfl

#print axioms Paper7MomentCounts.candB1FixedWordSubtypeEquiv

/-- One finite letter per full cycle block, tested with the original decoded predicate. -/
abbrev CandB1BlockWords (b N : ℕ) (hb : 3 ≤ b) (σ : dihedralSubgroup b hb) :=
  {f : CycleBlocks σ.val → MomentLetter b N //
    decodeWord (fun i => f (cycleBlockMk σ.val i)) ∈ CandB1 b N}

#print axioms Paper7MomentCounts.CandB1BlockWords

def candB1FixedWordBlocksEquiv (b N : ℕ) (hb : 3 ≤ b) (σ : dihedralSubgroup b hb) :
    {w : FixedCycleWords σ.val (MomentLetter b N) // decodeWord w.val ∈ CandB1 b N} ≃
      CandB1BlockWords b N hb σ where
  toFun w := ⟨fixedWordToBlocks σ.val w.val, w.property⟩
  invFun f := ⟨blockWordToFixed σ.val f.val, f.property⟩
  left_inv w := by
    apply Subtype.ext
    exact (fixedCycleWordsEquiv σ.val (MomentLetter b N)).left_inv w.val
  right_inv f := by
    apply Subtype.ext
    exact (fixedCycleWordsEquiv σ.val (MomentLetter b N)).right_inv f.val

#print axioms Paper7MomentCounts.candB1FixedWordBlocksEquiv

/-- Full bridge from actual action fixed points to the actual constrained block words. -/
def candB1FixedBlocksEquiv (b N : ℕ) (hb : 3 ≤ b) (σ : dihedralSubgroup b hb) :
    CandB1FixedBy b N hb σ ≃ CandB1BlockWords b N hb σ :=
  (candB1FixedWordEquiv b N hb σ).trans
    ((candB1FixedWordSubtypeEquiv b N hb σ).trans (candB1FixedWordBlocksEquiv b N hb σ))

#print axioms Paper7MomentCounts.candB1FixedBlocksEquiv

theorem candB1_fixedBy_card_eq_blockWords_card (b N : ℕ) (hb : 3 ≤ b)
    (σ : dihedralSubgroup b hb) :
    Fintype.card (@MulAction.fixedBy (dihedralSubgroup b hb) ↥(CandB1 b N) _
      (candB1DihedralAction b N hb) σ) = Fintype.card (CandB1BlockWords b N hb σ) :=
  Fintype.card_congr (candB1FixedBlocksEquiv b N hb σ)

#print axioms Paper7MomentCounts.candB1_fixedBy_card_eq_blockWords_card

theorem candB1_burnside_two_b (b N : ℕ) (hb : 3 ≤ b) (hN : N ≤ 49) :
    (∑ σ : dihedralSubgroup b hb,
      Fintype.card (@MulAction.fixedBy (dihedralSubgroup b hb) ↥(CandB1 b N) _
        (candB1DihedralAction b N hb) σ)) = (canonB1 b N).ncard * (2 * b) :=
  (candB1_burnside b N hb hN).trans
    (congrArg (fun k : ℕ => (canonB1 b N).ncard * k) (dihedralSubgroup_card b hb))

#print axioms Paper7MomentCounts.candB1_burnside_two_b

theorem candB1_blockWord_card_sum (b N : ℕ) (hb : 3 ≤ b) (hN : N ≤ 49) :
    (∑ σ : dihedralSubgroup b hb, Fintype.card (CandB1BlockWords b N hb σ)) =
      (canonB1 b N).ncard * (2 * b) := by
  calc
    (∑ σ : dihedralSubgroup b hb, Fintype.card (CandB1BlockWords b N hb σ)) =
        ∑ σ : dihedralSubgroup b hb,
          Fintype.card (@MulAction.fixedBy (dihedralSubgroup b hb) ↥(CandB1 b N) _
            (candB1DihedralAction b N hb) σ) := by
      apply Finset.sum_congr rfl
      intro σ _hσ
      exact (candB1_fixedBy_card_eq_blockWords_card b N hb σ).symm
    _ = (canonB1 b N).ncard * (2 * b) := candB1_burnside_two_b b N hb hN

#print axioms Paper7MomentCounts.candB1_blockWord_card_sum

end Paper7MomentCounts
