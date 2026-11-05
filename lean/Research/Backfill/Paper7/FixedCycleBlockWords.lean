import Research.Backfill.Paper7.FiniteWordCountDP

/-!
Source-only candidate by /root/paper6_tree_actual_final_review/p6_binding_spotcheck.
The imported Stage 02 FiniteWordCountDP remains a pending source candidate.
This module has not been compiled or accepted. Cycle blocks are the full
SameCycle quotient, including singleton blocks at every fixed point. No concrete
cycle-type enumeration or numerical moment-count certificate is assumed.
-/
set_option autoImplicit false
noncomputable section

namespace Paper7MomentCounts

open scoped BigOperators Classical

/-- All cycles of the actual permutation, including fixed-point singleton cycles. -/
abbrev CycleBlocks {b : ℕ} (σ : Equiv.Perm (Fin b)) :=
  Quotient (Equiv.Perm.SameCycle.setoid σ)

#print axioms Paper7MomentCounts.CycleBlocks

instance cycleBlocksFintype {b : ℕ} (σ : Equiv.Perm (Fin b)) :
    Fintype (CycleBlocks σ) := Fintype.ofFinite _

#print axioms Paper7MomentCounts.cycleBlocksFintype

def cycleBlockMk {b : ℕ} (σ : Equiv.Perm (Fin b)) (i : Fin b) : CycleBlocks σ :=
  Quotient.mk (Equiv.Perm.SameCycle.setoid σ) i

#print axioms Paper7MomentCounts.cycleBlockMk

/-- Words genuinely fixed by the supplied permutation. -/
abbrev FixedCycleWords {b : ℕ} (σ : Equiv.Perm (Fin b)) (A : Type*) :=
  {w : Fin b → A // ∀ i, w (σ i) = w i}

#print axioms Paper7MomentCounts.FixedCycleWords

instance fixedCycleWordsFintype {b : ℕ} (σ : Equiv.Perm (Fin b))
    (A : Type*) [Fintype A] : Fintype (FixedCycleWords σ A) := Fintype.ofFinite _

#print axioms Paper7MomentCounts.fixedCycleWordsFintype

theorem fixedWord_pow_apply {b : ℕ} {A : Type*} (σ : Equiv.Perm (Fin b))
    (w : FixedCycleWords σ A) (n : ℕ) (i : Fin b) :
    w.val ((σ ^ n) i) = w.val i := by
  induction n with
  | zero => rfl
  | succ n ih =>
    calc
      w.val ((σ ^ (n + 1)) i) = w.val (σ ((σ ^ n) i)) := by
        rw [pow_succ', Equiv.Perm.mul_apply]
      _ = w.val ((σ ^ n) i) := w.property _
      _ = w.val i := ih

#print axioms Paper7MomentCounts.fixedWord_pow_apply

theorem fixedWord_sameCycle {b : ℕ} {A : Type*} (σ : Equiv.Perm (Fin b))
    (w : FixedCycleWords σ A) {i j : Fin b} (h : σ.SameCycle i j) :
    w.val i = w.val j := by
  obtain ⟨n, hn⟩ := h.exists_nat_pow_eq
  exact (fixedWord_pow_apply σ w n i).symm.trans (congrArg w.val hn)

#print axioms Paper7MomentCounts.fixedWord_sameCycle

def fixedWordToBlocks {b : ℕ} {A : Type*} (σ : Equiv.Perm (Fin b))
    (w : FixedCycleWords σ A) : CycleBlocks σ → A :=
  Quotient.lift w.val (fun _ _ h => fixedWord_sameCycle σ w h)

#print axioms Paper7MomentCounts.fixedWordToBlocks

theorem fixedWordToBlocks_mk {b : ℕ} {A : Type*} (σ : Equiv.Perm (Fin b))
    (w : FixedCycleWords σ A) (i : Fin b) :
    fixedWordToBlocks σ w (cycleBlockMk σ i) = w.val i := rfl

#print axioms Paper7MomentCounts.fixedWordToBlocks_mk

def blockWordToFixed {b : ℕ} {A : Type*} (σ : Equiv.Perm (Fin b))
    (f : CycleBlocks σ → A) : FixedCycleWords σ A :=
  ⟨fun i => f (cycleBlockMk σ i), by
    intro i
    apply congrArg f
    apply Quotient.sound
    exact Equiv.Perm.sameCycle_apply_left.mpr (Equiv.Perm.SameCycle.refl σ i)⟩

#print axioms Paper7MomentCounts.blockWordToFixed

/-- Quotient descent and pullback are explicit inverse maps on actual words. -/
def fixedCycleWordsEquiv {b : ℕ} (σ : Equiv.Perm (Fin b)) (A : Type*) :
    FixedCycleWords σ A ≃ (CycleBlocks σ → A) where
  toFun := fixedWordToBlocks σ
  invFun := blockWordToFixed σ
  left_inv w := by
    apply Subtype.ext
    funext i
    rfl
  right_inv f := by
    funext o
    refine Quotient.inductionOn o ?_
    intro i
    rfl

#print axioms Paper7MomentCounts.fixedCycleWordsEquiv

theorem fixedCycleWords_card {b : ℕ} (σ : Equiv.Perm (Fin b))
    (A : Type*) [Fintype A] :
    Fintype.card (FixedCycleWords σ A) =
      Fintype.card A ^ Fintype.card (CycleBlocks σ) := by
  calc
    Fintype.card (FixedCycleWords σ A) = Fintype.card (CycleBlocks σ → A) :=
      Fintype.card_congr (fixedCycleWordsEquiv σ A)
    _ = Fintype.card A ^ Fintype.card (CycleBlocks σ) := Fintype.card_fun

#print axioms Paper7MomentCounts.fixedCycleWords_card

/-- The actual fibre of the quotient map, as a finite set of original positions. -/
def cycleBlock {b : ℕ} (σ : Equiv.Perm (Fin b)) (o : CycleBlocks σ) :
    Finset (Fin b) := Finset.univ.filter (fun i => cycleBlockMk σ i = o)

#print axioms Paper7MomentCounts.cycleBlock

theorem fixedWord_eq_blockValue {b : ℕ} {A : Type*} (σ : Equiv.Perm (Fin b))
    (w : FixedCycleWords σ A) (o : CycleBlocks σ) (i : Fin b)
    (hi : i ∈ cycleBlock σ o) : w.val i = fixedWordToBlocks σ w o := by
  have he : cycleBlockMk σ i = o := (Finset.mem_filter.mp hi).2
  exact (fixedWordToBlocks_mk σ w i).symm.trans
    (congrArg (fixedWordToBlocks σ w) he)

#print axioms Paper7MomentCounts.fixedWord_eq_blockValue

/-- The original word statistic is the sum of block sizes times their common values. -/
theorem fixedCycleWords_wordSum {b : ℕ} {A Γ : Type*} [AddCommMonoid Γ]
    (σ : Equiv.Perm (Fin b)) (c : A → Γ) (w : FixedCycleWords σ A) :
    Paper7MomentDP.wordSum c w.val =
      ∑ o : CycleBlocks σ, (cycleBlock σ o).card • c (fixedWordToBlocks σ w o) := by
  unfold Paper7MomentDP.wordSum
  calc
    (∑ i, c (w.val i)) = ∑ o : CycleBlocks σ, ∑ i ∈ cycleBlock σ o, c (w.val i) :=
      (Finset.sum_fiberwise Finset.univ (cycleBlockMk σ) (fun i => c (w.val i))).symm
    _ = ∑ o : CycleBlocks σ, (cycleBlock σ o).card • c (fixedWordToBlocks σ w o) := by
      apply Finset.sum_congr rfl
      intro o _ho
      calc
        (∑ i ∈ cycleBlock σ o, c (w.val i)) =
            ∑ _i ∈ cycleBlock σ o, c (fixedWordToBlocks σ w o) := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [fixedWord_eq_blockValue σ w o i hi]
        _ = (cycleBlock σ o).card • c (fixedWordToBlocks σ w o) := Finset.sum_const _

#print axioms Paper7MomentCounts.fixedCycleWords_wordSum

/-- Identity cycles are precisely all original positions, even when b = 0. -/
def identityCycleBlocksEquiv (b : ℕ) :
    CycleBlocks (1 : Equiv.Perm (Fin b)) ≃ Fin b where
  toFun := Quotient.lift (fun i => i)
    (fun _ _ h => Equiv.Perm.sameCycle_one.mp h)
  invFun := cycleBlockMk (1 : Equiv.Perm (Fin b))
  left_inv o := by
    refine Quotient.inductionOn o ?_
    intro i
    rfl
  right_inv i := rfl

#print axioms Paper7MomentCounts.identityCycleBlocksEquiv

theorem cycleBlocks_identity_card (b : ℕ) :
    Fintype.card (CycleBlocks (1 : Equiv.Perm (Fin b))) = b :=
  (Fintype.card_congr (identityCycleBlocksEquiv b)).trans (Fintype.card_fin b)

#print axioms Paper7MomentCounts.cycleBlocks_identity_card

theorem fixedCycleWords_identity_card (b : ℕ) (A : Type*) [Fintype A] :
    Fintype.card (FixedCycleWords (1 : Equiv.Perm (Fin b)) A) = Fintype.card A ^ b := by
  rw [fixedCycleWords_card, cycleBlocks_identity_card]

#print axioms Paper7MomentCounts.fixedCycleWords_identity_card

end Paper7MomentCounts
