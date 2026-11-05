import Research.Backfill.Paper7.MomentB6ThreePairRoute

/-! Genuine ordered histogram fibres and coordinate-bounded q assignments.
A capacity profile alone is not unique: Q is retained in the signature. -/
set_option autoImplicit false
noncomputable section
namespace Paper7MomentCounts
open Paper7MomentDP
open scoped BigOperators

def b6ThreePairWeight : Fin 16 → ℕ := ![1,1,1,1,1,2,1,2,1,1,2,4,3,3,2,1]
#print axioms Paper7MomentCounts.b6ThreePairWeight

def b6ThreePairCard : Fin 16 → ℕ := ![3,6,3,3,3,6,3,6,6,3,6,3,6,6,6,3]
#print axioms Paper7MomentCounts.b6ThreePairCard

def b6ThreePairSignature (j : Fin 16) : (Fin 19 → ℕ) × ℕ :=
  (finiteValueHistogram (b6ThreePairReference j),b6ThreePairQ j)
#print axioms Paper7MomentCounts.b6ThreePairSignature

theorem b6ThreePairSignature_injective : Function.Injective b6ThreePairSignature := by
  decide +kernel
#print axioms Paper7MomentCounts.b6ThreePairSignature_injective

theorem b6ThreePairReference_fibre_card : ∀ j : Fin 16,
    Fintype.card (BoundedQFibre (b6ThreePairNat j) (b6ThreePairQ j)) =
      b6ThreePairWeight j := by
  decide +kernel
#print axioms Paper7MomentCounts.b6ThreePairReference_fibre_card

theorem b6ThreePairCard_factorials : ∀ j : Fin 16,
    b6ThreePairCard j *
      (∏ v : Fin 19, (finiteValueHistogram (b6ThreePairReference j) v).factorial) = 6 ∧
    0 < (∏ v : Fin 19, (finiteValueHistogram (b6ThreePairReference j) v).factorial) := by
  decide +kernel
#print axioms Paper7MomentCounts.b6ThreePairCard_factorials

theorem b6ThreePairHistogram_card (j : Fin 16) :
    Fintype.card (FiniteHistogramFiber (b6ThreePairReference j)) = b6ThreePairCard j := by
  have h := finiteHistogramFiber_natCard_factorial (b6ThreePairReference j)
  have ht := b6ThreePairCard_factorials j
  calc
    Fintype.card (FiniteHistogramFiber (b6ThreePairReference j)) =
        Nat.card (FiniteHistogramFiber (b6ThreePairReference j)) :=
      (Nat.card_eq_fintype_card).symm
    _ = b6ThreePairCard j := Nat.mul_right_cancel ht.2 (h.trans ht.1.symm)
#print axioms Paper7MomentCounts.b6ThreePairHistogram_card

theorem b6ThreePairHistogram_accept (j : Fin 16)
    (g : FiniteHistogramFiber (b6ThreePairReference j)) :
    B6ThreePairGuard (fun i => (g.val i).val) (b6ThreePairQ j) := by
  obtain ⟨e,he⟩ := finiteValueHistogram_exists_perm (b6ThreePairReference j) g.val g.property
  have hn : (fun i => (g.val i).val) = b6ThreePairNat j ∘ e := by
    funext i
    exact congrArg Fin.val (congrFun he i)
  rw [hn,b6ThreePairGuard_comp_perm]
  exact b6ThreePairReference_accept j
#print axioms Paper7MomentCounts.b6ThreePairHistogram_accept

theorem b6ThreePairHistogram_weight (j : Fin 16)
    (g : FiniteHistogramFiber (b6ThreePairReference j)) :
    Nat.card (BoundedQFibre (fun i => (g.val i).val) (b6ThreePairQ j)) =
      b6ThreePairWeight j := by
  obtain ⟨e,he⟩ := finiteValueHistogram_exists_perm (b6ThreePairReference j) g.val g.property
  have hn : (fun i => (g.val i).val) = b6ThreePairNat j ∘ e := by
    funext i
    exact congrArg Fin.val (congrFun he i)
  rw [hn]
  calc
    Nat.card (BoundedQFibre (b6ThreePairNat j ∘ e) (b6ThreePairQ j)) =
        Nat.card (BoundedQFibre (b6ThreePairNat j) (b6ThreePairQ j)) :=
      Nat.card_congr (Paper7MomentReduction.boundedQFibrePermEquiv
        (b6ThreePairNat j) (b6ThreePairQ j) e).symm
    _ = b6ThreePairWeight j := by
      rw [Nat.card_eq_fintype_card]
      exact b6ThreePairReference_fibre_card j
#print axioms Paper7MomentCounts.b6ThreePairHistogram_weight

theorem b6ThreePair_weighted_sum :
    (∑ j : Fin 16,b6ThreePairCard j*b6ThreePairWeight j) = 129 := by
  decide +kernel
#print axioms Paper7MomentCounts.b6ThreePair_weighted_sum

end Paper7MomentCounts
