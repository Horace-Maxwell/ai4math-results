import Research.Backfill.Paper7.MomentB6TenProfileWeights

/-! Source-only exact ordered-position counts, obtained from the generic
histogram/permutation equivalence. No exhaustive list of six-tuples is assumed. -/
set_option autoImplicit false
noncomputable section
namespace Paper7MomentCounts
open scoped BigOperators Classical

def b6TenProfileCard : Fin 14 → ℕ := ![60,30,120,60,180,30,15,120,120,180,180,60,90,60]
#print axioms Paper7MomentCounts.b6TenProfileCard

def b6TenProfileStabilizerCard : Fin 14 → ℕ := ![12,24,6,12,4,24,48,6,6,4,4,12,8,12]
#print axioms Paper7MomentCounts.b6TenProfileStabilizerCard

theorem b6TenProfile_factorials : ∀ j : Fin 14,
    (∏ v : Fin 8, (b6TenProfile j v).factorial) = b6TenProfileStabilizerCard j := by
  decide
#print axioms Paper7MomentCounts.b6TenProfile_factorials

theorem finiteHistogramFiber_natCard_factorial
    {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β] (f : α → β) :
    Nat.card (FiniteHistogramFiber f) * (∏ b, (finiteValueHistogram f b).factorial) =
      (Fintype.card α).factorial := by
  rw [Nat.card_eq_fintype_card]
  exact finiteHistogramFiber_card_factorial f
#print axioms Paper7MomentCounts.finiteHistogramFiber_natCard_factorial

theorem b6TenHistogram_member_card (j : Fin 14) :
    Fintype.card (FiniteHistogramFiber (b6TenReference j)) = b6TenProfileCard j := by
  have h := finiteHistogramFiber_natCard_factorial (b6TenReference j)
  have hp : (∏ b : Fin 8, (finiteValueHistogram (b6TenReference j) b).factorial) =
      b6TenProfileStabilizerCard j := by
    rw [b6TenReference_histogram, b6TenProfile_factorials]
  rw [hp] at h
  have hcancel : ∀ c : ℕ, c * b6TenProfileStabilizerCard j =
      (Fintype.card (Fin 6)).factorial → c = b6TenProfileCard j := by
    intro c hc
    change c * b6TenProfileStabilizerCard j = 720 at hc
    fin_cases j <;> norm_num [b6TenProfileStabilizerCard, b6TenProfileCard] at hc ⊢ <;> omega
  calc
    Fintype.card (FiniteHistogramFiber (b6TenReference j)) =
        Nat.card (FiniteHistogramFiber (b6TenReference j)) :=
      (Nat.card_eq_fintype_card).symm
    _ = b6TenProfileCard j := hcancel _ h
#print axioms Paper7MomentCounts.b6TenHistogram_member_card

theorem b6TenProfile_weighted_sum :
    (∑ j : Fin 14, b6TenProfileCard j * b6TenProfileWeight j) = 7485 := by
  decide
#print axioms Paper7MomentCounts.b6TenProfile_weighted_sum

end Paper7MomentCounts
