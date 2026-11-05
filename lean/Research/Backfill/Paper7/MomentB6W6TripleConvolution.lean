import Research.Backfill.Paper7.MomentB6W6QSplitEquiv

/-! NEW uncompiled candidate. Unit 3: finite cardinal transport of the
actual bounded-q split. This is not a numerical certificate. -/
set_option autoImplicit false
noncomputable section
namespace Paper7MomentCounts
open scoped BigOperators Classical

theorem labelledTripleQWeight_convolution_W6 (u v : ℕ × ℕ × ℕ) (Q : ℕ) :
    (∑ t ∈ b6W6QSplitRange u v Q,
      labelledTripleQWeight u.1 u.2.1 u.2.2 t *
        labelledTripleQWeight v.1 v.2.1 v.2.2 (Q - t)) =
      labelledSixQWeight (b6W6JoinedCapacity u v) Q := by
  symm
  calc
    labelledSixQWeight (b6W6JoinedCapacity u v) Q =
        (Nat.card (B6W6BoundedFibre u v Q) : ℤ) :=
      labelledSixQWeight_eq_actual_card (b6W6JoinedCapacity u v) Q
    _ = (Nat.card (B6W6QSplitPair u v Q) : ℤ) :=
      congrArg (fun k : ℕ => (k : ℤ)) (Nat.card_congr (b6W6QSplitEquiv u v Q))
    _ = ∑ t : ↥(b6W6QSplitRange u v Q),
        labelledTripleQWeight u.1 u.2.1 u.2.2 t.val *
          labelledTripleQWeight v.1 v.2.1 v.2.2 (Q - t.val) := by
      rw [Nat.card_sigma, Nat.cast_sum]
      apply Finset.sum_congr rfl
      intro t _ht
      rw [Nat.card_prod, Nat.cast_mul,
        labelledTripleQFiber_card_eq_weight, labelledTripleQFiber_card_eq_weight]
    _ = ∑ t ∈ b6W6QSplitRange u v Q,
        labelledTripleQWeight u.1 u.2.1 u.2.2 t *
          labelledTripleQWeight v.1 v.2.1 v.2.2 (Q - t) :=
      Finset.sum_coe_sort (b6W6QSplitRange u v Q) (fun t : ℕ =>
        labelledTripleQWeight u.1 u.2.1 u.2.2 t *
          labelledTripleQWeight v.1 v.2.1 v.2.2 (Q - t))
#print axioms Paper7MomentCounts.labelledTripleQWeight_convolution_W6

end Paper7MomentCounts
