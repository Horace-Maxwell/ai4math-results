import Mathlib

/-! Uncompiled generic finite-sum equivalence layer. The computation reuses the
existing Nat.binaryRec with constant motive Nat → Int. No new well-founded
recursive definition, concrete theta evaluation or resource option is added.
The library still has its own termination machinery; kernel cost and any
improvement for the actual952 failure remain unmeasured. -/
set_option autoImplicit false
namespace Paper7MomentCounts
open scoped BigOperators

def b6BalancedRangeOffset (f : ℕ → ℤ) (n : ℕ) : ℕ → ℤ :=
  Nat.binaryRec (motive := fun _ => ℕ → ℤ)
    (fun _ => 0)
    (fun b k ih a => ih a + ih (a+k) +
      (bif b then f (a+(k+k)) else 0)) n
#print axioms Paper7MomentCounts.b6BalancedRangeOffset

theorem b6BalancedRangeOffset_zero (f : ℕ → ℤ) (a : ℕ) :
    b6BalancedRangeOffset f 0 a = 0 := rfl
#print axioms Paper7MomentCounts.b6BalancedRangeOffset_zero

theorem b6BalancedRangeOffset_bit (f : ℕ → ℤ) (b : Bool) (n a : ℕ) :
    b6BalancedRangeOffset f (Nat.bit b n) a =
      b6BalancedRangeOffset f n a + b6BalancedRangeOffset f n (a+n) +
        (bif b then f (a+(n+n)) else 0) := by
  unfold b6BalancedRangeOffset
  exact congrArg (fun g : ℕ → ℤ => g a)
    (Nat.binaryRec_eq (motive := fun _ => ℕ → ℤ)
      (zero := fun _ => 0)
      (bit := fun b k ih a => ih a + ih (a+k) +
        (bif b then f (a+(k+k)) else 0))
      b n (Or.inl (by funext _a; rfl)))
#print axioms Paper7MomentCounts.b6BalancedRangeOffset_bit

theorem b6BalancedRangeOffset_eq_sum_range (f : ℕ → ℤ) (n a : ℕ) :
    b6BalancedRangeOffset f n a = ∑ i ∈ Finset.range n, f (a+i) := by
  induction n using Nat.binaryRec generalizing a with
  | zero =>
    exact (b6BalancedRangeOffset_zero f a).trans
      (Finset.sum_range_zero (fun i => f (a+i))).symm
  | bit b n ih =>
    rw [b6BalancedRangeOffset_bit,ih a,ih (a+n)]
    cases b with
    | false =>
      change (∑ i ∈ Finset.range n, f (a+i)) +
          (∑ i ∈ Finset.range n, f (a+n+i)) + (0 : ℤ) =
        ∑ i ∈ Finset.range (2*n), f (a+i)
      rw [add_zero,Nat.two_mul,Finset.sum_range_add]
      simp only [Nat.add_assoc]
    | true =>
      change (∑ i ∈ Finset.range n, f (a+i)) +
          (∑ i ∈ Finset.range n, f (a+n+i)) + f (a+(n+n)) =
        ∑ i ∈ Finset.range (2*n+1), f (a+i)
      rw [Nat.two_mul,Finset.sum_range_succ,Finset.sum_range_add]
      simp only [Nat.add_assoc]
#print axioms Paper7MomentCounts.b6BalancedRangeOffset_eq_sum_range

theorem b6BalancedRangeOffset_eq_range (f : ℕ → ℤ) (n : ℕ) :
    b6BalancedRangeOffset f n 0 = ∑ i ∈ Finset.range n, f i := by
  simpa only [Nat.zero_add] using b6BalancedRangeOffset_eq_sum_range f n 0
#print axioms Paper7MomentCounts.b6BalancedRangeOffset_eq_range

def b6BalancedIcoSum (f : ℕ → ℤ) (a b : ℕ) : ℤ :=
  b6BalancedRangeOffset f (b-a) a
#print axioms Paper7MomentCounts.b6BalancedIcoSum

theorem b6BalancedIcoSum_eq (f : ℕ → ℤ) (a b : ℕ) :
    b6BalancedIcoSum f a b = ∑ i ∈ Finset.Ico a b, f i := by
  calc
    b6BalancedIcoSum f a b = ∑ i ∈ Finset.range (b-a), f (a+i) :=
      b6BalancedRangeOffset_eq_sum_range f (b-a) a
    _ = ∑ i ∈ Finset.Ico a b, f i :=
      (Finset.sum_Ico_eq_sum_range f a b).symm
#print axioms Paper7MomentCounts.b6BalancedIcoSum_eq

end Paper7MomentCounts
