import Mathlib

/-! Uncompiled generic alternative to the sum recursion in Nat.binaryRec.
Only this sum's recursion is explicitly structural in fuel. No claim is made
about proof machinery in Nat.div, sqrt or other library operations. The raw
fuel invariant is internal; the public entry chooses fuel=n and has no bound
premise. No concrete numerical candidate or resource option is introduced. -/
set_option autoImplicit false
namespace Paper7MomentCounts
open scoped BigOperators

def b6StructuralFuelSum (f : ℕ → ℤ) (fuel n a : ℕ) : ℤ :=
  match fuel with
  | 0 => 0
  | fuel+1 =>
    if n=0 then 0 else if n=1 then f a else
      b6StructuralFuelSum f fuel (n/2) a +
        b6StructuralFuelSum f fuel (n-n/2) (a+n/2)
termination_by structural fuel
#print axioms Paper7MomentCounts.b6StructuralFuelSum

theorem b6StructuralFuelSum_eq (f : ℕ → ℤ) (fuel n a : ℕ) (hn : n ≤ fuel) :
    b6StructuralFuelSum f fuel n a = ∑ i ∈ Finset.range n, f (a+i) := by
  induction fuel generalizing n a with
  | zero =>
    have h : n=0 := by omega
    subst n
    simp [b6StructuralFuelSum]
  | succ fuel ih =>
    by_cases h0 : n=0
    · subst n
      simp [b6StructuralFuelSum]
    · by_cases h1 : n=1
      · subst n
        simp [b6StructuralFuelSum]
      · have hl : n/2 ≤ fuel := by omega
        have hr : n-n/2 ≤ fuel := by omega
        have hs : n/2+(n-n/2)=n := by omega
        rw [b6StructuralFuelSum, ite_eq_right h0, ite_eq_right h1,
          ih (n/2) a hl, ih (n-n/2) (a+n/2) hr]
        calc
          _ = ∑ i ∈ Finset.range (n/2+(n-n/2)), f (a+i) := by
            rw [Finset.sum_range_add]
            simp only [Nat.add_assoc]
          _ = ∑ i ∈ Finset.range n, f (a+i) := by rw [hs]
#print axioms Paper7MomentCounts.b6StructuralFuelSum_eq

def b6StructuralRangeOffset (f : ℕ → ℤ) (n a : ℕ) : ℤ :=
  b6StructuralFuelSum f n n a
#print axioms Paper7MomentCounts.b6StructuralRangeOffset

theorem b6StructuralRangeOffset_eq (f : ℕ → ℤ) (n a : ℕ) :
    b6StructuralRangeOffset f n a = ∑ i ∈ Finset.range n, f (a+i) := by
  exact b6StructuralFuelSum_eq f n n a le_rfl
#print axioms Paper7MomentCounts.b6StructuralRangeOffset_eq

theorem b6StructuralRangeOffset_zero_eq (f : ℕ → ℤ) (n : ℕ) :
    b6StructuralRangeOffset f n 0 = ∑ i ∈ Finset.range n, f i := by
  simpa only [Nat.zero_add] using b6StructuralRangeOffset_eq f n 0
#print axioms Paper7MomentCounts.b6StructuralRangeOffset_zero_eq

def b6StructuralIcoSum (f : ℕ → ℤ) (a b : ℕ) : ℤ :=
  b6StructuralRangeOffset f (b-a) a
#print axioms Paper7MomentCounts.b6StructuralIcoSum

theorem b6StructuralIcoSum_eq (f : ℕ → ℤ) (a b : ℕ) :
    b6StructuralIcoSum f a b = ∑ i ∈ Finset.Ico a b, f i := by
  calc
    b6StructuralIcoSum f a b = ∑ i ∈ Finset.range (b-a), f (a+i) :=
      b6StructuralRangeOffset_eq f (b-a) a
    _ = ∑ i ∈ Finset.Ico a b, f i :=
      (Finset.sum_Ico_eq_sum_range f a b).symm
#print axioms Paper7MomentCounts.b6StructuralIcoSum_eq

end Paper7MomentCounts
