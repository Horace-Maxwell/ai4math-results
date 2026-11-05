import Mathlib

/-! Computable integer coefficients with a proof against the actual polynomial
product. No root table, search outcome or graph assertion occurs in this module. -/
set_option autoImplicit false
namespace Paper7CycleThreeCertificate
open Polynomial

def rootCoefficient : List ℤ → ℕ → ℤ
  | [], n => if n = 0 then 1 else 0
  | z :: a, 0 => -z * rootCoefficient a 0
  | z :: a, n + 1 => rootCoefficient a n - z * rootCoefficient a (n + 1)
#print axioms Paper7CycleThreeCertificate.rootCoefficient

theorem rootCoefficient_eq (a : List ℤ) (n : ℕ) :
    rootCoefficient a n = ((a.map (fun z => (X - C z : Polynomial ℤ))).prod).coeff n := by
  induction a generalizing n with
  | nil => simp only [rootCoefficient, List.map_nil, List.prod_nil, Polynomial.coeff_one]
  | cons z a ih =>
    cases n with
    | zero =>
      simp [rootCoefficient, Polynomial.mul_coeff_zero, ih]
    | succ n =>
      simpa only [rootCoefficient, List.map_cons, List.prod_cons,
        Polynomial.coeff_X_sub_C_mul] using
        congrArg₂ (fun r s : ℤ => r - z * s) (ih n) (ih (n + 1))
#print axioms Paper7CycleThreeCertificate.rootCoefficient_eq

/-- The exact two coefficient patterns used by Generator02. The lower bounds
on T come from natural parameters; its upper bound comes from order<=49. -/
def rootPattern (a : List ℤ) : Prop :=
  a.length = 8 ∧ a.sum = 0 ∧ rootCoefficient a 7 = 0 ∧
    rootCoefficient a 5 = -2 ∧ 0 ≤ rootCoefficient a 0 ∧
    ((rootCoefficient a 3 = 2 ∧ rootCoefficient a 1 = 0 ∧
        0 ≤ -rootCoefficient a 6 - 4 ∧ -rootCoefficient a 6 - 4 ≤ 46) ∨
     (rootCoefficient a 3 = 4 ∧ rootCoefficient a 1 = -2 ∧
        0 ≤ -rootCoefficient a 6 - 5 ∧ -rootCoefficient a 6 - 5 ≤ 46))
#print axioms Paper7CycleThreeCertificate.rootPattern

instance instDecidableRootPattern (a : List ℤ) : Decidable (rootPattern a) := by
  unfold rootPattern
  infer_instance
#print axioms Paper7CycleThreeCertificate.instDecidableRootPattern

/-- A table is arbitrary data. Its completeness must be checked separately. -/
def rootLeafCheck (rows : List (List ℤ)) (a : List ℤ) : Bool :=
  if rootPattern a then decide (a ∈ rows) else true
#print axioms Paper7CycleThreeCertificate.rootLeafCheck

theorem rootLeafCheck_sound (rows : List (List ℤ)) (a : List ℤ)
    (hcheck : rootLeafCheck rows a = true) (hpattern : rootPattern a) : a ∈ rows := by
  simpa only [rootLeafCheck, ite_eq_left hpattern, decide_eq_true_eq] using hcheck
#print axioms Paper7CycleThreeCertificate.rootLeafCheck_sound

end Paper7CycleThreeCertificate
