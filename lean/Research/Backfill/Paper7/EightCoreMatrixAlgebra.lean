import Mathlib

/-! Source-only small algebra lemmas, isolated from graph and concrete matrix
definitions so their proof terms are checked once before matrix assembly. -/
set_option autoImplicit false
noncomputable section
namespace Paper7EightCycle
open Polynomial

theorem eight_core_diag_factor (x a b : Polynomial ℤ) :
    x*(x^2-1)*(x-a)-b*(x^2-1) = (x^2-1)*(x^2-b-x*a) := by
  ring
#print axioms Paper7EightCycle.eight_core_diag_factor

theorem eight_core_off_factor (x a : Polynomial ℤ) :
    x*(x^2-1)*(0-a) = (x^2-1)*(0-x*a) := by
  ring
#print axioms Paper7EightCycle.eight_core_off_factor

theorem eight_core_scaled_det {n R : Type*} [DecidableEq n] [Fintype n] [CommRing R]
    (A : Matrix n n R) (s : R) : (s • A).det = s^(Fintype.card n)*A.det :=
  Matrix.det_smul A s
#print axioms Paper7EightCycle.eight_core_scaled_det

theorem eight_core_det_card_transport {n R : Type*} [DecidableEq n] [Fintype n]
    [CommRing R] (A : Matrix n n R) (s : R) (k : ℕ) (hk : Fintype.card n = k) :
    (s • A).det = s^k*A.det := by
  calc
    (s • A).det = s^(Fintype.card n)*A.det := eight_core_scaled_det A s
    _ = s^k*A.det := congrArg (fun exponent : ℕ => s^exponent*A.det) hk
#print axioms Paper7EightCycle.eight_core_det_card_transport

theorem eight_core_det_of_smul_eq {n R : Type*} [DecidableEq n] [Fintype n] [CommRing R]
    (A B : Matrix n n R) (s : R) (k : ℕ) (hk : Fintype.card n = k)
    (h : A = s • B) : A.det = s^k*B.det := by
  calc
    A.det = (s • B).det := congrArg Matrix.det h
    _ = s^k*B.det := eight_core_det_card_transport B s k hk
#print axioms Paper7EightCycle.eight_core_det_of_smul_eq

end Paper7EightCycle
