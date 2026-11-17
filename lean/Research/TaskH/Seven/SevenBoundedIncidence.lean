import Mathlib

/-! Finite weight identities on opaque sets and functions. The application
to the original graph must prove its actual row bound separately. -/

set_option autoImplicit false
universe u
namespace TaskH.Seven
open scoped Classical BigOperators

theorem sum_one_plus_indicator {α : Type u} (A : Finset α) (P : α → Prop) :
    (∑ x ∈ A, (1 + if P x then (1 : ℕ) else 0)) =
      A.card + (A.filter P).card := by
  classical
  rw [Finset.sum_add_distrib]
  have hones : (∑ _x ∈ A, (1 : ℕ)) = A.card := by
    simp only [Finset.sum_const, Nat.nsmul_eq_mul, Nat.mul_one]
  have hcount : (∑ x ∈ A, if P x then (1 : ℕ) else 0) = (A.filter P).card := by
    rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  exact congrArg₂ (fun a b : ℕ => a + b) hones hcount

theorem bounded_incidence_sum_le_card_add_ge_two {α : Type u}
    (A : Finset α) (f : α → ℕ) (hf : ∀ x ∈ A, f x ≤ 2) :
    (∑ x ∈ A, f x) ≤ A.card + (A.filter (fun x => 2 ≤ f x)).card := by
  classical
  have hrow : ∀ x ∈ A, f x ≤ 1 + if 2 ≤ f x then 1 else 0 := by
    intro x hx
    have hh := hf x hx
    split_ifs <;> omega
  calc
    _ ≤ ∑ x ∈ A, (1 + if 2 ≤ f x then (1 : ℕ) else 0) :=
      Finset.sum_le_sum hrow
    _ = A.card + (A.filter (fun x => 2 ≤ f x)).card := by
      rw [Finset.sum_add_distrib]
      have hones : (∑ _x ∈ A, (1 : ℕ)) = A.card := by
        simp only [Finset.sum_const, Nat.nsmul_eq_mul, Nat.mul_one]
      have hcount : (∑ x ∈ A, if 2 ≤ f x then (1 : ℕ) else 0) =
          (A.filter (fun x => 2 ≤ f x)).card := by
        rw [Finset.card_eq_sum_ones, Finset.sum_filter]
      exact congrArg₂ (fun a b : ℕ => a + b) hones hcount

end TaskH.Seven

#print axioms TaskH.Seven.sum_one_plus_indicator
#print axioms TaskH.Seven.bounded_incidence_sum_le_card_add_ge_two
