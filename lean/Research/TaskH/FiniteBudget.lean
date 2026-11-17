import Research.TaskH.Challenge

/-!
A finite-relation saturation lemma for the actual good-cycle double count.
This generic helper is not a substitute for constructing the graph's good
relation or proving its row and column bounds from the original hypotheses.
-/

set_option autoImplicit false

universe u v

namespace TaskH.FiniteBudget

variable {α : Type u} {β : Type v}

open scoped Classical in
theorem relation_double_count (A : Finset α) (C : Finset β) (R : α → β → Prop) :
    (∑ a ∈ A, (C.filter (R a)).card) =
      ∑ c ∈ C, (A.filter (fun a => R a c)).card := by
  classical
  simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
  exact Finset.sum_comm

open scoped Classical in
theorem columns_saturated (A : Finset α) (C : Finset β) (R : α → β → Prop)
    (L U : ℕ) (hbalance : A.card * L = C.card * U)
    (hrow : ∀ a ∈ A, L ≤ (C.filter (R a)).card)
    (hcol : ∀ c ∈ C, (A.filter (fun a => R a c)).card ≤ U) :
    ∀ c ∈ C, (A.filter (fun a => R a c)).card = U := by
  classical
  have hlo : C.card * U ≤ ∑ c ∈ C, (A.filter (fun a => R a c)).card := by
    calc
      C.card * U = ∑ _a ∈ A, L := by simpa using hbalance.symm
      _ ≤ ∑ a ∈ A, (C.filter (R a)).card := Finset.sum_le_sum hrow
      _ = ∑ c ∈ C, (A.filter (fun a => R a c)).card := relation_double_count A C R
  have hhi : (∑ c ∈ C, (A.filter (fun a => R a c)).card) ≤ C.card * U := by
    calc
      (∑ c ∈ C, (A.filter (fun a => R a c)).card) ≤ ∑ _c ∈ C, U :=
        Finset.sum_le_sum hcol
      _ = C.card * U := by simp
  have heq : (∑ c ∈ C, (A.filter (fun a => R a c)).card) = ∑ _c ∈ C, U := by
    simpa using Nat.le_antisymm hhi hlo
  exact (Finset.sum_eq_sum_iff_of_le hcol).mp heq

open scoped Classical in
theorem twenty_four_fifteen_columns_eq_eight
    (A : Finset α) (C : Finset β) (R : α → β → Prop)
    (hA : A.card = 24) (hC : C.card = 15)
    (hrow : ∀ a ∈ A, 5 ≤ (C.filter (R a)).card)
    (hcol : ∀ c ∈ C, (A.filter (fun a => R a c)).card ≤ 8) :
    ∀ c ∈ C, (A.filter (fun a => R a c)).card = 8 := by
  classical
  apply columns_saturated A C R 5 8 _ hrow hcol
  simp [hA, hC]

end TaskH.FiniteBudget

#print axioms TaskH.FiniteBudget.relation_double_count
#print axioms TaskH.FiniteBudget.columns_saturated
#print axioms TaskH.FiniteBudget.twenty_four_fifteen_columns_eq_eight
