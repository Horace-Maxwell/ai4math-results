import Research.Backfill.Paper7.AdmissibleMultisetCounts

/-! NEW SOURCE ONLY. Integer square lower bounds used for the actual spectrum. -/
set_option autoImplicit false
noncomputable section
namespace Paper7EightCycle
open scoped Classical

theorem square_floor_sixteen (s : Multiset ℝ)
    (h : ∀ x ∈ s, 2 ≤ x ∧ ∃ z : ℤ, x = z) :
    16*(s.card : ℝ) ≤ Paper7Admissible.squareSum s+
      12*(s.count 2 : ℝ)+7*(s.count 3 : ℝ) := by
  revert h
  induction s using Multiset.induction_on with
  | empty => intro _; simp [Paper7Admissible.squareSum]
  | @cons x s ih =>
    intro h
    have ht := ih (fun y hy => h y (Multiset.mem_cons_of_mem hy))
    obtain ⟨hx,hint⟩ := h x (Multiset.mem_cons_self x s)
    by_cases h2 : x = 2
    · subst x
      norm_num [Paper7Admissible.squareSum,Multiset.count_cons] at ht ⊢
      linarith
    by_cases h3 : x = 3
    · subst x
      norm_num [Paper7Admissible.squareSum,Multiset.count_cons] at ht ⊢
      linarith
    have hx4 : 4 ≤ x := by
      obtain ⟨z,rfl⟩ := hint
      have hz : (2 : ℤ) ≤ z := by exact_mod_cast hx
      have hz2 : z ≠ 2 := by exact_mod_cast h2
      have hz3 : z ≠ 3 := by exact_mod_cast h3
      exact_mod_cast (show (4 : ℤ) ≤ z by omega)
    have hc2 := Multiset.count_cons_of_ne (Ne.symm h2) s
    have hc3 := Multiset.count_cons_of_ne (Ne.symm h3) s
    simp only [Paper7Admissible.squareSum,Multiset.map_cons,Multiset.sum_cons,
      Multiset.card_cons,Nat.cast_add,Nat.cast_one,hc2,hc3] at ht ⊢
    nlinarith
#print axioms Paper7EightCycle.square_floor_sixteen

theorem square_floor_twenty_five (s : Multiset ℝ)
    (h : ∀ x ∈ s, 2 ≤ x ∧ ∃ z : ℤ, x = z) :
    25*(s.card : ℝ) ≤ Paper7Admissible.squareSum s+
      21*(s.count 2 : ℝ)+16*(s.count 3 : ℝ)+9*(s.count 4 : ℝ) := by
  revert h
  induction s using Multiset.induction_on with
  | empty => intro _; simp [Paper7Admissible.squareSum]
  | @cons x s ih =>
    intro h
    have ht := ih (fun y hy => h y (Multiset.mem_cons_of_mem hy))
    obtain ⟨hx,hint⟩ := h x (Multiset.mem_cons_self x s)
    by_cases h2 : x = 2
    · subst x
      norm_num [Paper7Admissible.squareSum,Multiset.count_cons] at ht ⊢
      linarith
    by_cases h3 : x = 3
    · subst x
      norm_num [Paper7Admissible.squareSum,Multiset.count_cons] at ht ⊢
      linarith
    by_cases h4 : x = 4
    · subst x
      norm_num [Paper7Admissible.squareSum,Multiset.count_cons] at ht ⊢
      linarith
    have hx5 : 5 ≤ x := by
      obtain ⟨z,rfl⟩ := hint
      have hz : (2 : ℤ) ≤ z := by exact_mod_cast hx
      have hz2 : z ≠ 2 := by exact_mod_cast h2
      have hz3 : z ≠ 3 := by exact_mod_cast h3
      have hz4 : z ≠ 4 := by exact_mod_cast h4
      exact_mod_cast (show (5 : ℤ) ≤ z by omega)
    have hc2 := Multiset.count_cons_of_ne (Ne.symm h2) s
    have hc3 := Multiset.count_cons_of_ne (Ne.symm h3) s
    have hc4 := Multiset.count_cons_of_ne (Ne.symm h4) s
    simp only [Paper7Admissible.squareSum,Multiset.map_cons,Multiset.sum_cons,
      Multiset.card_cons,Nat.cast_add,Nat.cast_one,hc2,hc3,hc4] at ht ⊢
    nlinarith
#print axioms Paper7EightCycle.square_floor_twenty_five

end Paper7EightCycle
