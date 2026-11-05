import Mathlib

/-! Generic integer-multiset counting. A maximum is an explicit
hypothesis; the cardinality estimates do not need its simplicity.
This file does not assert Perron--Frobenius or the full Lemma24. -/
set_option autoImplicit false
noncomputable section
namespace Paper7Admissible

def squareSum (s : Multiset ℝ) : ℝ := (s.map (fun x => x ^ 2)).sum

theorem integer_at_least_three {x : ℝ} (hx : ∃ z : ℤ, x = z)
    (hx2 : 2 ≤ x) (hne : x ≠ 2) : 3 ≤ x := by
  obtain ⟨z, rfl⟩ := hx
  have hz2 : (2 : ℤ) ≤ z := by exact_mod_cast hx2
  have hzne : z ≠ 2 := by exact_mod_cast hne
  have hz3 : (3 : ℤ) ≤ z := by omega
  exact_mod_cast hz3

theorem integer_between_two_four {x : ℝ} (hx : ∃ z : ℤ, x = z)
    (hx2 : 2 ≤ x) (hx4 : x < 4) : x = 2 ∨ x = 3 := by
  obtain ⟨z, rfl⟩ := hx
  have hz2 : (2 : ℤ) ≤ z := by exact_mod_cast hx2
  have hz4 : z < (4 : ℤ) := by exact_mod_cast hx4
  have hz : z = 2 ∨ z = 3 := by omega
  rcases hz with rfl | rfl <;> norm_num

theorem card_of_two_three (s : Multiset ℝ) (h : ∀ x ∈ s, x = 2 ∨ x = 3) :
    s.card = s.count 2 + s.count 3 := by
  classical
  revert h
  induction s using Multiset.induction_on with
  | empty => intro _; simp
  | @cons x s ih =>
    intro h
    have hi := ih (fun y hy => h y (Multiset.mem_cons_of_mem hy))
    rcases h x (Multiset.mem_cons_self x s) with rfl | rfl <;> simp [hi] <;> omega

theorem square_floor_sum (s : Multiset ℝ)
    (h : ∀ x ∈ s, 2 ≤ x ∧ ∃ z : ℤ, x = z) :
    9 * (s.card : ℝ) ≤ squareSum s + 5 * (s.count 2 : ℝ) := by
  classical
  revert h
  induction s using Multiset.induction_on with
  | empty => intro _; simp [squareSum]
  | @cons x s ih =>
    intro h
    have hi := ih (fun y hy => h y (Multiset.mem_cons_of_mem hy))
    obtain ⟨hx2, hint⟩ := h x (Multiset.mem_cons_self x s)
    by_cases hx : x = 2
    · subst x
      have hsum : squareSum ((2 : ℝ) ::ₘ s) = 4 + squareSum s := by norm_num [squareSum]
      simp only [hsum, Multiset.card_cons, Multiset.count_cons_self, Nat.cast_add, Nat.cast_one]
      linarith
    · have hx3 := integer_at_least_three hint hx2 hx
      have hcount : (x ::ₘ s).count 2 = s.count 2 :=
        Multiset.count_cons_of_ne (Ne.symm hx) s
      simp only [squareSum, Multiset.map_cons, Multiset.sum_cons] at hi ⊢
      rw [hcount, Multiset.card_cons, Nat.cast_add, Nat.cast_one]
      nlinarith

theorem square_floor_equality (s : Multiset ℝ)
    (h : ∀ x ∈ s, 2 ≤ x ∧ ∃ z : ℤ, x = z)
    (heq : squareSum s + 5 * (s.count 2 : ℝ) = 9 * (s.card : ℝ)) :
    ∀ x ∈ s, x = 2 ∨ x = 3 := by
  classical
  revert h heq
  induction s using Multiset.induction_on with
  | empty => simp
  | @cons x s ih =>
    intro h heq
    have hs := fun y hy => h y (Multiset.mem_cons_of_mem hy)
    have hfloor := square_floor_sum s hs
    obtain ⟨hx2, hint⟩ := h x (Multiset.mem_cons_self x s)
    have hcard : ((x ::ₘ s).card : ℝ) = (s.card : ℝ) + 1 := by simp
    have hsum : squareSum (x ::ₘ s) = x ^ 2 + squareSum s := by simp [squareSum]
    by_cases hx : x = 2
    · have hcount : ((x ::ₘ s).count 2 : ℝ) = (s.count 2 : ℝ) + 1 := by simp [hx]
      have htail : squareSum s + 5 * (s.count 2 : ℝ) = 9 * (s.card : ℝ) := by
        rw [hcard, hsum, hcount, hx] at heq
        nlinarith
      intro y hy
      rcases Multiset.mem_cons.mp hy with rfl | hy
      · exact Or.inl hx
      · exact ih hs htail y hy
    · have hx3 := integer_at_least_three hint hx2 hx
      have hcount : (x ::ₘ s).count 2 = s.count 2 :=
        Multiset.count_cons_of_ne (Ne.symm hx) s
      rw [hcard, hsum, hcount] at heq
      have hx3eq : x = 3 := by nlinarith
      have htail : squareSum s + 5 * (s.count 2 : ℝ) = 9 * (s.card : ℝ) := by
        rw [hx3eq] at heq
        nlinarith
      intro y hy
      rcases Multiset.mem_cons.mp hy with rfl | hy
      · exact Or.inr hx3eq
      · exact ih hs htail y hy

theorem five_forces_max_four (s : Multiset ℝ) (ρ : ℝ)
    (hs : ∀ x ∈ s, 2 ≤ x ∧ ∃ z : ℤ, x = z)
    (_hρ : ρ ∈ s) (hmax : ∀ x ∈ s, x ≤ ρ)
    (hc : ∀ x : ℝ, s.count x ≤ 2) (hfive : 5 ≤ s.card) : 4 ≤ ρ := by
  by_contra hn
  have hρ4 : ρ < 4 := lt_of_not_ge hn
  have h23 : ∀ x ∈ s, x = 2 ∨ x = 3 := by
    intro x hx
    exact integer_between_two_four (hs x hx).2 (hs x hx).1
      ((hmax x hx).trans_lt hρ4)
  have hcard := card_of_two_three s h23
  have h2 := hc 2
  have h3 := hc 3
  omega

theorem five_square_lower (s : Multiset ℝ) (ρ : ℝ)
    (hs : ∀ x ∈ s, 2 ≤ x ∧ ∃ z : ℤ, x = z)
    (hρ : ρ ∈ s) (hmax : ∀ x ∈ s, x ≤ ρ)
    (hc : ∀ x : ℝ, s.count x ≤ 2) (hfive : 5 ≤ s.card) :
    9 * (s.card : ℝ) - 3 ≤ squareSum s := by
  classical
  have hρ4 := five_forces_max_four s ρ hs hρ hmax hc hfive
  have hρ2 : (2 : ℝ) ≠ ρ := by linarith
  have ht := square_floor_sum (s.erase ρ) (fun x hx => hs x (Multiset.mem_of_mem_erase hx))
  have hc2 : ((s.erase ρ).count 2 : ℝ) ≤ 2 := by
    rw [Multiset.count_erase_of_ne hρ2]
    exact_mod_cast hc 2
  have hcard : ((s.erase ρ).card : ℝ) + 1 = (s.card : ℝ) := by
    exact_mod_cast Multiset.card_erase_add_one hρ
  have hsum : ρ ^ 2 + squareSum (s.erase ρ) = squareSum s := by
    simpa only [squareSum, Multiset.map_cons, Multiset.sum_cons] using
      congrArg squareSum (Multiset.cons_erase hρ)
  nlinarith

theorem admissible_five_bound (s : Multiset ℝ) (ρ : ℝ)
    (hs : ∀ x ∈ s, 2 ≤ x ∧ ∃ z : ℤ, x = z)
    (hρ : ρ ∈ s) (hmax : ∀ x ∈ s, x ≤ ρ)
    (hc : ∀ x : ℝ, s.count x ≤ 2)
    (h42 : squareSum s ≤ 42) :
    s.card ≤ 5 ∧ (s.card = 5 → s = {4, 3, 3, 2, 2}) := by
  classical
  have hcard : s.card ≤ 5 := by
    by_contra hn
    have h5 : 5 ≤ s.card := by omega
    have hl := five_square_lower s ρ hs hρ hmax hc h5
    have hc6 : (6 : ℝ) ≤ s.card := by exact_mod_cast (show 6 ≤ s.card by omega)
    linarith
  refine ⟨hcard, ?_⟩
  intro hfive
  have hρ4 := five_forces_max_four s ρ hs hρ hmax hc (by omega)
  have hρ2 : (2 : ℝ) ≠ ρ := by linarith
  have ht := square_floor_sum (s.erase ρ) (fun x hx => hs x (Multiset.mem_of_mem_erase hx))
  have hc2 : ((s.erase ρ).count 2 : ℝ) ≤ 2 := by
    rw [Multiset.count_erase_of_ne hρ2]
    exact_mod_cast hc 2
  have hcardt : (s.erase ρ).card = 4 := by
    have := Multiset.card_erase_add_one hρ
    omega
  have hsum : ρ ^ 2 + squareSum (s.erase ρ) = squareSum s := by
    simpa only [squareSum, Multiset.map_cons, Multiset.sum_cons] using
      congrArg squareSum (Multiset.cons_erase hρ)
  rw [hcardt] at ht
  norm_num at ht
  have hρeq : ρ = 4 := by nlinarith
  have hc2eq : (s.erase ρ).count 2 = 2 := by
    have h : ((s.erase ρ).count 2 : ℝ) = 2 := by nlinarith
    exact_mod_cast h
  have htailEq : squareSum (s.erase ρ) + 5 * ((s.erase ρ).count 2 : ℝ) =
      9 * ((s.erase ρ).card : ℝ) := by
    rw [hcardt]
    norm_num
    nlinarith
  have hall := square_floor_equality (s.erase ρ)
    (fun x hx => hs x (Multiset.mem_of_mem_erase hx)) htailEq
  have hcard23 := card_of_two_three (s.erase ρ) hall
  have hc3eq : (s.erase ρ).count 3 = 2 := by omega
  have htail : s.erase ρ = ({3, 3, 2, 2} : Multiset ℝ) := by
    apply Multiset.ext.mpr
    intro x
    by_cases hx2 : x = 2
    · subst x; simp [hc2eq]
    · by_cases hx3 : x = 3
      · subst x; simp [hc3eq]
      · have hxnot : x ∉ s.erase ρ := by
          intro hx
          exact (hall x hx).elim hx2 hx3
        simp [Multiset.count_eq_zero_of_notMem hxnot, hx2, hx3]
  rw [← Multiset.cons_erase hρ, htail, hρeq]
  rfl

theorem admissible_four_bound (s : Multiset ℝ) (ρ : ℝ)
    (hs : ∀ x ∈ s, 2 ≤ x ∧ ∃ z : ℤ, x = z)
    (hρ : ρ ∈ s) (hmax : ∀ x ∈ s, x ≤ ρ)
    (hc : ∀ x : ℝ, s.count x ≤ 2) (h41 : squareSum s ≤ 41) : s.card ≤ 4 := by
  by_contra hn
  have hl := five_square_lower s ρ hs hρ hmax hc (by omega)
  have hc5 : (5 : ℝ) ≤ s.card := by exact_mod_cast (show 5 ≤ s.card by omega)
  linarith

end Paper7Admissible
#print axioms Paper7Admissible.squareSum
#print axioms Paper7Admissible.integer_at_least_three
#print axioms Paper7Admissible.integer_between_two_four
#print axioms Paper7Admissible.card_of_two_three
#print axioms Paper7Admissible.square_floor_sum
#print axioms Paper7Admissible.square_floor_equality
#print axioms Paper7Admissible.five_forces_max_four
#print axioms Paper7Admissible.five_square_lower
#print axioms Paper7Admissible.admissible_five_bound
#print axioms Paper7Admissible.admissible_four_bound
