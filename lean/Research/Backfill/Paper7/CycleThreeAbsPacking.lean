import Research.Backfill.Paper7.CycleThreeSpectralObstruction
import Research.Backfill.Paper7.IntegralAbsPacking

/-! New source candidates. Stage01's opposite-spectrum obstruction is pending;
the imported integral multiplicity and square-budget bridges are actual prior PASS. -/
set_option autoImplicit false
noncomputable section
namespace Paper7CycleThree
open BackfillPaper7.Challenge Paper7Rank
open scoped Classical

theorem square_sum_small_value_correction (s : Multiset ℕ)
    (hmin : ∀ a ∈ s, 2 ≤ a) :
    25 * s.card ≤ (s.map (fun a => a ^ 2)).sum +
      21 * s.count 2 + 16 * s.count 3 + 9 * s.count 4 := by
  revert hmin
  induction s using Multiset.induction_on with
  | empty => intro _; simp
  | @cons a s ih =>
    intro hmin
    have ha := hmin a (Multiset.mem_cons_self a s)
    have hs := ih (fun z hz => hmin z (Multiset.mem_cons_of_mem hz))
    by_cases h2 : a = 2
    · subst a
      norm_num only [Multiset.card_cons, Multiset.map_cons, Multiset.sum_cons,
        Multiset.count_cons]
      simp only [ite_true, ite_false]
      omega
    · by_cases h3 : a = 3
      · subst a
        norm_num only [Multiset.card_cons, Multiset.map_cons, Multiset.sum_cons,
          Multiset.count_cons]
        simp only [ite_true, ite_false]
        omega
      · by_cases h4 : a = 4
        · subst a
          norm_num only [Multiset.card_cons, Multiset.map_cons, Multiset.sum_cons,
            Multiset.count_cons]
          simp only [ite_true, ite_false]
          omega
        · have ha5 : 5 ≤ a := by omega
          have hsq : 25 ≤ a ^ 2 := by nlinarith
          simp only [Multiset.card_cons, Multiset.map_cons, Multiset.sum_cons,
            Multiset.count_cons_of_ne (Ne.symm h2),
            Multiset.count_cons_of_ne (Ne.symm h3),
            Multiset.count_cons_of_ne (Ne.symm h4)]
          omega
#print axioms Paper7CycleThree.square_sum_small_value_correction

theorem square_sum_count_two_budget (s : Multiset ℕ)
    (hmin : ∀ a ∈ s, 2 ≤ a) (hcount : ∀ a, s.count a ≤ 2) :
    25 * s.card ≤ (s.map (fun a => a ^ 2)).sum + 92 := by
  have h := square_sum_small_value_correction s hmin
  have h2 := hcount 2
  have h3 := hcount 3
  have h4 := hcount 4
  omega
#print axioms Paper7CycleThree.square_sum_count_two_budget

theorem triangle_large_absNat_count_le_two (p q : Fin 3 → ℕ)
    (hG : IsIntegralGraph (SG 3 p q)) (n : ℕ) :
    ((bigEigs (SG 3 p q)).map absNat).count n ≤ 2 := by
  classical
  let s := bigEigs (SG 3 p q)
  have hint : ∀ x ∈ s, ∃ z : ℤ, x = (z : ℝ) := by
    intro x hx
    exact Paper7Moments.integral_spec_entry _ hG x (Multiset.mem_filter.mp hx).1
  by_cases hn : 2 ≤ n
  · have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
    have hp := ((Paper7Lemma22.check_Lemma22 3 p q (by omega)).1 (n : ℝ)
      (by linarith) (by linarith) (by linarith)).2.1
    have hm := ((Paper7Lemma22.check_Lemma22 3 p q (by omega)).1 (-(n : ℝ))
      (by linarith) (by linarith) (by linarith)).2.1
    have hc := count_absNat s hint n (by omega)
    have h1 : s.count (n : ℝ) = mult (SG 3 p q) (n : ℝ) := by
      exact Multiset.count_filter_of_pos
        (by simpa only [abs_of_nonneg (by linarith : (0 : ℝ) ≤ n)] using hnR)
    have h2 : s.count (-(n : ℝ)) = mult (SG 3 p q) (-(n : ℝ)) := by
      exact Multiset.count_filter_of_pos
        (by simpa only [abs_neg, abs_of_nonneg (by linarith : (0 : ℝ) ≤ n)] using hnR)
    have hpair := triangle_no_opposite_spectrum p q (n : ℝ)
      (by linarith) (by nlinarith)
    change (s.map absNat).count n ≤ 2
    by_cases hmem : (n : ℝ) ∈ spec (SG 3 p q)
    · have hnot : -(n : ℝ) ∉ s := by
        intro hneg
        exact hpair ⟨hmem, (Multiset.mem_filter.mp hneg).1⟩
      have hz := Multiset.count_eq_zero_of_notMem hnot
      omega
    · have hnot : (n : ℝ) ∉ s := fun h => hmem (Multiset.mem_filter.mp h).1
      have hz := Multiset.count_eq_zero_of_notMem hnot
      omega
  · have hnot : n ∉ s.map absNat := by
      intro hmem
      obtain ⟨x, hx, hxn⟩ := Multiset.mem_map.mp hmem
      have hc := cast_absNat x (hint x hx)
      have hx2 := (Multiset.mem_filter.mp hx).2
      have hnR : (n : ℝ) < 2 := by exact_mod_cast (by omega : n < 2)
      rw [hxn] at hc
      linarith
    change (s.map absNat).count n ≤ 2
    rw [Multiset.count_eq_zero_of_notMem hnot]
    omega
#print axioms Paper7CycleThree.triangle_large_absNat_count_le_two

theorem triangle_square_budget (p q : Fin 3 → ℕ)
    (hG : IsIntegralGraph (SG 3 p q)) :
    25 * ((bigEigs (SG 3 p q)).card : ℤ) + mult (SG 3 p q) 1 +
      mult (SG 3 p q) (-1) ≤ 2 * (nOf 3 p q : ℤ) + 92 := by
  classical
  let s := bigEigs (SG 3 p q)
  have hint : ∀ x ∈ s, ∃ z : ℤ, x = (z : ℝ) := by
    intro x hx
    exact Paper7Moments.integral_spec_entry _ hG x (Multiset.mem_filter.mp hx).1
  have hmin : ∀ a ∈ s.map absNat, 2 ≤ a := by
    intro a ha
    obtain ⟨x, hx, rfl⟩ := Multiset.mem_map.mp ha
    have hc := cast_absNat x (hint x hx)
    have hm := (Multiset.mem_filter.mp hx).2
    have hr : (2 : ℝ) ≤ absNat x := by linarith
    exact_mod_cast hr
  have hpack := square_sum_count_two_budget (s.map absNat) hmin
    (triangle_large_absNat_count_le_two p q hG)
  rw [Multiset.card_map] at hpack
  have hpackR : 25 * (s.card : ℝ) ≤
      (((s.map absNat).map (fun a : ℕ => a ^ 2)).sum : ℝ) + 92 := by
    exact_mod_cast hpack
  rw [absNat_square_sum s hint] at hpackR
  have hbudget := Paper7Admissible.graph_square_partition (SG 3 p q) hG
  rw [Paper7SunMoments.sg_second_moment 3 p q (by omega)] at hbudget
  have hR : 25 * (s.card : ℝ) + (mult (SG 3 p q) 1 : ℝ) +
      (mult (SG 3 p q) (-1) : ℝ) ≤ 2 * (nOf 3 p q : ℝ) + 92 := by
    change 2 * (nOf 3 p q : ℝ) = (s.map (fun x => x ^ 2)).sum +
      (mult (SG 3 p q) 1 : ℝ) + (mult (SG 3 p q) (-1) : ℝ) at hbudget
    linarith
  exact_mod_cast hR
#print axioms Paper7CycleThree.triangle_square_budget

theorem triangle_large_card_le_seven (p q : Fin 3 → ℕ)
    (hG : IsIntegralGraph (SG 3 p q)) (hn : nOf 3 p q ≤ 49) :
    (bigEigs (SG 3 p q)).card ≤ 7 := by
  have h := triangle_square_budget p q hG
  omega
#print axioms Paper7CycleThree.triangle_large_card_le_seven

end Paper7CycleThree
