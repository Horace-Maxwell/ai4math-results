import Research.Backfill.Paper7.Lemma24Counting
import Research.Backfill.Paper7.AdmissibleMultisetCounts

/-! Full branch (d) from the original graph assumptions. The proof uses a
finite multiset maximum, not an assumed Perron eigenvalue. -/
set_option autoImplicit false
noncomputable section
namespace Paper7Admissible
open BackfillPaper7.Challenge

theorem bplus_integral_entries (b : ℕ) (p q : Fin b → ℕ)
    (hG : IsIntegralGraph (SG b p q)) :
    ∀ x ∈ Bplus (SG b p q), 2 ≤ x ∧ ∃ z : ℤ, x = z := by
  intro x hx
  have h := Multiset.mem_filter.mp hx
  exact ⟨h.2, Paper7Moments.integral_spec_entry (SG b p q) hG x h.1⟩

theorem bplus_count_le_two (b : ℕ) (p q : Fin b → ℕ) (hb : 3 ≤ b) (x : ℝ) :
    (Bplus (SG b p q)).count x ≤ 2 := by
  classical
  by_cases hx : 2 ≤ x
  · have hxn : x ≠ -1 := by linarith
    have hx0 : x ≠ 0 := by linarith
    have hx1 : x ≠ 1 := by linarith
    have hm := ((Paper7Lemma22.check_Lemma22 b p q hb).1 x hxn hx0 hx1).2.1
    simpa only [Bplus, mult, Multiset.count_filter, hx, ite_true] using hm
  · simp only [Bplus, Multiset.count_filter, hx, ite_false, Nat.zero_le]

theorem lemma24_small_even_counts (b : ℕ) (p q : Fin b → ℕ) (hb : 3 ≤ b)
    (hG : IsIntegralGraph (SG b p q)) (he : Even b) :
    (nOf b p q ≤ 41 → Multiset.card (Bplus (SG b p q)) ≤ 4) ∧
    (nOf b p q ≤ 42 → Multiset.card (Bplus (SG b p q)) ≤ 5 ∧
      (Multiset.card (Bplus (SG b p q)) = 5 → Bplus (SG b p q) = {4, 3, 3, 2, 2})) := by
  classical
  let s := Bplus (SG b p q)
  have hsum : squareSum s ≤ (nOf b p q : ℝ) := by
    have heq := (lemma24_counting_even b p q hb hG he).2.1
    have hm : (0 : ℝ) ≤ mult (SG b p q) 1 := Nat.cast_nonneg _
    change S2 (SG b p q) ≤ (nOf b p q : ℝ)
    linarith
  by_cases hs0 : s = 0
  · constructor
    · intro _; change s.card ≤ 4; simp [hs0]
    · intro _; change s.card ≤ 5 ∧ (s.card = 5 → s = {4, 3, 3, 2, 2}); simp [hs0]
  · obtain ⟨ρ, hρ, hmax⟩ := Multiset.exists_max_image (fun x : ℝ => x) hs0
    have hs := bplus_integral_entries b p q hG
    have hc := bplus_count_le_two b p q hb
    constructor
    · intro hn
      have hnR : (nOf b p q : ℝ) ≤ 41 := by exact_mod_cast hn
      exact admissible_four_bound s ρ hs hρ hmax hc (hsum.trans hnR)
    · intro hn
      have hnR : (nOf b p q : ℝ) ≤ 42 := by exact_mod_cast hn
      exact admissible_five_bound s ρ hs hρ hmax hc (hsum.trans hnR)

end Paper7Admissible
#print axioms Paper7Admissible.bplus_integral_entries
#print axioms Paper7Admissible.bplus_count_le_two
#print axioms Paper7Admissible.lemma24_small_even_counts
