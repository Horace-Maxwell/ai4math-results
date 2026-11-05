import Research.Backfill.Paper7.Lemma22
import Research.Backfill.Paper7.Identities12

set_option autoImplicit false

noncomputable section

namespace Paper7Admissible

open BackfillPaper7.Challenge

/-- The original all-real large-root multiplicity bound; no integrality is needed. -/
theorem lemma24_large_multiplicity (b : ℕ) (p q : Fin b → ℕ) (hb : 3 ≤ b)
    (x : ℝ) (hx : 2 ≤ |x|) : mult (SG b p q) x ≤ 2 := by
  have hn : x ≠ -1 := by intro h; subst x; norm_num at hx
  have hz : x ≠ 0 := by intro h; subst x; norm_num at hx
  have hp : x ≠ 1 := by intro h; subst x; norm_num at hx
  exact ((Paper7Lemma22.check_Lemma22 b p q hb).1 x hn hz hp).2.1
#print axioms Paper7Admissible.lemma24_large_multiplicity

theorem lemma24_unit_multiplicity_bounds (b : ℕ) (p q : Fin b → ℕ) (hb : 3 ≤ b) :
    mult (SG b p q) 1 ≤ max (∑ k, q k) 2 ∧
      mult (SG b p q) (-1) ≤ max (∑ k, q k) 2 :=
  (Paper7Lemma22.check_Lemma22 b p q hb).2.2.2.2
#print axioms Paper7Admissible.lemma24_unit_multiplicity_bounds

theorem square_le_sum_squares (s : Multiset ℝ) (x : ℝ) (hx : x ∈ s) :
    x ^ 2 ≤ (s.map (fun y => y ^ 2)).sum := by
  classical
  obtain ⟨t, rfl⟩ := Multiset.exists_cons_of_mem hx
  simp only [Multiset.map_cons, Multiset.sum_cons]
  exact le_add_of_nonneg_right (Multiset.sum_nonneg (by
    intro y hy
    obtain ⟨z, hz, rfl⟩ := Multiset.mem_map.mp hy
    exact sq_nonneg z))
#print axioms Paper7Admissible.square_le_sum_squares

/-- Every real characteristic root, not only a finite searched interval. -/
theorem lemma24_square_bound (b : ℕ) (p q : Fin b → ℕ) (hb : 3 ≤ b)
    (x : ℝ) (hx : x ∈ spec (SG b p q)) : x ^ 2 ≤ 2 * (nOf b p q : ℝ) := by
  have h := square_le_sum_squares (spec (SG b p q)) x hx
  rwa [Paper7SunMoments.sg_second_moment b p q hb] at h
#print axioms Paper7Admissible.lemma24_square_bound

end Paper7Admissible
