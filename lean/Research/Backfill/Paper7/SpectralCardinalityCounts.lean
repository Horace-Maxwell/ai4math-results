import Research.Backfill.Paper7.IntegralSquareCounts
import Research.Backfill.Paper7.SpectrumGraphBasics

/-! Exact cardinality decomposition, retaining every eigenvalue multiplicity. -/
set_option autoImplicit false
noncomputable section

namespace Paper7Counting
open BackfillPaper7.Challenge

/-- The complement of the large spectrum consists precisely of -1, 0, 1. -/
theorem integral_card_partition (s : Multiset ℝ)
    (hint : ∀ x ∈ s, ¬ 2 ≤ |x| → x = -1 ∨ x = 0 ∨ x = 1) :
    s.card = (s.filter (fun x => 2 ≤ |x|)).card +
      s.count 1 + s.count (-1) + s.count 0 := by
  classical
  revert hint
  induction s using Multiset.induction_on with
  | empty => intro _; simp
  | @cons x s ih =>
    intro hint
    have hi := ih (fun y hy => hint y (Multiset.mem_cons_of_mem hy))
    by_cases hx : 2 ≤ |x|
    · have h1 : (1 : ℝ) ≠ x := by intro h; rw [← h] at hx; norm_num at hx
      have hn : (-1 : ℝ) ≠ x := by intro h; rw [← h] at hx; norm_num at hx
      have h0 : (0 : ℝ) ≠ x := by intro h; rw [← h] at hx; norm_num at hx
      simp only [Multiset.card_cons, Multiset.filter_cons_of_pos (p := fun y : ℝ => 2 ≤ |y|) s hx,
        Multiset.count_cons_of_ne h1, Multiset.count_cons_of_ne hn,
        Multiset.count_cons_of_ne h0]
      omega
    · rcases hint x (Multiset.mem_cons_self x s) hx with rfl | rfl | rfl
      · simp only [Multiset.card_cons,
          Multiset.filter_cons_of_neg (p := fun y : ℝ => 2 ≤ |y|) s (by norm_num : ¬ 2 ≤ |(-1 : ℝ)|),
          Multiset.count_cons_self,
          Multiset.count_cons_of_ne (by norm_num : (1 : ℝ) ≠ -1),
          Multiset.count_cons_of_ne (by norm_num : (0 : ℝ) ≠ -1)]
        omega
      · simp only [Multiset.card_cons,
          Multiset.filter_cons_of_neg (p := fun y : ℝ => 2 ≤ |y|) s (by norm_num : ¬ 2 ≤ |(0 : ℝ)|),
          Multiset.count_cons_self,
          Multiset.count_cons_of_ne (by norm_num : (1 : ℝ) ≠ 0),
          Multiset.count_cons_of_ne (by norm_num : (-1 : ℝ) ≠ 0)]
        omega
      · simp only [Multiset.card_cons,
          Multiset.filter_cons_of_neg (p := fun y : ℝ => 2 ≤ |y|) s (by norm_num : ¬ 2 ≤ |(1 : ℝ)|),
          Multiset.count_cons_self,
          Multiset.count_cons_of_ne (by norm_num : (-1 : ℝ) ≠ 1),
          Multiset.count_cons_of_ne (by norm_num : (0 : ℝ) ≠ 1)]
        omega
#print axioms Paper7Counting.integral_card_partition

/-- The two disjoint large-spectrum halves are related by negation. -/
theorem large_card_split (s : Multiset ℝ) :
    (s.filter (fun x => 2 ≤ |x|)).card =
      (s.filter (fun x => 2 ≤ x)).card +
      ((s.map (fun x => -x)).filter (fun x => 2 ≤ x)).card := by
  classical
  induction s using Multiset.induction_on with
  | empty => simp
  | @cons x s ih =>
    by_cases hx : 2 ≤ x
    · have hnx : ¬ 2 ≤ -x := by linarith
      have ha : 2 ≤ |x| := by rw [abs_of_nonneg (by linarith : 0 ≤ x)]; exact hx
      rw [Multiset.filter_cons_of_pos (p := fun y : ℝ => 2 ≤ |y|) s ha, Multiset.card_cons,
        Multiset.filter_cons_of_pos (p := fun y : ℝ => 2 ≤ y) s hx, Multiset.card_cons,
        Multiset.map_cons, Multiset.filter_cons_of_neg (p := fun y : ℝ => 2 ≤ y) _ hnx]
      omega
    · by_cases hnx : 2 ≤ -x
      · have ha : 2 ≤ |x| := by
          rw [abs_of_nonpos (by linarith : x ≤ 0)]
          exact hnx
        rw [Multiset.filter_cons_of_pos (p := fun y : ℝ => 2 ≤ |y|) s ha, Multiset.card_cons,
          Multiset.filter_cons_of_neg (p := fun y : ℝ => 2 ≤ y) s hx, Multiset.map_cons,
          Multiset.filter_cons_of_pos (p := fun y : ℝ => 2 ≤ y) _ hnx, Multiset.card_cons]
        omega
      · have ha : ¬ 2 ≤ |x| := by
          apply not_le.mpr
          exact abs_lt.mpr ⟨by linarith, by linarith⟩
        rw [Multiset.filter_cons_of_neg (p := fun y : ℝ => 2 ≤ |y|) s ha, Multiset.filter_cons_of_neg (p := fun y : ℝ => 2 ≤ y) s hx,
          Multiset.map_cons, Multiset.filter_cons_of_neg (p := fun y : ℝ => 2 ≤ y) _ hnx]
        exact ih
#print axioms Paper7Counting.large_card_split

theorem symmetric_big_card {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hs : ∀ x : ℝ, mult G x = mult G (-x)) :
    (bigEigs G).card = 2 * (Bplus G).card := by
  have hm : (spec G).map (fun x => -x) = spec G :=
    Paper7Admissible.map_neg_eq_of_count _ hs
  change ((spec G).filter (fun x => 2 ≤ |x|)).card = _
  rw [large_card_split, hm]
  change (Bplus G).card + (Bplus G).card = 2 * (Bplus G).card
  omega
#print axioms Paper7Counting.symmetric_big_card

/-- A cardinality identity for the entire real spectrum, including zeros. -/
theorem symmetric_spectrum_card {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : IsIntegralGraph G)
    (hs : ∀ x : ℝ, mult G x = mult G (-x)) :
    Fintype.card V = 2 * (Bplus G).card + mult G 1 + mult G (-1) + mult G 0 := by
  calc
    Fintype.card V = (spec G).card := (Paper7Spectrum.spec_card G).symm
    _ = (bigEigs G).card + mult G 1 + mult G (-1) + mult G 0 :=
      integral_card_partition (spec G) (Paper7Moments.small_integral_spec_entry G hG)
    _ = 2 * (Bplus G).card + mult G 1 + mult G (-1) + mult G 0 := by
      rw [symmetric_big_card G hs]
#print axioms Paper7Counting.symmetric_spectrum_card

end Paper7Counting
