import Research.Backfill.Paper7.IntegralMomentFilters

set_option autoImplicit false
noncomputable section
namespace Paper7Admissible
open BackfillPaper7.Challenge

theorem square_partition (s : Multiset ℝ)
    (hint : ∀ x ∈ s, ¬ 2 ≤ |x| → x = -1 ∨ x = 0 ∨ x = 1) :
    (s.map (fun x => x ^ 2)).sum =
      ((s.filter (fun x => 2 ≤ |x|)).map (fun x => x ^ 2)).sum +
        (s.count 1 : ℝ) + (s.count (-1) : ℝ) := by
  classical
  revert hint
  induction s using Multiset.induction_on with
  | empty => intro _; simp
  | @cons x s ih =>
    intro hint
    have hi := ih (fun y hy => hint y (Multiset.mem_cons_of_mem hy))
    by_cases hx : 2 ≤ |x|
    · have hx1 : x ≠ 1 := by intro h; subst x; norm_num at hx
      have hxn : x ≠ -1 := by intro h; subst x; norm_num at hx
      simp [hx, Ne.symm hx1, Ne.symm hxn, hi]
      ring
    · rcases hint x (Multiset.mem_cons_self x s) hx with rfl | rfl | rfl <;>
        norm_num [Multiset.count_cons, hi] <;> ring

theorem large_square_split (s : Multiset ℝ) :
    ((s.filter (fun x => 2 ≤ |x|)).map (fun x => x ^ 2)).sum =
      ((s.filter (fun x => 2 ≤ x)).map (fun x => x ^ 2)).sum +
      (((s.map (fun x => -x)).filter (fun x => 2 ≤ x)).map (fun x => x ^ 2)).sum := by
  classical
  induction s using Multiset.induction_on with
  | empty => simp
  | @cons x s ih =>
    by_cases hx : 2 ≤ x
    · have hnx : ¬ 2 ≤ -x := by linarith
      have ha : 2 ≤ |x| := by rw [abs_of_nonneg (by linarith : 0 ≤ x)]; exact hx
      simp [hx, hnx, ha, ih]
      ring
    · by_cases hnx : 2 ≤ -x
      · have ha : 2 ≤ |x| := by rw [abs_of_nonpos (by linarith : x ≤ 0)]; exact hnx
        simp [hx, hnx, ha, ih]
        ring
      · have ha : ¬ 2 ≤ |x| := by
          apply not_le.mpr
          exact abs_lt.mpr ⟨by linarith, by linarith⟩
        simp [hx, hnx, ha, ih]

theorem map_neg_eq_of_count (s : Multiset ℝ)
    (hs : ∀ x : ℝ, s.count x = s.count (-x)) : s.map (fun x => -x) = s := by
  classical
  apply Multiset.ext.mpr
  intro x
  have h := Multiset.count_map_eq_count' (fun y : ℝ => -y) s neg_injective (-x)
  simpa only [neg_neg] using h.trans (hs (-x))

theorem graph_square_partition {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : IsIntegralGraph G) :
    ((spec G).map (fun x => x ^ 2)).sum =
      ((bigEigs G).map (fun x => x ^ 2)).sum + (mult G 1 : ℝ) + (mult G (-1) : ℝ) :=
  square_partition (spec G) (Paper7Moments.small_integral_spec_entry G hG)

theorem symmetric_large_square {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hs : ∀ x : ℝ, mult G x = mult G (-x)) :
    ((bigEigs G).map (fun x => x ^ 2)).sum = 2 * S2 G := by
  have hm : (spec G).map (fun x => -x) = spec G := map_neg_eq_of_count _ hs
  change (((spec G).filter (fun x => 2 ≤ |x|)).map (fun x => x ^ 2)).sum = _
  rw [large_square_split, hm]
  unfold S2 Bplus
  ring

end Paper7Admissible
#print axioms Paper7Admissible.square_partition
#print axioms Paper7Admissible.large_square_split
#print axioms Paper7Admissible.map_neg_eq_of_count
#print axioms Paper7Admissible.graph_square_partition
#print axioms Paper7Admissible.symmetric_large_square
