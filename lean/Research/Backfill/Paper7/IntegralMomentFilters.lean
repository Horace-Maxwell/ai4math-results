import Research.Backfill.Paper7.SpectralMoments

/-! The exact large-eigenvalue filter drops only integer eigenvalues -1,0,1.
These algebraic bridges retain all multiset multiplicities and all odd exponents.
They are helpers, not completed Lemma23 or Identities12 contracts. -/

set_option autoImplicit false

noncomputable section

open BackfillPaper7.Challenge

namespace Paper7Moments

theorem sum_filter_large_eq (s : Multiset ℝ) (F : ℝ → ℝ)
    (hF : ∀ x ∈ s, ¬ 2 ≤ |x| → F x = 0) :
    ((s.filter (fun x => 2 ≤ |x|)).map F).sum = (s.map F).sum := by
  classical
  revert hF
  induction s using Multiset.induction_on with
  | empty => intro _; simp
  | @cons x s ih =>
    intro hF
    have hs : ∀ y ∈ s, ¬ 2 ≤ |y| → F y = 0 :=
      fun y hy => hF y (Multiset.mem_cons_of_mem hy)
    have hx := hF x (Multiset.mem_cons_self x s)
    by_cases hlarge : 2 ≤ |x|
    · simp [hlarge, ih hs]
    · simp [hlarge, hx hlarge, ih hs]

theorem small_integral_spec_entry {V : Type} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] (hH : IsIntegralGraph H)
    (x : ℝ) (hx : x ∈ spec H) (hsmall : ¬ 2 ≤ |x|) :
    x = -1 ∨ x = 0 ∨ x = 1 := by
  obtain ⟨z, hz⟩ := integral_spec_entry H hH x hx
  have hbounds : -(2 : ℝ) < (z : ℝ) ∧ (z : ℝ) < 2 := by
    rw [← hz]
    exact abs_lt.mp (lt_of_not_ge hsmall)
  have hboundsZ : -(2 : ℤ) < z ∧ z < 2 := by exact_mod_cast hbounds
  have hzvalues : z = -1 ∨ z = 0 ∨ z = 1 := by omega
  rcases hzvalues with hzv | hzv | hzv
  · left; simpa only [hzv, Int.cast_neg, Int.cast_one] using hz
  · right; left; simpa only [hzv, Int.cast_zero] using hz
  · right; right; simpa only [hzv, Int.cast_one] using hz

theorem integral_big_quartic_eq_traces {V : Type} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] (hH : IsIntegralGraph H) :
    ((bigEigs H).map (fun x => x ^ 2 * (x ^ 2 - 1))).sum =
      (((H.adjMatrix ℤ) ^ 4).trace : ℝ) - (((H.adjMatrix ℤ) ^ 2).trace : ℝ) := by
  have hfilter : ((bigEigs H).map (fun x => x ^ 2 * (x ^ 2 - 1))).sum =
      ((spec H).map (fun x => x ^ 2 * (x ^ 2 - 1))).sum := by
    apply sum_filter_large_eq
    intro x hx hsmall
    rcases small_integral_spec_entry H hH x hx hsmall with hxv | hxv | hxv
    · rw [hxv]; norm_num
    · rw [hxv]; norm_num
    · rw [hxv]; norm_num
  rw [hfilter]
  have hpoly : (fun x : ℝ => x ^ 2 * (x ^ 2 - 1)) = (fun x => x ^ 4 - x ^ 2) := by
    funext x
    ring
  rw [hpoly, Multiset.sum_map_sub, graph_moment_eq_int_trace, graph_moment_eq_int_trace]

theorem integral_big_odd_eq_trace {V : Type} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] (hH : IsIntegralGraph H)
    (L : ℕ) (hL : Odd L) :
    ((bigEigs H).map (fun x => x ^ L - x)).sum = (((H.adjMatrix ℤ) ^ L).trace : ℝ) := by
  have hL0 : L ≠ 0 := by
    intro heq
    subst L
    norm_num at hL
  have hfilter : ((bigEigs H).map (fun x => x ^ L - x)).sum =
      ((spec H).map (fun x => x ^ L - x)).sum := by
    apply sum_filter_large_eq
    intro x hx hsmall
    rcases small_integral_spec_entry H hH x hx hsmall with hxv | hxv | hxv
    · rw [hxv, hL.neg_one_pow, sub_self]
    · simp only [hxv, zero_pow hL0, sub_self]
    · simp only [hxv, one_pow, sub_self]
  rw [hfilter, Multiset.sum_map_sub, Multiset.map_id', graph_moment_eq_int_trace,
    graph_first_moment_zero, sub_zero]

end Paper7Moments

#print axioms Paper7Moments.sum_filter_large_eq
#print axioms Paper7Moments.small_integral_spec_entry
#print axioms Paper7Moments.integral_big_quartic_eq_traces
#print axioms Paper7Moments.integral_big_odd_eq_trace
