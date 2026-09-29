import Research.Backfill.Paper3.Challenge
import Research.Backfill.Paper3.Proof.L8.Core
import Research.Backfill.Paper3.Proof.L8.Bridge

/-!
# Paper 3, Lemma 8: lower bound in Cramér's theorem for laws on `{0, …, M}`

`check_Lemma8` and `check_Lemma8_bddBelow` prove the frozen statements `Lemma8` and
`Lemma8_bddBelow`. The integrals against `p` are finite sums (`Research.Backfill.Paper3.Proof.L8.Bridge`), the probability
of `Σ ξ_i ∈ A` is bounded below by coefficient sums of `(Σ_i p(i) z^i)^m` (`Research.Backfill.Paper3.Proof.L8.Bridge`), and
those are bounded below by exponential tilting and Chebyshev's inequality (`Research.Backfill.Paper3.Proof.L8.Core`).
-/

set_option autoImplicit false

namespace P3L8

open MeasureTheory ProbabilityTheory Polynomial Finset Filter

theorem check_Lemma8_bddBelow : BackfillPaper3.Challenge.Lemma8_bddBelow := by
  intro M p hsupp h0 hM x hx0 hxM
  set a : ℕ → ℝ := fun i => (p i).toReal with ha_def
  have ha : ∀ i, 0 ≤ a i := fun i => ENNReal.toReal_nonneg
  have ha0 : 0 < a 0 := ENNReal.toReal_pos h0 (p.apply_ne_top 0)
  have haM : 0 < a M := ENNReal.toReal_pos hM (p.apply_ne_top M)
  have hZ : ∀ l : ℝ, ∫ i, Real.exp (l * i) ∂p.toMeasure = Zf a M l := by
    intro l
    rw [integral_pmf p M hsupp]
    rfl
  simp_rw [hZ]
  exact ⟨bddBelow_Ici a M ha haM x hxM, bddBelow_Iic a M ha ha0 x hx0⟩

theorem check_Lemma8 : BackfillPaper3.Challenge.Lemma8 := by
  intro M p hsupp h0 hM
  set a : ℕ → ℝ := fun i => (p i).toReal with ha_def
  have ha : ∀ i, 0 ≤ a i := fun i => ENNReal.toReal_nonneg
  have ha0 : 0 < a 0 := ENNReal.toReal_pos h0 (p.apply_ne_top 0)
  have haM : 0 < a M := ENNReal.toReal_pos hM (p.apply_ne_top M)
  have hsum : ∑ i ∈ range (M + 1), a i = 1 := sum_toReal_eq_one p M hsupp
  have hZ : ∀ l : ℝ, ∫ i, Real.exp (l * i) ∂p.toMeasure = Zf a M l := by
    intro l
    rw [integral_pmf p M hsupp]
    rfl
  have hE : ∫ i, (i : ℝ) ∂p.toMeasure = ∑ i ∈ range (M + 1), (i : ℝ) * a i := by
    rw [integral_pmf p M hsupp]
    apply sum_congr rfl
    intro i _
    rw [mul_comm]
  simp_rw [hZ]
  rw [hE]
  constructor
  · intro x hx1 hx2 ε hε
    filter_upwards [core_a a M ha hsum ha0 haM x hx1 hx2 ε hε] with m hm
    intro Ω _ P _ ξ hind hlaw
    refine hm.trans ?_
    have hset : {ω | (m : ℝ) * x < ∑ i, (ξ i ω : ℝ)} =
        {ω | (∑ i, ξ i ω) ∈ {s : ℕ | (m : ℝ) * x < s}} := by
      ext ω
      simp only [Set.mem_ofPred_eq, Nat.cast_sum]
    rw [hset]
    exact prob_ge_sum p M hsupp m P ξ hind hlaw _ _ (fun s hs => (mem_filter.mp hs).2)
  · intro x hx1 hx2 ε hε
    filter_upwards [core_b a M ha hsum ha0 x hx1 hx2 ε hε] with m hm
    intro Ω _ P _ ξ hind hlaw
    refine hm.trans ?_
    have hset : {ω | ∑ i, (ξ i ω : ℝ) < m * x} =
        {ω | (∑ i, ξ i ω) ∈ {s : ℕ | (s : ℝ) < m * x}} := by
      ext ω
      simp only [Set.mem_ofPred_eq, Nat.cast_sum]
    rw [hset]
    exact prob_ge_sum p M hsupp m P ξ hind hlaw _ _ (fun s hs => (mem_filter.mp hs).2)

#print axioms check_Lemma8
#print axioms check_Lemma8_bddBelow

end P3L8
