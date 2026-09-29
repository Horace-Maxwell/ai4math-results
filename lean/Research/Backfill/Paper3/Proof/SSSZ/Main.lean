import Research.Backfill.Paper3.Proof.SSSZ.Cover
import Research.Backfill.Paper3.Proof.Poly

/-!
# Tier C: `SSSZBound`, `KahnZhao`, `CareniniProp21`, `QuestionTrueZero`

`SSSZBound` is `sssz_bound` (proved for `0 ≤ q ≤ 1`); `KahnZhao` is its case `q = 0`
(`P_G(0) = i_0(G)`, `P_d(0) = 2^{d+1} - 1`); `CareniniProp21` follows from the Markov-type bound
`[e(A) ≤ γdn] ≤ e^{γtn} q^{e(A)}` with `q = e^{-t/d}`; `QuestionTrueZero` from `KahnZhao` and
`i_0(m K_{d,d}) = P_d(0)^m` (`Research.Backfill.Paper3.Proof.Poly`).
-/

set_option autoImplicit false

open Finset BackfillPaper3.Challenge

namespace P3SSSZ

theorem evalR_pow (p : Polynomial ℤ) (m : ℕ) (q : ℝ) : evalR (p ^ m) q = evalR p q ^ m := by
  unfold evalR
  exact map_pow _ _ _

/-- Counting a filter by a weight that is `≥ 1` on it and `≥ 0` everywhere. -/
theorem card_filter_le_sum {α : Type*} (s : Finset α) (p : α → Prop) [DecidablePred p]
    (f : α → ℝ) (hf : ∀ a ∈ s, 0 ≤ f a) (h : ∀ a ∈ s, p a → 1 ≤ f a) :
    (#(s.filter p) : ℝ) ≤ ∑ a ∈ s, f a := by
  rw [card_eq_sum_ones, Nat.cast_sum, Nat.cast_one]
  calc ∑ a ∈ s.filter p, (1 : ℝ) ≤ ∑ a ∈ s.filter p, f a :=
        sum_le_sum fun a ha => h a (mem_filter.mp ha).1 (mem_filter.mp ha).2
    _ ≤ ∑ a ∈ s, f a := sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun a ha _ => hf a ha

theorem check_SSSZBound : SSSZBound := by
  intro d hd V _ _ G _ hG q hq0 hq1
  exact sssz_bound d hd G hG hq0.le hq1

#print axioms check_SSSZBound

theorem check_KahnZhao : KahnZhao := by
  intro d hd V _ _ G _ hG
  have h := sssz_bound d hd G hG le_rfl zero_le_one
  rwa [evalR_edgePoly_zero, evalR_Pd_zero] at h

#print axioms check_KahnZhao

theorem check_CareniniProp21 : CareniniProp21 := by
  intro d hd V _ _ G _ hG γ hγ t ht
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  have hq0 : 0 ≤ Real.exp (-t / d) := (Real.exp_pos _).le
  have hq1 : Real.exp (-t / d) ≤ 1 :=
    Real.exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr ht) hdpos.le)
  have hB := sssz_bound d hd G hG hq0 hq1
  have hM : (iGamma G d γ : ℝ) ≤
      ∑ A : Finset V, Real.exp (γ * t * Fintype.card V) * Real.exp (-t / d) ^ edgesIn G A := by
    unfold iGamma
    refine card_filter_le_sum _ _ _ (fun A _ => mul_nonneg (Real.exp_pos _).le (pow_nonneg hq0 _))
      fun A _ hA => ?_
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    apply Real.one_le_exp
    have h1 : γ * t * Fintype.card V + (edgesIn G A : ℝ) * (-t / d) =
        t / d * (γ * d * Fintype.card V - edgesIn G A) := by
      field_simp
      ring
    rw [h1]
    exact mul_nonneg (div_nonneg ht hdpos.le) (sub_nonneg.mpr hA)
  rw [← mul_sum, ← evalR_edgePoly] at hM
  exact hM.trans (mul_le_mul_of_nonneg_left hB (Real.exp_pos _).le)

#print axioms check_CareniniProp21

theorem check_QuestionTrueZero : QuestionTrueZero := by
  intro n d hadm V _ _ G _ hcard hG
  obtain ⟨hd, -, m, hm⟩ := hadm
  have hd0 : 0 < 2 * d := by omega
  have hdR : (d : ℝ) ≠ 0 := by
    have : (0 : ℝ) < d := by exact_mod_cast hd
    exact this.ne'
  have hmdiv : n / (2 * d) = m := by
    rw [hm]
    exact Nat.mul_div_cancel_left m hd0
  rw [hmdiv, P3Basic.iGamma_eq_iCount (γ := 0) G d 0 (by simp),
    P3Basic.iGamma_eq_iCount (γ := 0) (KddUnion m d) d 0 (by simp)]
  have hKZ := check_KahnZhao d hd V G hG
  have hK : (iCount (KddUnion m d) 0 : ℝ) = ((2 : ℝ) ^ (d + 1) - 1) ^ m := by
    rw [← evalR_edgePoly_zero, P3Basic.check_PolyFacts.2.2.1 m d, evalR_pow, evalR_Pd_zero]
  have hexp : (Fintype.card V : ℝ) / (2 * d) = m := by
    rw [hcard, hm]
    push_cast
    field_simp
  rw [hexp, Real.rpow_natCast, ← hK] at hKZ
  exact_mod_cast hKZ

#print axioms check_QuestionTrueZero

end P3SSSZ
