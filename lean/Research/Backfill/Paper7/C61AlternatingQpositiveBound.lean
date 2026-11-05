import Research.Backfill.Paper7.C61ThreeQpositiveAlgebra
import Research.Backfill.Paper7.C61FinSixIndexSimp

/-! NEW SOURCE ONLY. General total bound from the actual saturated unit
kernel recurrence and eigenvalue-two pair identities. -/
set_option autoImplicit false
noncomputable section
namespace Paper7C61Four
open BackfillPaper7.Challenge BackfillPaper7.Challenge.Legacy.Algebra
open Paper7C61Three
open scoped BigOperators Classical

theorem odd_zero_three_ones_total_nine (p q : Fin 6 → ℕ)
    (hp1 : p 1 = 0) (hp3 : p 3 = 0) (hp5 : p 5 = 0)
    (hq0 : q 0 = 0) (hq2 : q 2 = 0) (hq4 : q 4 = 0)
    (hp0 : p 0 = 1) (hp2 : p 2 = 1) (hp4 : p 4 = 1)
    (hm : PairTwo p q) : totalP 6 p + totalQ 6 q = 9 := by
  obtain ⟨h0, h1, h2⟩ := hm
  norm_num [coefficientTwo, hp0, hp1, hp2, hp3, hp4, hp5, hq0, hq2, hq4] at h0 h1 h2
  have hQR : (q 1 : ℝ) + q 3 + q 5 = 6 := by linarith
  have hQN : q 1 + q 3 + q 5 = 6 := by exact_mod_cast hQR
  norm_num [totalP, totalQ, Fin.sum_univ_succ,
    hp0, hp1, hp2, hp3, hp4, hp5, hq0, hq2, hq4]
  omega
#print axioms Paper7C61Four.odd_zero_three_ones_total_nine

theorem odd_zero_q_one_total_bound (p q : Fin 6 → ℕ) (C : ℕ)
    (hp1 : p 1 = 0) (hp3 : p 3 = 0) (hp5 : p 5 = 0)
    (hq0 : q 0 = 0) (hq2 : q 2 = 0) (hq4 : q 4 = 0)
    (hw : FullUnitWitness p q) (hm : PairTwo p q)
    (hl : ∀ k, p k + q k ≤ C) (hq1 : 0 < q 1) :
    totalP 6 p + totalQ 6 q = 9 ∨ totalP 6 p + totalQ 6 q ≤ C + 4 := by
  obtain ⟨y, hy1, hy2, hy⟩ := hw 1 hq1
  norm_num [nxt_six] at hy2
  by_cases hq3 : 0 < q 3
  · have hy3 := (hy 3).1 hq3
    have hr2 := (hy 2).2 hq2
    norm_num [prv_six, nxt_six] at hr2
    rw [hy1, hy2, hy3] at hr2
    have hp2R : (p 2 : ℝ) = 1 := by nlinarith
    have hp2 : p 2 = 1 := by exact_mod_cast hp2R
    obtain ⟨z, hz3, hz4, hz⟩ := hw 3 hq3
    norm_num [nxt_six] at hz4
    have hz1 := (hz 1).1 hq1
    have hr4 := (hz 4).2 hq4
    norm_num [prv_six, nxt_six] at hr4
    rw [hz3, hz4] at hr4
    have hz5 : z 5 = 1 - (p 4 : ℝ) := by nlinarith
    have hpp : p 0 = 1 ∧ p 4 = 1 := by
      by_cases hq5 : 0 < q 5
      · have hz5zero := (hz 5).1 hq5
        have hp4R : (p 4 : ℝ) = 1 := by linarith
        obtain ⟨w, hw5, hw0, hw⟩ := hw 5 hq5
        norm_num [nxt_six] at hw0
        have hw1 := (hw 1).1 hq1
        have hr0 := (hw 0).2 hq0
        norm_num [prv_six, nxt_six] at hr0
        rw [hw5, hw0, hw1] at hr0
        have hp0R : (p 0 : ℝ) = 1 := by nlinarith
        exact ⟨by exact_mod_cast hp0R, by exact_mod_cast hp4R⟩
      · have hq5z : q 5 = 0 := by omega
        have hr5 := (hz 5).2 hq5z
        norm_num [prv_six, nxt_six, hp5, Nat.cast_zero, sub_zero, one_mul] at hr5
        have hz0 : z 0 = -(p 4 : ℝ) := by linarith
        have hr0 := (hz 0).2 hq0
        norm_num [prv_six, nxt_six] at hr0
        rw [hz5, hz1, hz0] at hr0
        exact natural_product_one (p 0) (p 4) (by nlinarith)
    left
    exact odd_zero_three_ones_total_nine p q hp1 hp3 hp5 hq0 hq2 hq4
      hpp.1 hp2 hpp.2 hm
  · have hq3z : q 3 = 0 := by omega
    by_cases hq5 : 0 < q 5
    · have hy5 := (hy 5).1 hq5
      have hr2 := (hy 2).2 hq2
      norm_num [prv_six, nxt_six] at hr2
      rw [hy1, hy2] at hr2
      have hy3 : y 3 = 1 - (p 2 : ℝ) := by nlinarith
      have hr3 := (hy 3).2 hq3z
      norm_num [prv_six, nxt_six, hp3, Nat.cast_zero, sub_zero, one_mul] at hr3
      have hy4 : y 4 = -(p 2 : ℝ) := by linarith
      have hr4 := (hy 4).2 hq4
      norm_num [prv_six, nxt_six] at hr4
      rw [hy3, hy4, hy5] at hr4
      have hp24 : p 2 = 1 ∧ p 4 = 1 :=
        natural_product_one (p 2) (p 4) (by nlinarith)
      obtain ⟨z, hz5, hz0, hz⟩ := hw 5 hq5
      norm_num [nxt_six] at hz0
      have hz1 := (hz 1).1 hq1
      have hr0 := (hz 0).2 hq0
      norm_num [prv_six, nxt_six] at hr0
      rw [hz5, hz0, hz1] at hr0
      have hp0R : (p 0 : ℝ) = 1 := by nlinarith
      have hp0 : p 0 = 1 := by exact_mod_cast hp0R
      left
      exact odd_zero_three_ones_total_nine p q hp1 hp3 hp5 hq0 hq2 hq4
        hp0 hp24.1 hp24.2 hm
    · have hq5z : q 5 = 0 := by omega
      have hr2 := (hy 2).2 hq2
      norm_num [prv_six, nxt_six] at hr2
      rw [hy1, hy2] at hr2
      have hy3 : y 3 = 1 - (p 2 : ℝ) := by nlinarith
      have hr3 := (hy 3).2 hq3z
      norm_num [prv_six, nxt_six, hp3, Nat.cast_zero, sub_zero, one_mul] at hr3
      have hy4 : y 4 = -(p 2 : ℝ) := by linarith
      have hr4 := (hy 4).2 hq4
      norm_num [prv_six, nxt_six] at hr4
      rw [hy3, hy4] at hr4
      have hy5 : y 5 = (p 2 : ℝ) * p 4 - 1 := by nlinarith
      have hr5 := (hy 5).2 hq5z
      norm_num [prv_six, nxt_six, hp5, Nat.cast_zero, sub_zero, one_mul] at hr5
      have hy0 : y 0 = (p 2 : ℝ) * p 4 + p 2 - 1 := by linarith
      have hr0 := (hy 0).2 hq0
      norm_num [prv_six, nxt_six] at hr0
      rw [hy5, hy1, hy0] at hr0
      have hd : (p 0 : ℝ) * p 2 * (p 4 + 1) = p 0 + p 2 := by nlinarith
      rcases singleton_dirichlet_bound (p 0) (p 2) (p 4) hd with hz | hb
      · exfalso
        have hh := hm.2.2
        norm_num [coefficientTwo, hz.1, hz.2, hp3, hp5, hq0, hq2, hq3z, hq5z] at hh
      · right
        have hql := hl 1
        rw [hp1, zero_add] at hql
        norm_num [totalP, totalQ, Fin.sum_univ_succ,
          hp1, hp3, hp5, hq0, hq2, hq3z, hq4, hq5z]
        omega
#print axioms Paper7C61Four.odd_zero_q_one_total_bound

end Paper7C61Four
