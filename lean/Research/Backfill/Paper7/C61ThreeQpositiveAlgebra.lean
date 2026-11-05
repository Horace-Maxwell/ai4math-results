import Research.Backfill.Paper7.C61ThreeUnitWitness
import Research.Backfill.Paper7.C61ThreeMonodromy

/-! NEW SOURCE ONLY. The hypotheses in the algebraic helpers are all obtained
from the original profile by the final wrapper. No tuple classification is used. -/
set_option autoImplicit false
noncomputable section
namespace Paper7C61Three
open BackfillPaper7.Challenge BackfillPaper7.Challenge.Legacy.Algebra
open Paper7C61Profile
open scoped BigOperators Classical

def PairTwo (p q : Fin 6 → ℕ) : Prop :=
  coefficientTwo p q 0 * coefficientTwo p q 1 +
    coefficientTwo p q 3 * coefficientTwo p q 4 = 2 ∧
  coefficientTwo p q 1 * coefficientTwo p q 2 +
    coefficientTwo p q 4 * coefficientTwo p q 5 = 2 ∧
  coefficientTwo p q 2 * coefficientTwo p q 3 +
    coefficientTwo p q 5 * coefficientTwo p q 0 = 2
#print axioms Paper7C61Three.PairTwo

theorem pair_two_shift (p q : Fin 6 → ℕ) (h : PairTwo p q) :
    PairTwo (shiftSix p) (shiftSix q) := by
  obtain ⟨h0, h1, h2⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · simpa only [coefficientTwo, shiftSix, show (0 : Fin 6) + 1 = 1 from rfl, show (1 : Fin 6) + 1 = 2 from rfl, show (2 : Fin 6) + 1 = 3 from rfl, show (3 : Fin 6) + 1 = 4 from rfl, show (4 : Fin 6) + 1 = 5 from rfl, show (5 : Fin 6) + 1 = 0 from rfl, show (0 : Fin 6) + 5 = 5 from rfl, show (1 : Fin 6) + 5 = 0 from rfl, show (2 : Fin 6) + 5 = 1 from rfl, show (3 : Fin 6) + 5 = 2 from rfl, show (4 : Fin 6) + 5 = 3 from rfl, show (5 : Fin 6) + 5 = 4 from rfl] using h1
  · simpa only [coefficientTwo, shiftSix, show (0 : Fin 6) + 1 = 1 from rfl, show (1 : Fin 6) + 1 = 2 from rfl, show (2 : Fin 6) + 1 = 3 from rfl, show (3 : Fin 6) + 1 = 4 from rfl, show (4 : Fin 6) + 1 = 5 from rfl, show (5 : Fin 6) + 1 = 0 from rfl, show (0 : Fin 6) + 5 = 5 from rfl, show (1 : Fin 6) + 5 = 0 from rfl, show (2 : Fin 6) + 5 = 1 from rfl, show (3 : Fin 6) + 5 = 2 from rfl, show (4 : Fin 6) + 5 = 3 from rfl, show (5 : Fin 6) + 5 = 4 from rfl] using h2
  · simpa [coefficientTwo, shiftSix, show (0 : Fin 6) + 1 = 1 from rfl, show (1 : Fin 6) + 1 = 2 from rfl, show (2 : Fin 6) + 1 = 3 from rfl, show (3 : Fin 6) + 1 = 4 from rfl, show (4 : Fin 6) + 1 = 5 from rfl, show (5 : Fin 6) + 1 = 0 from rfl, show (0 : Fin 6) + 5 = 5 from rfl, show (1 : Fin 6) + 5 = 0 from rfl, show (2 : Fin 6) + 5 = 1 from rfl, show (3 : Fin 6) + 5 = 2 from rfl, show (4 : Fin 6) + 5 = 3 from rfl, show (5 : Fin 6) + 5 = 4 from rfl, add_comm] using h0
#print axioms Paper7C61Three.pair_two_shift

theorem total_shift (p q : Fin 6 → ℕ) :
    totalP 6 (shiftSix p) + totalQ 6 (shiftSix q) = totalP 6 p + totalQ 6 q := by
  simp only [totalP, totalQ, shiftSix, Fin.sum_univ_six, show (0 : Fin 6) + 1 = 1 from rfl, show (1 : Fin 6) + 1 = 2 from rfl, show (2 : Fin 6) + 1 = 3 from rfl, show (3 : Fin 6) + 1 = 4 from rfl, show (4 : Fin 6) + 1 = 5 from rfl, show (5 : Fin 6) + 1 = 0 from rfl]
  omega
#print axioms Paper7C61Three.total_shift

theorem odd_zero_even_q_impossible (p q : Fin 6 → ℕ)
    (hp1 : p 1 = 0) (hp3 : p 3 = 0) (hp5 : p 5 = 0)
    (hw : FullUnitWitness p q) (hm : PairTwo p q) (hq0 : 0 < q 0) : False := by
  have hq1 : q 1 = 0 := by
    simpa only [nxt_six, show (0 : Fin 6) + 1 = 1 from rfl, show (1 : Fin 6) + 1 = 2 from rfl, show (2 : Fin 6) + 1 = 3 from rfl, show (3 : Fin 6) + 1 = 4 from rfl, show (4 : Fin 6) + 1 = 5 from rfl, show (5 : Fin 6) + 1 = 0 from rfl, show (0 : Fin 6) + 5 = 5 from rfl, show (1 : Fin 6) + 5 = 0 from rfl, show (2 : Fin 6) + 5 = 1 from rfl, show (3 : Fin 6) + 5 = 2 from rfl, show (4 : Fin 6) + 5 = 3 from rfl, show (5 : Fin 6) + 5 = 4 from rfl] using full_unit_witness_adjacent p q hw 0 hq0
  have hq5 : q 5 = 0 := by
    by_contra hn
    have h := full_unit_witness_adjacent p q hw 5 (Nat.pos_of_ne_zero hn)
    norm_num only [nxt_six, show (0 : Fin 6) + 1 = 1 from rfl, show (1 : Fin 6) + 1 = 2 from rfl, show (2 : Fin 6) + 1 = 3 from rfl, show (3 : Fin 6) + 1 = 4 from rfl, show (4 : Fin 6) + 1 = 5 from rfl, show (5 : Fin 6) + 1 = 0 from rfl, show (0 : Fin 6) + 5 = 5 from rfl, show (1 : Fin 6) + 5 = 0 from rfl, show (2 : Fin 6) + 5 = 1 from rfl, show (3 : Fin 6) + 5 = 2 from rfl, show (4 : Fin 6) + 5 = 3 from rfl, show (5 : Fin 6) + 5 = 4 from rfl] at h
    omega
  obtain ⟨y, hy0, hy1, hy⟩ := hw 0 hq0
  norm_num only [nxt_six, show (0 : Fin 6) + 1 = 1 from rfl, show (1 : Fin 6) + 1 = 2 from rfl, show (2 : Fin 6) + 1 = 3 from rfl, show (3 : Fin 6) + 1 = 4 from rfl, show (4 : Fin 6) + 1 = 5 from rfl, show (5 : Fin 6) + 1 = 0 from rfl, show (0 : Fin 6) + 5 = 5 from rfl, show (1 : Fin 6) + 5 = 0 from rfl, show (2 : Fin 6) + 5 = 1 from rfl, show (3 : Fin 6) + 5 = 2 from rfl, show (4 : Fin 6) + 5 = 3 from rfl, show (5 : Fin 6) + 5 = 4 from rfl] at hy1
  have hr1 := (hy 1).2 hq1
  norm_num only [prv_six, nxt_six, show (0 : Fin 6) + 1 = 1 from rfl, show (1 : Fin 6) + 1 = 2 from rfl, show (2 : Fin 6) + 1 = 3 from rfl, show (3 : Fin 6) + 1 = 4 from rfl, show (4 : Fin 6) + 1 = 5 from rfl, show (5 : Fin 6) + 1 = 0 from rfl, show (0 : Fin 6) + 5 = 5 from rfl, show (1 : Fin 6) + 5 = 0 from rfl, show (2 : Fin 6) + 5 = 1 from rfl, show (3 : Fin 6) + 5 = 2 from rfl, show (4 : Fin 6) + 5 = 3 from rfl, show (5 : Fin 6) + 5 = 4 from rfl, hp1, Nat.cast_zero, sub_zero, one_mul] at hr1
  have hy2 : y 2 = 1 := by linarith
  have hq2 : q 2 = 0 := by
    by_contra hn
    have hz := (hy 2).1 (Nat.pos_of_ne_zero hn)
    linarith
  have hq4 : q 4 = 0 := by
    by_contra hn
    obtain ⟨z, hz4, hz5, hz⟩ := hw 4 (Nat.pos_of_ne_zero hn)
    norm_num only [nxt_six, show (0 : Fin 6) + 1 = 1 from rfl, show (1 : Fin 6) + 1 = 2 from rfl, show (2 : Fin 6) + 1 = 3 from rfl, show (3 : Fin 6) + 1 = 4 from rfl, show (4 : Fin 6) + 1 = 5 from rfl, show (5 : Fin 6) + 1 = 0 from rfl, show (0 : Fin 6) + 5 = 5 from rfl, show (1 : Fin 6) + 5 = 0 from rfl, show (2 : Fin 6) + 5 = 1 from rfl, show (3 : Fin 6) + 5 = 2 from rfl, show (4 : Fin 6) + 5 = 3 from rfl, show (5 : Fin 6) + 5 = 4 from rfl] at hz5
    have hz0 := (hz 0).1 hq0
    have hr5 := (hz 5).2 hq5
    norm_num only [prv_six, nxt_six, show (0 : Fin 6) + 1 = 1 from rfl, show (1 : Fin 6) + 1 = 2 from rfl, show (2 : Fin 6) + 1 = 3 from rfl, show (3 : Fin 6) + 1 = 4 from rfl, show (4 : Fin 6) + 1 = 5 from rfl, show (5 : Fin 6) + 1 = 0 from rfl, show (0 : Fin 6) + 5 = 5 from rfl, show (1 : Fin 6) + 5 = 0 from rfl, show (2 : Fin 6) + 5 = 1 from rfl, show (3 : Fin 6) + 5 = 2 from rfl, show (4 : Fin 6) + 5 = 3 from rfl, show (5 : Fin 6) + 5 = 4 from rfl, hp5, Nat.cast_zero, sub_zero, one_mul] at hr5
    linarith
  have hps : p 2 = 0 ∧ p 4 = 0 := by
    by_cases hq3 : 0 < q 3
    · have hy3 := (hy 3).1 hq3
      have hr2 := (hy 2).2 hq2
      norm_num only [prv_six, nxt_six, show (0 : Fin 6) + 1 = 1 from rfl, show (1 : Fin 6) + 1 = 2 from rfl, show (2 : Fin 6) + 1 = 3 from rfl, show (3 : Fin 6) + 1 = 4 from rfl, show (4 : Fin 6) + 1 = 5 from rfl, show (5 : Fin 6) + 1 = 0 from rfl, show (0 : Fin 6) + 5 = 5 from rfl, show (1 : Fin 6) + 5 = 0 from rfl, show (2 : Fin 6) + 5 = 1 from rfl, show (3 : Fin 6) + 5 = 2 from rfl, show (4 : Fin 6) + 5 = 3 from rfl, show (5 : Fin 6) + 5 = 4 from rfl] at hr2
      rw [hy1, hy2, hy3] at hr2
      have hp2R : (p 2 : ℝ) = 0 := by nlinarith
      obtain ⟨z, hz3, hz4, hz⟩ := hw 3 hq3
      norm_num only [nxt_six, show (0 : Fin 6) + 1 = 1 from rfl, show (1 : Fin 6) + 1 = 2 from rfl, show (2 : Fin 6) + 1 = 3 from rfl, show (3 : Fin 6) + 1 = 4 from rfl, show (4 : Fin 6) + 1 = 5 from rfl, show (5 : Fin 6) + 1 = 0 from rfl, show (0 : Fin 6) + 5 = 5 from rfl, show (1 : Fin 6) + 5 = 0 from rfl, show (2 : Fin 6) + 5 = 1 from rfl, show (3 : Fin 6) + 5 = 2 from rfl, show (4 : Fin 6) + 5 = 3 from rfl, show (5 : Fin 6) + 5 = 4 from rfl] at hz4
      have hz0 := (hz 0).1 hq0
      have hr5 := (hz 5).2 hq5
      norm_num only [prv_six, nxt_six, show (0 : Fin 6) + 1 = 1 from rfl, show (1 : Fin 6) + 1 = 2 from rfl, show (2 : Fin 6) + 1 = 3 from rfl, show (3 : Fin 6) + 1 = 4 from rfl, show (4 : Fin 6) + 1 = 5 from rfl, show (5 : Fin 6) + 1 = 0 from rfl, show (0 : Fin 6) + 5 = 5 from rfl, show (1 : Fin 6) + 5 = 0 from rfl, show (2 : Fin 6) + 5 = 1 from rfl, show (3 : Fin 6) + 5 = 2 from rfl, show (4 : Fin 6) + 5 = 3 from rfl, show (5 : Fin 6) + 5 = 4 from rfl, hp5, Nat.cast_zero, sub_zero, one_mul] at hr5
      have hz5 : z 5 = 1 := by linarith
      have hr4 := (hz 4).2 hq4
      norm_num only [prv_six, nxt_six, show (0 : Fin 6) + 1 = 1 from rfl, show (1 : Fin 6) + 1 = 2 from rfl, show (2 : Fin 6) + 1 = 3 from rfl, show (3 : Fin 6) + 1 = 4 from rfl, show (4 : Fin 6) + 1 = 5 from rfl, show (5 : Fin 6) + 1 = 0 from rfl, show (0 : Fin 6) + 5 = 5 from rfl, show (1 : Fin 6) + 5 = 0 from rfl, show (2 : Fin 6) + 5 = 1 from rfl, show (3 : Fin 6) + 5 = 2 from rfl, show (4 : Fin 6) + 5 = 3 from rfl, show (5 : Fin 6) + 5 = 4 from rfl] at hr4
      rw [hz3, hz4, hz5] at hr4
      have hp4R : (p 4 : ℝ) = 0 := by nlinarith
      exact ⟨by exact_mod_cast hp2R, by exact_mod_cast hp4R⟩
    · have hq3z : q 3 = 0 := by omega
      have hr2 := (hy 2).2 hq2
      have hr3 := (hy 3).2 hq3z
      have hr4 := (hy 4).2 hq4
      have hr5 := (hy 5).2 hq5
      norm_num only [prv_six, nxt_six, show (0 : Fin 6) + 1 = 1 from rfl, show (1 : Fin 6) + 1 = 2 from rfl, show (2 : Fin 6) + 1 = 3 from rfl, show (3 : Fin 6) + 1 = 4 from rfl, show (4 : Fin 6) + 1 = 5 from rfl, show (5 : Fin 6) + 1 = 0 from rfl, show (0 : Fin 6) + 5 = 5 from rfl, show (1 : Fin 6) + 5 = 0 from rfl, show (2 : Fin 6) + 5 = 1 from rfl, show (3 : Fin 6) + 5 = 2 from rfl, show (4 : Fin 6) + 5 = 3 from rfl, show (5 : Fin 6) + 5 = 4 from rfl, hp3, hp5, Nat.cast_zero, sub_zero, one_mul] at hr2 hr3 hr4 hr5
      rw [hy1, hy2] at hr2
      have hy3 : y 3 = -(p 2 : ℝ) := by nlinarith
      have hy4 : y 4 = -(p 2 : ℝ) - 1 := by linarith
      have hy5 : y 5 = -(p 2 : ℝ) - 1 := by linarith
      rw [hy3, hy4, hy5] at hr4
      have hp2n : (0 : ℝ) ≤ p 2 := Nat.cast_nonneg (p 2)
      have hp4n : (0 : ℝ) ≤ p 4 := Nat.cast_nonneg (p 4)
      have hmul := mul_nonneg hp2n hp4n
      have hp2R : (p 2 : ℝ) = 0 := by nlinarith
      have hp4R : (p 4 : ℝ) = 0 := by nlinarith
      exact ⟨by exact_mod_cast hp2R, by exact_mod_cast hp4R⟩
  have hh := hm.2.1
  norm_num [coefficientTwo, hp1, hp5, hps.1, hps.2, hq1, hq2, hq4, hq5] at hh
#print axioms Paper7C61Three.odd_zero_even_q_impossible

theorem odd_zero_three_ones_impossible (p q : Fin 6 → ℕ)
    (hp1 : p 1 = 0) (hp3 : p 3 = 0) (hp5 : p 5 = 0)
    (hq0 : q 0 = 0) (hq2 : q 2 = 0) (hq4 : q 4 = 0)
    (hp0 : p 0 = 1) (hp2 : p 2 = 1) (hp4 : p 4 = 1)
    (hm : PairTwo p q) (hs : totalP 6 p + totalQ 6 q = 11) : False := by
  obtain ⟨h0, h1, h2⟩ := hm
  norm_num [coefficientTwo, hp0, hp1, hp2, hp3, hp4, hp5, hq0, hq2, hq4] at h0 h1 h2
  have hsR : (totalP 6 p : ℝ) + totalQ 6 q = 11 := by exact_mod_cast hs
  norm_num [totalP, totalQ, Fin.sum_univ_succ,
    hp0, hp1, hp2, hp3, hp4, hp5, hq0, hq2, hq4] at hsR
  linarith
#print axioms Paper7C61Three.odd_zero_three_ones_impossible

theorem natural_product_one (a b : ℕ) (h : (a : ℝ) * b = 1) : a = 1 ∧ b = 1 := by
  have hn : a * b = 1 := by exact_mod_cast h
  have ha : 1 ≤ a := by
    by_contra hz
    have hzero : a = 0 := by omega
    simp [hzero] at hn
  have hb : 1 ≤ b := by
    by_contra hz
    have hzero : b = 0 := by omega
    simp [hzero] at hn
  exact (mul_eq_one_iff_of_one_le ha hb).mp hn
#print axioms Paper7C61Three.natural_product_one

theorem singleton_dirichlet_bound (a b c : ℕ)
    (h : (a : ℝ) * b * (c + 1) = a + b) :
    (a = 0 ∧ b = 0) ∨ a + b + c ≤ 4 := by
  by_cases ha : a = 0
  · left
    refine ⟨ha, ?_⟩
    have hbR : (b : ℝ) = 0 := by simpa [ha] using h.symm
    exact_mod_cast hbR
  by_cases hb : b = 0
  · have haR : (a : ℝ) = 0 := by simpa [hb] using h.symm
    exact (ha (by exact_mod_cast haR)).elim
  right
  have haN : 1 ≤ a := Nat.one_le_iff_ne_zero.mpr ha
  have hbN : 1 ≤ b := Nat.one_le_iff_ne_zero.mpr hb
  have ha1 : (1 : ℝ) ≤ a := by exact_mod_cast haN
  have hb1 : (1 : ℝ) ≤ b := by exact_mod_cast hbN
  have hc0 : (0 : ℝ) ≤ c := Nat.cast_nonneg c
  have hbase := mul_nonneg (sub_nonneg.mpr ha1) (sub_nonneg.mpr hb1)
  have hab : (1 : ℝ) ≤ (a : ℝ) * b := by nlinarith
  have hc1 : c ≤ 1 := by
    by_contra hn
    have hc2 : (2 : ℝ) ≤ c := by exact_mod_cast (show 2 ≤ c by omega)
    have hm := mul_nonneg (sub_nonneg.mpr hab) (sub_nonneg.mpr hc2)
    nlinarith
  have hc : c = 0 ∨ c = 1 := by omega
  rcases hc with rfl | rfl
  · norm_num at h
    have ha2 : a ≤ 2 := by
      by_contra hn
      have ha3 : (3 : ℝ) ≤ a := by exact_mod_cast (show 3 ≤ a by omega)
      have hb2N : 2 ≤ b := by
        by_contra hh
        have hbEq : b = 1 := by omega
        norm_num [hbEq] at h
      have hb2 : (2 : ℝ) ≤ b := by exact_mod_cast hb2N
      have hm := mul_nonneg (show (0 : ℝ) ≤ (a : ℝ) - 3 by linarith)
        (show (0 : ℝ) ≤ (b : ℝ) - 2 by linarith)
      nlinarith
    have hb2 : b ≤ 2 := by
      by_contra hn
      have hb3 : (3 : ℝ) ≤ b := by exact_mod_cast (show 3 ≤ b by omega)
      have haN : a = 1 ∨ a = 2 := by omega
      rcases haN with haN | haN <;> norm_num [haN] at h
      nlinarith
    omega
  · norm_num at h
    obtain ⟨haEq, hbEq⟩ := natural_product_one a b (by nlinarith)
    omega
#print axioms Paper7C61Three.singleton_dirichlet_bound

end Paper7C61Three
