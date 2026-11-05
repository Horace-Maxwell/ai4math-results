import Research.Backfill.Paper7.CycleCosineThreshold
import Research.Backfill.Paper7.SpectralMoments

/-! Source-only classification of actual bare cycle graphs for every b >= 3.
The existing complete Fourier characteristic polynomial and real spectral
multiset are reused. This is not the general unicyclic IntroUnicyclic21 check,
and it supplies no reduction of branching attachment trees to sun graphs.
Repair02 is uncompiled. The prior source failed actual development463;
its first seven declarations printed Std3, but that failed module is not a
successful producer. Only the three finite cosine proof bodies are repaired. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace Paper7BareCycle
open Polynomial BackfillPaper7.Challenge Paper7Lemma41

theorem cycleCosine_mem_spec (b : ℕ) [NeZero b] (hb : 3 ≤ b) (k : ZMod b) :
    cycleCosine b k ∈ spec (SimpleGraph.cycleGraph b) := by
  rw [cycleGraph_spec b hb]
  exact Multiset.mem_map.mpr ⟨k, by simp, rfl⟩
#print axioms Paper7BareCycle.cycleCosine_mem_spec

theorem cycle_integral_iff_integer_cosines (b : ℕ) [NeZero b] (hb : 3 ≤ b) :
    IsIntegralGraph (SimpleGraph.cycleGraph b) ↔
      ∀ k : ZMod b, ∃ z : ℤ, cycleCosine b k = (z : ℝ) := by
  constructor
  · intro hG k
    exact Paper7Moments.integral_spec_entry (SimpleGraph.cycleGraph b) hG
      (cycleCosine b k) (cycleCosine_mem_spec b hb k)
  · intro h μ hμ
    have hroot := Matrix.mem_spectrum_iff_isRoot_charpoly.mp hμ
    rw [cycleGraph_charpoly_complex b hb] at hroot
    obtain ⟨k, _hk, hk⟩ := (Polynomial.isRoot_prod _ _ μ).mp hroot
    have hμk : μ = (cycleCosine b k : ℂ) := by
      simpa only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C,
        character_pair_eq_cycleCosine, sub_eq_zero] using hk.eq_zero
    obtain ⟨z, hz⟩ := h k
    refine ⟨z, hμk.trans ?_⟩
    simpa only [Complex.ofReal_intCast] using
      congrArg (fun x : ℝ => (x : ℂ)) hz
#print axioms Paper7BareCycle.cycle_integral_iff_integer_cosines

theorem cycleCosine_one (b : ℕ) [NeZero b] (hb : 3 ≤ b) :
    cycleCosine b (1 : ZMod b) = 2 * Real.cos (2 * Real.pi / b) := by
  simp only [cycleCosine, ZMod.val_one'' (by omega : b ≠ 1),
    Nat.cast_one, mul_one_div]
#print axioms Paper7BareCycle.cycleCosine_one

theorem cycleCosine_one_lt_two (b : ℕ) [NeZero b] (hb : 3 ≤ b) :
    cycleCosine b (1 : ZMod b) < 2 := by
  have hbR : (3 : ℝ) ≤ b := by exact_mod_cast hb
  have hbpos : (0 : ℝ) < b := by linarith
  have hpos : 0 < 2 * Real.pi / b :=
    div_pos (mul_pos (by norm_num) Real.pi_pos) hbpos
  have hpi : 2 * Real.pi / b ≤ Real.pi := by
    apply (div_le_iff₀ hbpos).mpr
    have hm := mul_le_mul_of_nonneg_left (show (2 : ℝ) ≤ b by linarith)
      Real.pi_pos.le
    nlinarith
  have hc := Real.cos_lt_cos_of_nonneg_of_le_pi (x := 0)
    (y := 2 * Real.pi / b) (le_refl 0) hpi hpos
  rw [Real.cos_zero] at hc
  rw [cycleCosine_one b hb]
  linarith
#print axioms Paper7BareCycle.cycleCosine_one_lt_two

theorem cycleGraph_not_integral_of_seven_le (b : ℕ) (hb : 7 ≤ b) :
    ¬ IsIntegralGraph (SimpleGraph.cycleGraph b) := by
  let : NeZero b := ⟨by omega⟩
  have hb3 : 3 ≤ b := by omega
  have hval : (1 : ZMod b).val = 1 := ZMod.val_one'' (by omega)
  have hlo : 1 < cycleCosine b (1 : ZMod b) := by
    apply (cycleCosine_gt_one_iff b 1).mpr
    exact Or.inl (by rw [hval]; omega)
  have hhi := cycleCosine_one_lt_two b hb3
  intro hG
  obtain ⟨z, hz⟩ := (cycle_integral_iff_integer_cosines b hb3).mp hG 1
  rw [hz] at hlo hhi
  have hzlo : (1 : ℤ) < z := by exact_mod_cast hlo
  have hzhi : z < (2 : ℤ) := by exact_mod_cast hhi
  omega
#print axioms Paper7BareCycle.cycleGraph_not_integral_of_seven_le

theorem cycleCosine_five_one_bounds :
    0 < cycleCosine 5 (1 : ZMod 5) ∧ cycleCosine 5 (1 : ZMod 5) < 1 := by
  simp only [cycleCosine_one 5 (by norm_num)]
  have hpos : 0 < Real.cos (2 * Real.pi / 5) := by
    apply Real.cos_pos_of_mem_Ioo
    constructor <;> linarith [Real.pi_pos]
  have hhalf := Real.cos_lt_cos_of_nonneg_of_le_pi (x := Real.pi / 3)
    (y := 2 * Real.pi / 5) (by positivity) (by linarith [Real.pi_pos])
    (by linarith [Real.pi_pos])
  rw [Real.cos_pi_div_three] at hhalf
  constructor <;> linarith
#print axioms Paper7BareCycle.cycleCosine_five_one_bounds

theorem cycleGraph_five_not_integral :
    ¬ IsIntegralGraph (SimpleGraph.cycleGraph 5) := by
  intro hG
  obtain ⟨z, hz⟩ := (cycle_integral_iff_integer_cosines 5 (by norm_num)).mp hG 1
  obtain ⟨hlo, hhi⟩ := cycleCosine_five_one_bounds
  rw [hz] at hlo hhi
  have hzlo : (0 : ℤ) < z := by exact_mod_cast hlo
  have hzhi : z < (1 : ℤ) := by exact_mod_cast hhi
  omega
#print axioms Paper7BareCycle.cycleGraph_five_not_integral

theorem cycle_three_cosines_integer (k : ZMod 3) :
    ∃ z : ℤ, cycleCosine 3 k = (z : ℝ) := by
  fin_cases k
  · refine ⟨2, ?_⟩
    norm_num [cycleCosine, ZMod.val]
  · refine ⟨-1, ?_⟩
    simp only [cycleCosine, ZMod.val, Nat.cast_ofNat, Nat.cast_one]
    rw [show 2 * Real.pi * (1 / 3) = Real.pi - Real.pi / 3 by ring,
      Real.cos_pi_sub, Real.cos_pi_div_three]
    norm_num
  · refine ⟨-1, ?_⟩
    simp only [cycleCosine, ZMod.val, Nat.cast_ofNat]
    rw [show 2 * Real.pi * (2 / 3) =
      2 * Real.pi - (Real.pi - Real.pi / 3) by ring,
      Real.cos_two_pi_sub, Real.cos_pi_sub, Real.cos_pi_div_three]
    norm_num
#print axioms Paper7BareCycle.cycle_three_cosines_integer

theorem cycle_four_cosines_integer (k : ZMod 4) :
    ∃ z : ℤ, cycleCosine 4 k = (z : ℝ) := by
  fin_cases k
  · refine ⟨2, ?_⟩
    norm_num [cycleCosine, ZMod.val]
  · refine ⟨0, ?_⟩
    simp only [cycleCosine, ZMod.val, Nat.cast_ofNat, Nat.cast_one]
    rw [show 2 * Real.pi * (1 / 4) = Real.pi / 2 by ring,
      Real.cos_pi_div_two]
    norm_num
  · refine ⟨-2, ?_⟩
    simp only [cycleCosine, ZMod.val, Nat.cast_ofNat]
    rw [show 2 * Real.pi * (2 / 4) = Real.pi by ring, Real.cos_pi]
    norm_num
  · refine ⟨0, ?_⟩
    simp only [cycleCosine, ZMod.val, Nat.cast_ofNat]
    rw [show 2 * Real.pi * (3 / 4) = 2 * Real.pi - Real.pi / 2 by ring,
      Real.cos_two_pi_sub, Real.cos_pi_div_two]
    norm_num
#print axioms Paper7BareCycle.cycle_four_cosines_integer

theorem cycle_six_cosines_integer (k : ZMod 6) :
    ∃ z : ℤ, cycleCosine 6 k = (z : ℝ) := by
  fin_cases k
  · refine ⟨2, ?_⟩
    norm_num [cycleCosine, ZMod.val]
  · refine ⟨1, ?_⟩
    simp only [cycleCosine, ZMod.val, Nat.cast_ofNat, Nat.cast_one]
    rw [show 2 * Real.pi * (1 / 6) = Real.pi / 3 by ring,
      Real.cos_pi_div_three]
    norm_num
  · refine ⟨-1, ?_⟩
    simp only [cycleCosine, ZMod.val, Nat.cast_ofNat]
    rw [show 2 * Real.pi * (2 / 6) = Real.pi - Real.pi / 3 by ring,
      Real.cos_pi_sub, Real.cos_pi_div_three]
    norm_num
  · refine ⟨-2, ?_⟩
    simp only [cycleCosine, ZMod.val, Nat.cast_ofNat]
    rw [show 2 * Real.pi * (3 / 6) = Real.pi by ring, Real.cos_pi]
    norm_num
  · refine ⟨-1, ?_⟩
    simp only [cycleCosine, ZMod.val, Nat.cast_ofNat]
    rw [show 2 * Real.pi * (4 / 6) =
      2 * Real.pi - (Real.pi - Real.pi / 3) by ring,
      Real.cos_two_pi_sub, Real.cos_pi_sub, Real.cos_pi_div_three]
    norm_num
  · refine ⟨1, ?_⟩
    simp only [cycleCosine, ZMod.val, Nat.cast_ofNat]
    rw [show 2 * Real.pi * (5 / 6) = 2 * Real.pi - Real.pi / 3 by ring,
      Real.cos_two_pi_sub, Real.cos_pi_div_three]
    norm_num
#print axioms Paper7BareCycle.cycle_six_cosines_integer

theorem cycleGraph_three_integral : IsIntegralGraph (SimpleGraph.cycleGraph 3) :=
  (cycle_integral_iff_integer_cosines 3 (by norm_num)).mpr cycle_three_cosines_integer
#print axioms Paper7BareCycle.cycleGraph_three_integral

theorem cycleGraph_four_integral : IsIntegralGraph (SimpleGraph.cycleGraph 4) :=
  (cycle_integral_iff_integer_cosines 4 (by norm_num)).mpr cycle_four_cosines_integer
#print axioms Paper7BareCycle.cycleGraph_four_integral

theorem cycleGraph_six_integral : IsIntegralGraph (SimpleGraph.cycleGraph 6) :=
  (cycle_integral_iff_integer_cosines 6 (by norm_num)).mpr cycle_six_cosines_integer
#print axioms Paper7BareCycle.cycleGraph_six_integral

theorem cycleGraph_integral_iff (b : ℕ) (hb : 3 ≤ b) :
    IsIntegralGraph (SimpleGraph.cycleGraph b) ↔ b = 3 ∨ b = 4 ∨ b = 6 := by
  constructor
  · intro hG
    have hsmall : b ≤ 6 := by
      by_contra h
      exact cycleGraph_not_integral_of_seven_le b (by omega) hG
    have hfive : b ≠ 5 := by
      rintro rfl
      exact cycleGraph_five_not_integral hG
    omega
  · rintro (rfl | rfl | rfl)
    · exact cycleGraph_three_integral
    · exact cycleGraph_four_integral
    · exact cycleGraph_six_integral
#print axioms Paper7BareCycle.cycleGraph_integral_iff

end Paper7BareCycle
