import Research.Backfill.Paper7.CycleCosineSpectrum
import Research.Backfill.Paper7.CycleFrequencyCard

/-! Strict threshold one, including equality frequencies when six divides b. -/
set_option autoImplicit false
noncomputable section
namespace Paper7Lemma41
open BackfillPaper7.Challenge

theorem two_cos_gt_one_first_half (θ : ℝ) (h0 : 0 ≤ θ) (hp : θ ≤ Real.pi) :
    1 < 2 * Real.cos θ ↔ θ < Real.pi / 3 := by
  have hthird : Real.pi / 3 ∈ Set.Icc (0 : ℝ) Real.pi := by
    constructor <;> linarith [Real.pi_pos]
  have hi := Real.strictAntiOn_cos.lt_iff_gt hthird (show θ ∈ Set.Icc 0 Real.pi from ⟨h0,hp⟩)
  rw [Real.cos_pi_div_three] at hi
  constructor
  · intro h
    exact hi.mp (by linarith)
  · intro h
    have hc := hi.mpr h
    linarith
#print axioms Paper7Lemma41.two_cos_gt_one_first_half

theorem two_cos_gt_one_period (θ : ℝ) (h0 : 0 ≤ θ) (hp : θ ≤ 2 * Real.pi) :
    1 < 2 * Real.cos θ ↔ θ < Real.pi / 3 ∨ 2 * Real.pi - θ < Real.pi / 3 := by
  by_cases hh : θ ≤ Real.pi
  · have hn : ¬ 2 * Real.pi - θ < Real.pi / 3 := by linarith [Real.pi_pos]
    rw [or_iff_left hn]
    exact two_cos_gt_one_first_half θ h0 hh
  · have hn : ¬ θ < Real.pi / 3 := by linarith [Real.pi_pos]
    rw [or_iff_right hn]
    have hr0 : 0 ≤ 2 * Real.pi - θ := by linarith
    have hrp : 2 * Real.pi - θ ≤ Real.pi := by linarith
    have h := two_cos_gt_one_first_half (2 * Real.pi - θ) hr0 hrp
    simpa only [Real.cos_two_pi_sub] using h
#print axioms Paper7Lemma41.two_cos_gt_one_period

theorem angle_lt_third_iff (b j : ℕ) (hb : 0 < b) :
    2 * Real.pi * ((j : ℝ) / b) < Real.pi / 3 ↔ 6 * j < b := by
  have hbR : 0 < (b : ℝ) := by exact_mod_cast hb
  rw [show 2 * Real.pi * ((j : ℝ) / b) = (2 * Real.pi * j) / b by ring,
    div_lt_iff₀ hbR]
  constructor
  · intro h
    have hm : Real.pi * (6 * (j : ℝ)) < Real.pi * b := by nlinarith
    have hj := (mul_lt_mul_iff_right₀ Real.pi_pos).mp hm
    exact_mod_cast hj
  · intro h
    have hj : 6 * (j : ℝ) < b := by exact_mod_cast h
    have hm := (mul_lt_mul_iff_right₀ Real.pi_pos).mpr hj
    nlinarith
#print axioms Paper7Lemma41.angle_lt_third_iff

theorem reflected_angle (b j : ℕ) (hb : 0 < b) (hj : j ≤ b) :
    2 * Real.pi - 2 * Real.pi * ((j : ℝ) / b) =
      2 * Real.pi * (((b-j : ℕ) : ℝ) / b) := by
  have hbR : (b : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hb)
  rw [Nat.cast_sub hj]
  field_simp [hbR]
#print axioms Paper7Lemma41.reflected_angle

theorem cycleCosine_gt_one_iff (b : ℕ) [NeZero b] (k : ZMod b) :
    1 < cycleCosine b k ↔ 6 * k.val < b ∨ 6 * (b-k.val) < b := by
  have hb : 0 < b := Nat.pos_of_ne_zero (NeZero.ne b)
  have hbR : 0 < (b : ℝ) := by exact_mod_cast hb
  have hk : k.val < b := ZMod.val_lt k
  have hkR : (k.val : ℝ) ≤ b := by exact_mod_cast hk.le
  have hfrac : (k.val : ℝ) / b ≤ 1 := (div_le_one hbR).mpr hkR
  have hθ0 : 0 ≤ 2 * Real.pi * ((k.val : ℝ) / b) := by positivity
  have hθp : 2 * Real.pi * ((k.val : ℝ) / b) ≤ 2 * Real.pi := by
    nlinarith [Real.pi_pos]
  rw [cycleCosine, two_cos_gt_one_period _ hθ0 hθp,
    reflected_angle b k.val hb hk.le, angle_lt_third_iff b k.val hb,
    angle_lt_third_iff b (b-k.val) hb]
#print axioms Paper7Lemma41.cycleCosine_gt_one_iff

/-- Exactly the first clause of frozen Lemma41, with all cycle frequencies counted. -/
theorem cycle_Ngt_one_exact (b : ℕ) (hb : 3 ≤ b) :
    Ngt (SimpleGraph.cycleGraph b) 1 = 2 * ((b + 5) / 6) - 1 := by
  obtain ⟨n,rfl⟩ : ∃ n, b = n+3 := ⟨b-3, by omega⟩
  rw [cycleGraph_Ngt_one_frequency_count (n+3) hb]
  simp_rw [cycleCosine_gt_one_iff]
  change (Finset.univ.filter (fun k : Fin (n+3) =>
    6*k.val < n+3 ∨ 6*(n+3-k.val) < n+3)).card = _
  exact cycle_frequency_card (n+3) hb
#print axioms Paper7Lemma41.cycle_Ngt_one_exact

end Paper7Lemma41
