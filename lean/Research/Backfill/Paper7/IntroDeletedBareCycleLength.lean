import Research.Backfill.Paper7.IntroDeletedBareCycleIntegral
import Research.Backfill.Paper7.CycleCosineThreshold

/-! The genuine bare-cycle side is reduced to length four or six in the even case. -/
set_option autoImplicit false
noncomputable section
open scoped Classical

namespace Paper7IntroBareSide
open SimpleGraph BackfillPaper7.Challenge Paper7Lemma41 Paper7IntroCutGap

theorem large_cycle_first_cosine_in_unit_gap (b : ℕ) [NeZero b] (hb : 7 ≤ b) :
    1 < cycleCosine b (1 : ZMod b) ∧ cycleCosine b (1 : ZMod b) < 2 := by
  have hval : (1 : ZMod b).val = 1 := ZMod.val_one'' (by omega)
  have hlo : 1 < cycleCosine b (1 : ZMod b) :=
    (cycleCosine_gt_one_iff b 1).mpr (Or.inl (by rw [hval]; omega))
  have hbR : (0 : ℝ) < b := by exact_mod_cast (show 0 < b by omega)
  have hangle := (angle_lt_third_iff b 1 (by omega)).mpr (by omega)
  have hangle' : 2 * Real.pi * ((1 : ℝ) / b) < Real.pi / 3 := by
    simpa only [Nat.cast_one] using hangle
  have hcos : Real.cos (2 * Real.pi * ((1 : ℝ) / b)) < 1 := by
    have h := Real.cos_lt_cos_of_nonneg_of_le_pi (x := 0)
      (y := 2 * Real.pi * ((1 : ℝ) / b)) (by norm_num)
      (by linarith [Real.pi_pos])
      (by positivity)
    simpa only [Real.cos_zero] using h
  refine ⟨hlo, ?_⟩
  unfold cycleCosine
  rw [hval, Nat.cast_one]
  linarith
#print axioms Paper7IntroBareSide.large_cycle_first_cosine_in_unit_gap

theorem integral_deleted_isolated_cycle_length_le_six
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hI : IsIntegralGraph G)
    (v : V) (S : Set {w : V // w ≠ v})
    (hsep : ∀ i ∈ S, ∀ j ∉ S, ¬(vertexDeletedGraph G v).Adj i j)
    (b : ℕ) (hb : 3 ≤ b) (e : (vertexDeletedGraph G v).induce S ≃g cycleGraph b) : b ≤ 6 := by
  by_contra hbig
  have hb7 : 7 ≤ b := by omega
  let : NeZero b := ⟨by omega⟩
  have hx : cycleCosine b (1 : ZMod b) ∈ spec (cycleGraph b) := by
    rw [cycleGraph_spec b hb]
    exact Multiset.mem_map.mpr ⟨1, Finset.mem_univ 1, rfl⟩
  obtain ⟨z, hz⟩ := integral_deleted_isolated_cycle_real_roots_integer G hI v S hsep b hb e
    (cycleCosine b 1) hx
  obtain ⟨hlo, hhi⟩ := large_cycle_first_cosine_in_unit_gap b hb7
  rw [hz] at hlo hhi
  have hloZ : (1 : ℤ) < z := by exact_mod_cast hlo
  have hhiZ : z < (2 : ℤ) := by exact_mod_cast hhi
  omega
#print axioms Paper7IntroBareSide.integral_deleted_isolated_cycle_length_le_six

theorem integral_deleted_isolated_even_cycle_four_or_six
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hI : IsIntegralGraph G)
    (v : V) (S : Set {w : V // w ≠ v})
    (hsep : ∀ i ∈ S, ∀ j ∉ S, ¬(vertexDeletedGraph G v).Adj i j)
    (b : ℕ) (hb : 3 ≤ b) (heven : Even b)
    (e : (vertexDeletedGraph G v).induce S ≃g cycleGraph b) : b = 4 ∨ b = 6 := by
  have hle := integral_deleted_isolated_cycle_length_le_six G hI v S hsep b hb e
  obtain ⟨k, hk⟩ := heven
  omega
#print axioms Paper7IntroBareSide.integral_deleted_isolated_even_cycle_four_or_six

end Paper7IntroBareSide
