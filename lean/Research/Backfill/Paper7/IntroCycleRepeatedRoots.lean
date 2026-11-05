import Research.Backfill.Paper7.CycleCosineSpectrum

/-! Noninteger cycle roots occur at two distinct actual Fourier frequencies. -/
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators

namespace Paper7IntroBareSide
open BackfillPaper7.Challenge Paper7Lemma41

theorem cycleCosine_neg_eq (b : ℕ) [NeZero b] (k : ZMod b) :
    cycleCosine b (-k) = cycleCosine b k := by
  apply Complex.ofReal_injective
  rw [← character_pair_eq_cycleCosine b (-k), ← character_pair_eq_cycleCosine b k]
  simp only [neg_neg, add_comm]
#print axioms Paper7IntroBareSide.cycleCosine_neg_eq

theorem cycleCosine_of_eq_neg (b : ℕ) [NeZero b] (k : ZMod b) (hk : k = -k) :
    cycleCosine b k = 2 ∨ cycleCosine b k = -2 := by
  have hzero : k + k = 0 := by
    calc
      k + k = k + (-k) := congrArg (fun j => k + j) hk
      _ = 0 := add_neg_cancel k
  have hchar : ZMod.stdAddChar k * ZMod.stdAddChar k = (1 : ℂ) := by
    rw [← AddChar.map_add_eq_mul, hzero, AddChar.map_zero_eq_one]
  have hpair := character_pair_eq_cycleCosine b k
  rw [← hk] at hpair
  rcases mul_self_eq_one_iff.mp hchar with hpos | hneg
  · have hval : (cycleCosine b k : ℂ) = 2 := by
      calc
        _ = ZMod.stdAddChar k + ZMod.stdAddChar k := hpair.symm
        _ = 2 := by rw [hpos]; norm_num
    exact Or.inl (by exact_mod_cast hval)
  · have hval : (cycleCosine b k : ℂ) = -2 := by
      calc
        _ = ZMod.stdAddChar k + ZMod.stdAddChar k := hpair.symm
        _ = -2 := by rw [hneg]; norm_num
    exact Or.inr (by exact_mod_cast hval)
#print axioms Paper7IntroBareSide.cycleCosine_of_eq_neg

theorem cycle_noninteger_root_count_ge_two
    (b : ℕ) [NeZero b] (hb : 3 ≤ b) (x : ℝ)
    (hx : x ∈ spec (SimpleGraph.cycleGraph b))
    (hn : ¬∃ z : ℤ, x = (z : ℝ)) :
    2 ≤ (spec (SimpleGraph.cycleGraph b)).count x := by
  rw [cycleGraph_spec b hb] at hx ⊢
  obtain ⟨k, _hk, rfl⟩ := Multiset.mem_map.mp hx
  have hne : k ≠ -k := by
    intro hk
    rcases cycleCosine_of_eq_neg b k hk with hpos | hneg
    · exact hn ⟨2, by simpa using hpos⟩
    · exact hn ⟨-2, by simpa using hneg⟩
  rw [Multiset.count_map]
  change 2 ≤ (Finset.univ.filter (fun j : ZMod b => cycleCosine b k = cycleCosine b j)).card
  calc
    2 = ({k, -k} : Finset (ZMod b)).card := (Finset.card_pair hne).symm
    _ ≤ _ := Finset.card_le_card (by
      intro j hj
      simp only [Finset.mem_insert, Finset.mem_singleton] at hj
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      rcases hj with rfl | rfl
      · rfl
      · exact (cycleCosine_neg_eq b k).symm)
#print axioms Paper7IntroBareSide.cycle_noninteger_root_count_ge_two

end Paper7IntroBareSide
