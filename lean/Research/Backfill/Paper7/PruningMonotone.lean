import Research.Backfill.Paper7.PruningUnitMono

/-! Exactly conjunct four of the frozen PruningAndEnumerationCompleteness.
This is not a proof of the entire multi-part Pruning contract. -/
set_option autoImplicit false
noncomputable section
namespace Paper7Pruning
open BackfillPaper7.Challenge BackfillPaper7.Challenge.Legacy

theorem lower_bounds_coordinate_mono (b d : ℕ) (x y : PQ b) (hd : d < b)
    (hxy : ∀ i, x.1 i ≤ y.1 i ∧ x.2 i ≤ y.2 i) (m : ℕ) (hm : 1 ≤ m) :
    lowerGT b d x m ≤ lowerGT b d y m ∧ lowerGE b d x m ≤ lowerGE b d y m := by
  by_cases hm1 : m = 1
  · subst m
    refine ⟨lowerGT_one_mono b d x y hd hxy, ?_⟩
    simp only [lowerGE, ite_eq_left (show (1 : ℕ) < 2 by omega), le_refl]
  · have hm2 : 2 ≤ m := by omega
    have h := pathMatrix_inertia_mono b d x y hxy (m : ℝ) (by exact_mod_cast hm2)
    simpa only [lowerGT, lowerGE, ite_eq_right hm1, ite_eq_right (by omega : ¬m < 2)] using h
#print axioms Paper7Pruning.lower_bounds_coordinate_mono

theorem amonotone_downward (b N d : ℕ) (_hb : 3 ≤ b) (hd : d < b) (_hN : N ≤ 49)
    (x y : PQ b) (hxy : ∀ i, x.1 i ≤ y.1 i ∧ x.2 i ≤ y.2 i)
    (cyc cnt : Bool) (hy : AMonotonePass cyc cnt b N d y) :
    AMonotonePass cyc cnt b N d x := by
  obtain ⟨s, hA, hw, hl, hspec, hc⟩ := hy
  have hwindow := windowLo_coordinate_mono b d x y hxy
  have hsum := prefix_sums_mono b d x y hxy
  have hpZ : (pSum («prefix» d x) : ℤ) ≤ pSum («prefix» d y) := by exact_mod_cast hsum.1
  have hqZ : (qSum («prefix» d x) : ℤ) ≤ qSum («prefix» d y) := by exact_mod_cast hsum.2.1
  refine ⟨s, hA, ?_, ?_, ?_, ?_⟩
  · by_cases he : Even b
    · simp only [ite_eq_left he] at hw ⊢
      exact hwindow.trans hw
    · simp only [ite_eq_right he] at hw ⊢
      omega
  · by_cases he : Even b
    · simp only [ite_eq_left he] at hl ⊢
      omega
    · simp only [ite_eq_right he] at hl ⊢
      omega
  · intro m hm1 hm9
    have hm := lower_bounds_coordinate_mono b d x y hd hxy m hm1
    exact ⟨hm.1.trans (hspec m hm1 hm9).1, hm.2.trans (hspec m hm1 hm9).2⟩
  · intro hcnt he
    exact partialCountPass_downward b N d x y s hxy (hc hcnt he)
#print axioms Paper7Pruning.amonotone_downward

end Paper7Pruning
