import Research.Backfill.Paper1.SupplementStatements

set_option autoImplicit false
noncomputable section
namespace CodexPaper1
open BackfillPaper1

theorem check_ParameterRegions : NarrowSupplement.ParameterRegions := by
  refine ⟨?_, ?_, ?_⟩
  · intro p q hpq
    obtain ⟨hp, hq, hne, hpo, hqo⟩ := hpq
    have hp3 : 3 ≤ p := hp.odd_iff.mp hpo
    have hq3 : 3 ≤ q := hq.odd_iff.mp hqo
    have hp35 : p = 3 ∨ 5 ≤ p := by obtain ⟨k, hk⟩ := hpo; omega
    have hq35 : q = 3 ∨ 5 ≤ q := by obtain ⟨k, hk⟩ := hqo; omega
    constructor
    · rcases hp35 with hpEq | hp5
      · have hq5 : 5 ≤ q := by
          rcases hq35 with hqEq | hq5
          · exact False.elim (hne (hpEq.trans hqEq.symm))
          · exact hq5
        exact Or.inr ⟨by exact_mod_cast hpEq, by exact_mod_cast hq5⟩
      · exact Or.inl ⟨by exact_mod_cast hp5, by exact_mod_cast hq3⟩
    · rcases hq35 with hqEq | hq5
      · have hp5 : 5 ≤ p := by
          rcases hp35 with hpEq | hp5
          · exact False.elim (hne (hpEq.trans hqEq.symm))
          · exact hp5
        refine Or.inr ⟨by exact_mod_cast hqEq, ?_⟩
        have h : (5 : ℝ) ≤ p := by exact_mod_cast hp5
        linarith
      · refine Or.inl ⟨by exact_mod_cast hq5, ?_⟩
        have h : (3 : ℝ) ≤ p := by exact_mod_cast hp3
        linarith
  · intro x R h
    rcases h with ⟨hx, hR⟩ | ⟨rfl, hR⟩
    · nlinarith [mul_nonneg (sub_nonneg.mpr hx) (show 0 ≤ R - 1 by linarith)]
    · linarith
  · intro p q h
    rcases h with ⟨hp, hq⟩ | ⟨rfl, hq⟩
    · refine ⟨Or.inl ⟨by linarith, by linarith⟩, by linarith, ?_⟩
      nlinarith [mul_nonneg (sub_nonneg.mpr hp) (sub_nonneg.mpr hq)]
    · refine ⟨Or.inr ⟨by norm_num, by linarith⟩, by linarith, ?_⟩
      nlinarith

theorem check_MultiplicativeMaxComparison : NarrowSupplement.MultiplicativeMaxComparison := by
  intro p q a b _hpq _ha _hb V W S hmax hmult
  obtain ⟨D, hD, _hMultD, hE⟩ := hmult.1
  rw [← hE]
  exact (hmax.2 D hD).1

#print axioms check_ParameterRegions
#print axioms check_MultiplicativeMaxComparison
end CodexPaper1
