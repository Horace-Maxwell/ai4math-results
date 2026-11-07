import Research.Backfill.Paper2.Challenge
import Research.Backfill.Paper2.Entry389472Mod3
import Research.Backfill.Paper2.EntryA388734
import Research.Backfill.Paper2.EntryA377100
import Research.Backfill.Paper2.EntryA274479
import Research.Backfill.Paper2.EntryA120566
import Research.Backfill.Paper2.EntryA361047

set_option autoImplicit false
namespace BackfillPaper2.EntryTheorems
open PowerSeries BackfillPaper2.Challenge

theorem check_Thm4 : Thm4 :=
  fun A h n hn => Entry389472Mod3.integer_conjecture A h n hn

theorem check_Thm6 : Thm6 := fun A h n => EntryA388734.hanna_a388734 A h n

theorem check_Thm7 : Thm7 := by
  rintro A U h0 h1 ⟨hU, hA⟩ n hn
  exact EntryA377100.hanna_a377100 A U h0 h1 hU hA n hn

private lemma h274479_spec : h274479 * (1 - 2 * X - 4 * X ^ 2) = X ^ 2 := by
  rw [h274479, mul_assoc, mul_comm (PowerSeries.invOfUnit _ _),
    PowerSeries.mul_invOfUnit, mul_one]
  simp

theorem check_Thm8 : Thm8 :=
  fun A h0 h1 hA n hn => EntryA274479.hanna_a274479 A h274479 h0 h1 h274479_spec hA n hn

theorem check_Thm9 : Thm9 :=
  fun A h0 h1 hA n hn => EntryA120566.hanna_a120566 A h0 h1 hA n hn

theorem check_Thm10 : Thm10 := by
  intro A h0 hA m
  refine ⟨?_, ?_⟩
  · rintro ⟨k, rfl⟩
    exact EntryA361047.hanna_a361047_pow A h0 hA k
  · intro hm
    exact Int.modEq_zero_iff_dvd.mpr
      (EntryA361047.hanna_a361047_nonpow A h0 hA m (fun k hk => hm ⟨k, hk⟩))

end BackfillPaper2.EntryTheorems


#print axioms BackfillPaper2.EntryTheorems.check_Thm4
#print axioms BackfillPaper2.EntryTheorems.check_Thm6
#print axioms BackfillPaper2.EntryTheorems.check_Thm7
#print axioms BackfillPaper2.EntryTheorems.check_Thm8
#print axioms BackfillPaper2.EntryTheorems.check_Thm9
#print axioms BackfillPaper2.EntryTheorems.check_Thm10
