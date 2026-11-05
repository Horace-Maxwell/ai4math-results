import Research.Backfill.Paper7.IntegralThresholdOne
import Research.Backfill.Paper7.CycleCosineThreshold
import Research.Backfill.Paper7.Lemma24SmallEven

/-! Complete source-only candidate for frozen Lemma41. Lemma24SmallEven is
an explicitly listed uncompiled dependency candidate with its own proof bodies,
not an assumed main contract. No additional hypothesis is added to this check. -/
set_option autoImplicit false
namespace Paper7Lemma41
open BackfillPaper7.Challenge

theorem check_Lemma41 : BackfillPaper7.Challenge.Lemma41 := by
  intro b p q hb
  have hinter := lemma41_interlacing b p q hb
  refine ⟨cycle_Ngt_one_exact b hb, hinter.1, hinter.2, ?_⟩
  intro hG _hpend
  have hlower : 2 * ((b + 5) / 6) - 1 ≤ (Bplus (SG b p q)).card := by
    rw [← cycle_Ngt_one_exact b hb]
    exact cycle_count_le_integral_Bplus b p q hb hG
  refine ⟨hlower, ?_, ?_⟩
  · intro he
    have hc := Paper7Admissible.lemma24_small_even_counts b p q hb hG he
    refine ⟨?_, ?_, ?_⟩
    · intro hn
      exact cycle_length_le_twelve_of_count b _ hb hlower (hc.1 hn)
    · intro hn
      exact cycle_length_le_eighteen_of_count b _ hb hlower (hc.2 hn).1
    · intro hn hbcase
      apply (hc.2 hn).2
      exact count_eq_five_at_fourteen_sixteen_eighteen b _ hbcase hlower (hc.2 hn).1
  · intro hn hmod
    have he : Even b := Nat.even_iff.mpr (by omega)
    have hc := Paper7Admissible.lemma24_small_even_counts b p q hb hG he
    have hbound := cycle_length_le_eighteen_of_count b _ hb hlower (hc.2 hn).1
    exact mod_four_two_cycle_cases b hb hbound hmod
#print axioms Paper7Lemma41.check_Lemma41

end Paper7Lemma41
