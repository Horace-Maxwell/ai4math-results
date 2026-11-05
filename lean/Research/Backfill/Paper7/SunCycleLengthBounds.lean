import Research.Backfill.Paper7.Corollary31
import Research.Backfill.Paper7.SunSchwenkCycleData
import Research.Backfill.Paper7.Section6CycleThree
import Research.Backfill.Paper7.Lemma44

/-! NEW SOURCE ONLY. Global cycle-length reductions for the original arbitrary
pendant lists. All mathematical inputs are accepted contracts or their proved
helper chain. This module does not classify any remaining even cycle length. -/
set_option autoImplicit false
noncomputable section
namespace Paper7CycleLength
open BackfillPaper7.Challenge
open scoped BigOperators Classical

theorem integral_order_le_forty_two_even (b : ℕ) (L : Fin b → List ℕ)
    (hb : 3 ≤ b) (hp : 0 < pendantCount b L)
    (hG : IsIntegralGraph (sunGraph b L)) (hn : order b L ≤ 42) : Even b := by
  rcases Nat.even_or_odd b with he | ho
  · exact he
  · exfalso
    by_cases hthree : b = 3
    · subst b
      have h50 := Paper7CycleThree.check_Section6CycleThree L hp hG
      omega
    · have h31 := Paper7Corollary31.check_Corollary31.1
        (SunV b L) (sunGraph b L) b hG
        (Paper7SunSchwenk.sun_unicyclic b L hb) ho
      have h102 := (h31.2.2 hthree).2
      change 102 ≤ order b L at h102
      omega
#print axioms Paper7CycleLength.integral_order_le_forty_two_even

theorem integral_order_le_forty_two_cycle_le_thirteen
    (b : ℕ) (L : Fin b → List ℕ) (hb : 3 ≤ b)
    (hp : 0 < pendantCount b L) (hG : IsIntegralGraph (sunGraph b L))
    (hn : order b L ≤ 42) : b ≤ 13 := by
  obtain ⟨p, q, hI, hsize, hpos⟩ :=
    Paper7CycleThree.integral_normalization b L hb hp hG
  have hn' : nOf b p q ≤ 42 := by omega
  exact (Paper7Rank.check_Lemma44 b p q hb hpos hI).2.2.2.2.2 hn'
#print axioms Paper7CycleLength.integral_order_le_forty_two_cycle_le_thirteen

theorem integral_order_le_forty_two_cycle_cases
    (b : ℕ) (L : Fin b → List ℕ) (hb : 3 ≤ b)
    (hp : 0 < pendantCount b L) (hG : IsIntegralGraph (sunGraph b L))
    (hn : order b L ≤ 42) : b = 4 ∨ b = 6 ∨ b = 8 ∨ b = 10 ∨ b = 12 := by
  have h13 := integral_order_le_forty_two_cycle_le_thirteen b L hb hp hG hn
  obtain ⟨k, hk⟩ := integral_order_le_forty_two_even b L hb hp hG hn
  omega
#print axioms Paper7CycleLength.integral_order_le_forty_two_cycle_cases

theorem counterexample_order_le_forty_two_cycle_cases
    (b : ℕ) (L : Fin b → List ℕ) (hC : IsCounterexample b L)
    (hn : order b L ≤ 42) : b = 6 ∨ b = 10 := by
  obtain ⟨hb, hp, hG, hfour⟩ := hC
  rcases integral_order_le_forty_two_cycle_cases b L hb hp hG hn with
    h4 | h6 | h8 | h10 | h12
  · subst b
    exact (hfour (by norm_num)).elim
  · exact Or.inl h6
  · subst b
    exact (hfour (by norm_num)).elim
  · exact Or.inr h10
  · subst b
    exact (hfour (by norm_num)).elim
#print axioms Paper7CycleLength.counterexample_order_le_forty_two_cycle_cases

end Paper7CycleLength
