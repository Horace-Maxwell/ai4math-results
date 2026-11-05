import Research.Backfill.Paper7.SunCycleLengthBounds
import Research.Backfill.Paper7.SunSixAcceptedClassification

/-! NEW SOURCE ONLY. Complete global reductions to the remaining even cycle
branches. No b=4 control, b=8/10/12 exclusion, or final theorem is assumed. -/
set_option autoImplicit false
noncomputable section
namespace Paper7CycleLength
open BackfillPaper7.Challenge

theorem integral_order_le_forty_one_cycle_cases
    (b : ℕ) (L : Fin b → List ℕ) (hb : 3 ≤ b)
    (hp : 0 < pendantCount b L) (hG : IsIntegralGraph (sunGraph b L))
    (hn : order b L ≤ 41) : b = 4 ∨ b = 8 ∨ b = 10 ∨ b = 12 := by
  have hc := integral_order_le_forty_two_cycle_cases b L hb hp hG (by omega)
  have hne : b ≠ 6 := by
    intro heq
    subst b
    have h42 := original_integral_six_order L hp hG (by omega)
    omega
  rcases hc with h4 | h6 | h8 | h10 | h12
  · exact Or.inl h4
  · exact (hne h6).elim
  · exact Or.inr (Or.inl h8)
  · exact Or.inr (Or.inr (Or.inl h10))
  · exact Or.inr (Or.inr (Or.inr h12))
#print axioms Paper7CycleLength.integral_order_le_forty_one_cycle_cases

theorem counterexample_order_le_forty_one_cycle_ten
    (b : ℕ) (L : Fin b → List ℕ) (hC : IsCounterexample b L)
    (hn : order b L ≤ 41) : b = 10 := by
  have hc := counterexample_order_le_forty_two_cycle_cases b L hC (by omega)
  rcases hc with h6 | h10
  · subst b
    have h42 := original_integral_six_order L hC.2.1 hC.2.2.1 (by omega)
    omega
  · exact h10
#print axioms Paper7CycleLength.counterexample_order_le_forty_one_cycle_ten

theorem counterexample_order_le_forty_two_six_or_ten
    (b : ℕ) (L : Fin b → List ℕ) (hC : IsCounterexample b L)
    (hn : order b L ≤ 42) :
    (order b L = 42 ∧ Nonempty (sunGraph b L ≃g sunGraph 6 C61)) ∨ b = 10 := by
  rcases counterexample_order_le_forty_two_cycle_cases b L hC hn with h6 | h10
  · subst b
    exact Or.inl ⟨original_integral_six_order L hC.2.1 hC.2.2.1 hn,
      original_integral_six_iso L hC.2.1 hC.2.2.1 hn⟩
  · exact Or.inr h10
#print axioms Paper7CycleLength.counterexample_order_le_forty_two_six_or_ten

end Paper7CycleLength
