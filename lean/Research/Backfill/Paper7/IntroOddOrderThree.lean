import Research.Backfill.Paper7.IntroOddCharacteristicCases
import Research.Backfill.Paper7.IntroOddRadiusFourObstruction
import Research.Backfill.Paper7.UnicyclicBareCycleIso

/-! Full odd-cycle order conclusion in the original arbitrary finite-graph
range. This does not assert the separate even-cycle classification. -/
set_option autoImplicit false
noncomputable section
open scoped Classical

namespace Paper7IntroOddMultiplicity
open SimpleGraph Polynomial BackfillPaper7.Challenge
open BackfillPaper7.Challenge.Legacy.Algebra Paper7IntroOddForest

theorem intro21_odd_card_eq_three
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (b : ℕ)
    (hG : IsUnicyclicWithCycle G b) (hI : IsIntegralGraph G)
    (hn : Fintype.card V ≤ 21) (hb : Odd b) : Fintype.card V = 3 := by
  rcases intro21_odd_characteristic_cases G b hG hI hn hb with hthree | hthree | hfour
  · exact hthree
  · obtain ⟨a, u, v, _ha, _hu, _hv, hnformula, hphi⟩ := hthree
    have hnodiv := unicyclic_odd_antipart_not_dvd_radiusThreeForestFactor G b hG hb
    exfalso
    apply hnodiv
    rw [hnformula, hphi, radiusThreeCharacteristic_antipart]
    refine ⟨-4 * (X ^ a * pairedEvenFactor u v), ?_⟩
    ring
  · obtain ⟨hcard, hphi⟩ := hfour
    have hnodiv := unicyclic_odd_antipart_not_dvd_radiusFourForestFactor G b hG hb
    exfalso
    apply hnodiv
    rw [hcard, hphi, radiusFourCharacteristic_antipart]
    refine ⟨-4 * X ^ 14, ?_⟩
    ring
#print axioms Paper7IntroOddMultiplicity.intro21_odd_card_eq_three

theorem intro21_odd_card_and_cycle_eq_three
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (b : ℕ)
    (hG : IsUnicyclicWithCycle G b) (hI : IsIntegralGraph G)
    (hn : Fintype.card V ≤ 21) (hb : Odd b) : Fintype.card V = 3 ∧ b = 3 :=
  ⟨intro21_odd_card_eq_three G b hG hI hn hb,
    intro21_odd_cycle_eq_three G b hG hI hn hb⟩
#print axioms Paper7IntroOddMultiplicity.intro21_odd_card_and_cycle_eq_three

theorem intro21_odd_iso_cycle_three
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (b : ℕ)
    (hG : IsUnicyclicWithCycle G b) (hI : IsIntegralGraph G)
    (hn : Fintype.card V ≤ 21) (hb : Odd b) :
    Nonempty (G ≃g cycleGraph 3) := by
  obtain ⟨hcard, hcycle⟩ := intro21_odd_card_and_cycle_eq_three G b hG hI hn hb
  have hGthree : IsUnicyclicWithCycle G 3 := hcycle ▸ hG
  exact Paper7UnicyclicStructure.unicyclic_card_eq_cycle_iso G 3 hGthree hcard
#print axioms Paper7IntroOddMultiplicity.intro21_odd_iso_cycle_three

end Paper7IntroOddMultiplicity
