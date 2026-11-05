import Research.Backfill.Paper7.IntroIntegerCharacteristicProduct
import Research.Backfill.Paper7.IntroOddMultiplicityCases
import Research.Backfill.Paper7.IntroOddCharacteristicAlgebra

/-! Characteristic-polynomial alternatives derived from the actual graph.
All three free natural exponents in the middle alternative are actual counts. -/
set_option autoImplicit false
noncomputable section
open scoped Classical

namespace Paper7IntroOddMultiplicity
open Polynomial BackfillPaper7.Challenge
open BackfillPaper7.Challenge.Legacy.Algebra Paper7OddIntegral

theorem intro21_odd_characteristic_cases
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (b : ℕ)
    (hG : IsUnicyclicWithCycle G b) (hI : IsIntegralGraph G)
    (hn : Fintype.card V ≤ 21) (hb : Odd b) :
    Fintype.card V = 3 ∨
    (∃ a u v : ℕ, a = (integerSpectrum G).count 0 ∧
      u = (integerSpectrum G).count (-1) ∧ v = (integerSpectrum G).count 2 ∧
      Fintype.card V = a + 2 * u + 2 * v + 7 ∧
      graphPhi G = radiusThreeCharacteristic a u v) ∨
    (Fintype.card V = 21 ∧ graphPhi G = radiusFourCharacteristic) := by
  rcases intro21_odd_actual_multiplicity_cases G b hG hI hn hb with hthree | hrad | hrad
  · exact Or.inl hthree
  · obtain ⟨hp3, hm3, hp4, hm4, hd2, hd1⟩ := hrad
    have hm2 : (integerSpectrum G).count (-2) = (integerSpectrum G).count 2 + 3 := by
      dsimp only [signedIntegerMultiplicity] at hd2
      omega
    have hp1 : (integerSpectrum G).count 1 = (integerSpectrum G).count (-1) + 3 := by
      dsimp only [signedIntegerMultiplicity] at hd1
      omega
    have htotal := intro21_multiplicity_total G b hG hI hn
    dsimp only [pairedIntegerMultiplicity] at htotal
    rw [hp3, hm3, hp4, hm4, hm2, hp1] at htotal
    refine Or.inr (Or.inl ⟨(integerSpectrum G).count 0,
      (integerSpectrum G).count (-1), (integerSpectrum G).count 2,
      rfl, rfl, rfl, ?_, ?_⟩)
    · omega
    · rw [intro21_graphPhi_nine_factors G b hG hI hn,
        hp3, hm3, hp4, hm4, hm2, hp1]
      simp only [pow_zero, pow_one, one_mul, mul_one]
      unfold radiusThreeCharacteristic pairedEvenFactor radiusThreeCore
      have hq1 : (X ^ 2 - 1 : Polynomial ℤ) = (X - 1) * (X + 1) := by ring
      have hq2 : (X ^ 2 - 4 : Polynomial ℤ) = (X - 2) * (X + 2) := by ring
      rw [hq1, hq2]
      simp only [pow_add, mul_pow]
      ring
  · obtain ⟨hcard, hp4, hm4, hp3, hm3, hp2, hm2, hp1, hm1, hzero⟩ := hrad
    refine Or.inr (Or.inr ⟨hcard, ?_⟩)
    rw [intro21_graphPhi_nine_factors G b hG hI hn,
      hp4, hm4, hp3, hm3, hp2, hm2, hp1, hm1, hzero]
    simp only [pow_zero, pow_one, one_mul, mul_one]
    unfold radiusFourCharacteristic radiusFourCore
    ring
#print axioms Paper7IntroOddMultiplicity.intro21_odd_characteristic_cases

end Paper7IntroOddMultiplicity
