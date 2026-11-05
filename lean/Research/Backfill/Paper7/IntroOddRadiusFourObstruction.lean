import Research.Backfill.Paper7.IntroOddCharacteristicAlgebra
import Research.Backfill.Paper7.IntroOddForestRootObstruction

/-! An explicit nonreal root of the radius-four forest factor. The last
statement applies to every finite odd unicyclic graph, with arbitrary branches. -/
set_option autoImplicit false
noncomputable section
open scoped Classical

namespace Paper7IntroOddMultiplicity
open Polynomial BackfillPaper7.Challenge
open BackfillPaper7.Challenge.Legacy.Algebra Paper7IntroOddForest

theorem radiusFourForestFactor_nonreal_root :
    ∃ z : ℂ, 0 < z.im ∧
      (radiusFourForestFactor.map (Int.castRingHom ℂ)).IsRoot z := by
  let t : ℝ := 15 + Real.sqrt 336
  have htpos : 0 < t := by dsimp [t]; positivity
  have hteq : t ^ 2 - 30 * t - 111 = 0 := by
    have hs : (Real.sqrt 336) ^ 2 = 336 := Real.sq_sqrt (by norm_num)
    dsimp [t]
    nlinarith
  let z : ℂ := Complex.I * (Real.sqrt t : ℂ)
  have hzim : z.im = Real.sqrt t := by
    simp only [z, Complex.I_mul_im, Complex.ofReal_re]
  have hzsq : z ^ 2 = -(t : ℂ) := by
    dsimp only [z]
    rw [mul_pow, Complex.I_sq, ← Complex.ofReal_pow, Real.sq_sqrt htpos.le]
    ring
  have htc : (t : ℂ) ^ 2 - 30 * (t : ℂ) - 111 = 0 := by exact_mod_cast hteq
  have hquartic : z ^ 4 + 30 * z ^ 2 - 111 = 0 := by
    calc
      z ^ 4 + 30 * z ^ 2 - 111 = (z ^ 2) ^ 2 + 30 * z ^ 2 - 111 := by ring
      _ = (t : ℂ) ^ 2 - 30 * (t : ℂ) - 111 := by rw [hzsq]; ring
      _ = 0 := htc
  refine ⟨z, ?_, ?_⟩
  · rw [hzim]
    exact Real.sqrt_pos.mpr htpos
  · change (radiusFourForestFactor.map (Int.castRingHom ℂ)).eval z = 0
    simpa [radiusFourForestFactor, Polynomial.eval_map] using hquartic
#print axioms Paper7IntroOddMultiplicity.radiusFourForestFactor_nonreal_root

theorem radiusFourForestFactor_not_dvd_of_real_roots (f : Polynomial ℤ)
    (hf : ∀ z : ℂ, (f.map (Int.castRingHom ℂ)).IsRoot z → z.im = 0) :
    ¬ radiusFourForestFactor ∣ f := by
  intro hdiv
  obtain ⟨q, hq⟩ := hdiv
  obtain ⟨z, hzi, hz⟩ := radiusFourForestFactor_nonreal_root
  have hroot : (f.map (Int.castRingHom ℂ)).IsRoot z := by
    change (f.map (Int.castRingHom ℂ)).eval z = 0
    rw [hq, Polynomial.map_mul, Polynomial.eval_mul, hz.eq_zero, zero_mul]
  exact (ne_of_gt hzi) (hf z hroot)
#print axioms Paper7IntroOddMultiplicity.radiusFourForestFactor_not_dvd_of_real_roots

theorem unicyclic_odd_antipart_not_dvd_radiusFourForestFactor
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (b : ℕ)
    (hG : IsUnicyclicWithCycle G b) (hb : Odd b) :
    ¬ radiusFourForestFactor ∣
      graphPhi G - C ((-1 : ℤ) ^ Fintype.card V) * (graphPhi G).comp (-X) :=
  radiusFourForestFactor_not_dvd_of_real_roots _
    (unicyclic_odd_antipart_root_real G b hG hb)
#print axioms Paper7IntroOddMultiplicity.unicyclic_odd_antipart_not_dvd_radiusFourForestFactor

end Paper7IntroOddMultiplicity
