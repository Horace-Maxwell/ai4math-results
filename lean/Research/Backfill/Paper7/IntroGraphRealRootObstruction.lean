import Research.Backfill.Paper7.SpectrumGraphBasics

/-! A universal real-root obstruction for characteristic polynomials of finite
simple graphs. The quartic obstruction is proved by an explicit nonreal root;
no graph spectrum profile is supplied as a premise. -/
set_option autoImplicit false
noncomputable section
open scoped Classical

namespace Paper7IntroOddForest
open SimpleGraph Polynomial BackfillPaper7.Challenge.Legacy.Algebra

theorem graphPhi_complex_root_real {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (z : ℂ)
    (hz : ((graphPhi G).map (Int.castRingHom ℂ)).IsRoot z) : z.im = 0 := by
  have hA := G.isHermitian_adjMatrix ℂ
  have hroot : (G.adjMatrix ℂ).charpoly.IsRoot z := by
    rwa [Paper7Spectrum.graphPhi_map G ℂ] at hz
  have hmem := (Polynomial.mem_roots (G.adjMatrix ℂ).charpoly_monic.ne_zero).mpr hroot
  rw [hA.roots_charpoly_eq_eigenvalues] at hmem
  obtain ⟨i, _hi, he⟩ := Multiset.mem_map.mp hmem
  change (hA.eigenvalues i : ℂ) = z at he
  rw [← he]
  exact Complex.ofReal_im _
#print axioms Paper7IntroOddForest.graphPhi_complex_root_real

theorem graphPhi_nonreal_eval_ne_zero {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (z : ℂ) (hz : z.im ≠ 0) :
    ((graphPhi G).map (Int.castRingHom ℂ)).eval z ≠ 0 := by
  intro h
  exact hz (graphPhi_complex_root_real G z h)
#print axioms Paper7IntroOddForest.graphPhi_nonreal_eval_ne_zero

def radiusThreeForestFactor : Polynomial ℤ := X ^ 4 + 3 * X ^ 2 - 12
#print axioms Paper7IntroOddForest.radiusThreeForestFactor

theorem radiusThreeForestFactor_nonreal_root :
    ∃ z : ℂ, 0 < z.im ∧
      (radiusThreeForestFactor.map (Int.castRingHom ℂ)).IsRoot z := by
  let t : ℝ := (3 + Real.sqrt 57) / 2
  have htpos : 0 < t := by dsimp [t]; positivity
  have hteq : t ^ 2 - 3 * t - 12 = 0 := by
    have hs : (Real.sqrt 57) ^ 2 = 57 := Real.sq_sqrt (by norm_num)
    dsimp [t]
    nlinarith
  let z : ℂ := Complex.I * (Real.sqrt t : ℂ)
  have hzim : z.im = Real.sqrt t := by
    simp only [z, Complex.I_mul_im, Complex.ofReal_re]
  have hzsq : z ^ 2 = -(t : ℂ) := by
    dsimp only [z]
    rw [mul_pow, Complex.I_sq, ← Complex.ofReal_pow, Real.sq_sqrt htpos.le]
    ring
  have htc : (t : ℂ) ^ 2 - 3 * (t : ℂ) - 12 = 0 := by exact_mod_cast hteq
  have hquartic : z ^ 4 + 3 * z ^ 2 - 12 = 0 := by
    calc
      z ^ 4 + 3 * z ^ 2 - 12 = (z ^ 2) ^ 2 + 3 * z ^ 2 - 12 := by ring
      _ = (t : ℂ) ^ 2 - 3 * (t : ℂ) - 12 := by rw [hzsq]; ring
      _ = 0 := htc
  refine ⟨z, ?_, ?_⟩
  · rw [hzim]
    exact Real.sqrt_pos.mpr htpos
  · change (radiusThreeForestFactor.map (Int.castRingHom ℂ)).eval z = 0
    simpa [radiusThreeForestFactor, Polynomial.eval_map] using hquartic
#print axioms Paper7IntroOddForest.radiusThreeForestFactor_nonreal_root

theorem radiusThreeForestFactor_not_dvd_of_real_roots (f : Polynomial ℤ)
    (hf : ∀ z : ℂ, (f.map (Int.castRingHom ℂ)).IsRoot z → z.im = 0) :
    ¬ radiusThreeForestFactor ∣ f := by
  intro hdiv
  obtain ⟨q, hq⟩ := hdiv
  obtain ⟨z, hzi, hz⟩ := radiusThreeForestFactor_nonreal_root
  have hroot : (f.map (Int.castRingHom ℂ)).IsRoot z := by
    change (f.map (Int.castRingHom ℂ)).eval z = 0
    rw [hq, Polynomial.map_mul, Polynomial.eval_mul, hz.eq_zero, zero_mul]
  exact (ne_of_gt hzi) (hf z hroot)
#print axioms Paper7IntroOddForest.radiusThreeForestFactor_not_dvd_of_real_roots

theorem graphPhi_not_dvd_radiusThreeForestFactor
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    ¬ radiusThreeForestFactor ∣ graphPhi G :=
  radiusThreeForestFactor_not_dvd_of_real_roots (graphPhi G)
    (graphPhi_complex_root_real G)
#print axioms Paper7IntroOddForest.graphPhi_not_dvd_radiusThreeForestFactor

end Paper7IntroOddForest
