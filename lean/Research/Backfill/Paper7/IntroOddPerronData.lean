import Research.Backfill.Paper7.IntroOddSignedMoments
import Research.Backfill.Paper7.OddPerronBoundary

/-! Actual Perron data in the original odd unicyclic order-21 range.
The radius alternatives and signed endpoint counts are derived, not assumed. -/
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators Matrix

namespace Paper7IntroOddMultiplicity
open Matrix BackfillPaper7.Challenge Paper7OddIntegral Paper7Unicyclic
open Paper7Admissible Paper7IntroGeneral

theorem adjacency_quadratic_ones {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    (G.adjMatrix ℝ).toQuadraticForm' (fun _ : V => 1) =
      2 * (G.edgeFinset.card : ℝ) := by
  calc
    _ = ∑ v : V, (G.degree v : ℝ) := by
      simp only [Paper7Inertia.quadratic_apply, dotProduct,
        SimpleGraph.adjMatrix_mulVec_apply, one_mul, Finset.sum_const,
        nsmul_eq_mul, SimpleGraph.card_neighborFinset_eq_degree, mul_one]
    _ = 2 * (G.edgeFinset.card : ℝ) := by
      exact_mod_cast G.sum_degrees_eq_twice_card_edges
#print axioms Paper7IntroOddMultiplicity.adjacency_quadratic_ones

theorem intro21_odd_perron_integer_data
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (b : ℕ)
    (hG : IsUnicyclicWithCycle G b) (hI : IsIntegralGraph G)
    (hn : Fintype.card V ≤ 21) (hb : Odd b) :
    ∃ R : ℤ, (R = 2 ∨ R = 3 ∨ R = 4) ∧
      (integerSpectrum G).count R = 1 ∧ (integerSpectrum G).count (-R) = 0 ∧
      ∀ z ∈ integerSpectrum G, |z| ≤ R := by
  let : Nonempty V := hG.1.nonempty
  obtain ⟨r, hr, v, hv, _hvnorm, hve, hr0, hsimple, hupper, hdom⟩ :=
    connected_perron G hG.1
  have hu := hupper (fun _ : V => 1)
  have honenorm : (fun _ : V => (1 : ℝ)) ⬝ᵥ (fun _ : V => (1 : ℝ)) =
      (Fintype.card V : ℝ) := by simp [dotProduct]
  rw [adjacency_quadratic_ones, unicyclic_card_edges G hG, honenorm] at hu
  have hnpos : 0 < (Fintype.card V : ℝ) := by
    have hthree := unicyclic_card_ge_three G hG
    exact_mod_cast (show 0 < Fintype.card V by omega)
  have hr2 : 2 ≤ r := (mul_le_mul_iff_left₀ hnpos).mp hu
  obtain ⟨R, hR, _hlo, hhi⟩ := integral_unicyclic21_spectrum_window G hG hI hn r hr
  have hR2 : (2 : ℤ) ≤ R := by
    rw [hR] at hr2
    exact_mod_cast hr2
  have hcases : R = 2 ∨ R = 3 ∨ R = 4 := by omega
  obtain ⟨s, ⟨u, w, _hw, hlen, _hedges⟩, _huniq⟩ := hG.2
  have hodd : Odd w.length := hlen.symm ▸ hb
  have hneg := odd_closed_walk_excludes_negative_perron G hG.1 r hr0 v hv hve u w hodd
  refine ⟨R, hcases, ?_, ?_, ?_⟩
  · rw [integerSpectrum_count G hI]
    simpa only [hR] using hsimple
  · rw [integerSpectrum_count G hI, Int.cast_neg]
    exact Multiset.count_eq_zero.mpr (by simpa only [hR] using hneg)
  · intro z hz
    have hzr : (z : ℝ) ∈ spec G := by
      rw [← integerSpectrum_cast G hI]
      exact Multiset.mem_map.mpr ⟨z, hz, rfl⟩
    have hd := hdom z hzr
    rw [hR] at hd
    exact_mod_cast hd
#print axioms Paper7IntroOddMultiplicity.intro21_odd_perron_integer_data

theorem integerSpectrum_count_zero_above_bound
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (R z : ℤ)
    (hbound : ∀ x ∈ integerSpectrum G, |x| ≤ R) (hz : R < |z|) :
    (integerSpectrum G).count z = 0 := by
  exact Multiset.count_eq_zero.mpr (fun h => (not_le_of_gt hz) (hbound z h))
#print axioms Paper7IntroOddMultiplicity.integerSpectrum_count_zero_above_bound

end Paper7IntroOddMultiplicity
