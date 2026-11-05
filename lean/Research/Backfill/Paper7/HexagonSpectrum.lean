import Research.Backfill.Paper7.HexagonPolynomial
import Research.Backfill.Paper7.VerasSquares

set_option autoImplicit false
set_option maxRecDepth 4096

noncomputable section

namespace Paper7Hexagon

open Polynomial BackfillPaper7.Challenge BackfillPaper7.Challenge.Legacy.Algebra

def hexagonRootList (a : ℕ) (r t : ℤ) : List ℤ :=
  List.replicate (6 * a - 4) 0 ++
    [r, r, -r, -r, r + 1, r + 1, -(r + 1), -(r + 1), t, -t]
#print axioms Paper7Hexagon.hexagonRootList

theorem hexagon_root_product (a : ℕ) (r t : ℤ) :
    ((hexagonRootList a r t).map (fun z => X - C z)).prod =
      X ^ (6 * a - 4) * (X ^ 2 - C (t ^ 2)) *
        ((X ^ 2 - C (r * (r + 1))) ^ 2 - X ^ 2) ^ 2 := by
  simp only [hexagonRootList, List.map_append, List.prod_append, List.map_replicate,
    List.prod_replicate, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    map_zero, sub_zero, map_neg, map_pow, map_add, map_mul, map_one]
  ring
#print axioms Paper7Hexagon.hexagon_root_product

/-- An explicit full factor list proves integrality of the original graph. -/
theorem hexagon_integral_of_parameters (a : ℕ) (ha : 1 ≤ a) (r t : ℤ)
    (hr : r * (r + 1) = (a : ℤ)) (ht : t ^ 2 = 2 * (a : ℤ) + 4) :
    IsIntegralGraph (sunGraph 6 (HexagonFamily a)) := by
  classical
  have hf : graphPhi (sunGraph 6 (HexagonFamily a)) =
      ((hexagonRootList a r t).map (fun z => X - C z)).prod := by
    rw [hexagon_graphPhi a ha, hexagon_root_product, hr, ht]
  apply (Paper7Spectrum.integral_iff_integerFactorization _).mpr
  exact ⟨(hexagonRootList a r t).toFinset, hexagonRootList a r t,
    fun z hz => List.mem_toFinset.mpr hz, hf⟩
#print axioms Paper7Hexagon.hexagon_integral_of_parameters

/-- Necessity uses an actual characteristic factor, not a selected sample
of possible roots or a sufficient Pell condition. -/
theorem hexagon_necessary_square (a : ℕ) (ha : 1 ≤ a)
    (hG : IsIntegralGraph (sunGraph 6 (HexagonFamily a))) :
    ∃ t : ℤ, t ^ 2 = 2 * (a : ℤ) + 4 := by
  have hdiv : (X ^ 2 - C ((2 * a + 4 : ℕ) : ℤ) : Polynomial ℤ) ∣
      graphPhi (sunGraph 6 (HexagonFamily a)) := by
    rw [hexagon_graphPhi a ha]
    refine ⟨X ^ (6 * a - 4) * ((X ^ 2 - C (a : ℤ)) ^ 2 - X ^ 2) ^ 2, ?_⟩
    norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
    ring
  obtain ⟨t, ht⟩ := Paper7Veras.integer_square_of_quadratic_dvd _ (2 * a + 4) hG hdiv
  exact ⟨t, by simpa using ht⟩
#print axioms Paper7Hexagon.hexagon_necessary_square

theorem hexagon_parameter_minimum (a : ℕ) (ha : 1 ≤ a) (t : ℤ)
    (ht : t ^ 2 = 2 * (a : ℤ) + 4) : 6 ≤ a := by
  by_contra h
  have ha' : (a : ℤ) < 6 := by exact_mod_cast (show a < 6 by omega)
  have htLower : -3 ≤ t := by
    by_contra hh
    have hbad : t ≤ -4 := by omega
    nlinarith [sq_nonneg (t + 4)]
  have htUpper : t ≤ 3 := by
    by_contra hh
    have hbad : 4 ≤ t := by omega
    nlinarith [sq_nonneg (t - 4)]
  interval_cases t <;> norm_num at ht <;> omega
#print axioms Paper7Hexagon.hexagon_parameter_minimum

theorem hexagon_order_minimum (a : ℕ) (ha : 1 ≤ a)
    (hG : IsIntegralGraph (sunGraph 6 (HexagonFamily a))) :
    42 ≤ order 6 (HexagonFamily a) := by
  obtain ⟨t, ht⟩ := hexagon_necessary_square a ha hG
  have hmin := hexagon_parameter_minimum a ha t ht
  rw [hexagon_order]
  omega
#print axioms Paper7Hexagon.hexagon_order_minimum

theorem hexagon_counterexample_of_integral (a : ℕ) (ha : 1 ≤ a)
    (hG : IsIntegralGraph (sunGraph 6 (HexagonFamily a))) :
    IsCounterexample 6 (HexagonFamily a) := by
  refine ⟨by decide, ?_, hG, by decide⟩
  rw [hexagon_pendant_count]
  omega
#print axioms Paper7Hexagon.hexagon_counterexample_of_integral

theorem hexagon_six_integral : IsIntegralGraph (sunGraph 6 (HexagonFamily 6)) := by
  exact hexagon_integral_of_parameters 6 (by decide) 2 4 (by norm_num) (by norm_num)
#print axioms Paper7Hexagon.hexagon_six_integral

theorem hexagon_six_counterexample : IsCounterexample 6 (HexagonFamily 6) :=
  hexagon_counterexample_of_integral 6 (by decide) hexagon_six_integral
#print axioms Paper7Hexagon.hexagon_six_counterexample

end Paper7Hexagon
