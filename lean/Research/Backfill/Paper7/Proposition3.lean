import Research.Backfill.Paper7.OddSpectralSupport
import Research.Backfill.Paper7.DistinctIntegerSquares

/-! The entire original frozen Proposition3, for arbitrary finite graphs. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace Paper7OddIntegral
open BackfillPaper7.Challenge

theorem proposition3_square_bound {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (g : ℕ)
    (hG : IsIntegralGraph G) (hg : IsOddGirth G g) :
    ∑ v ∈ Finset.Icc 2 ((g + 1) / 2), v ^ 2 ≤ 2 * G.edgeFinset.card := by
  have h := distinct_integer_squares_lower (spectralAsymmetry G)
    (fun v hv => (spectralAsymmetry_spec G hG v hv).1) ((g - 1) / 2)
    (spectralAsymmetry_card G g hG hg)
  have hindex : (g - 1) / 2 + 1 = (g + 1) / 2 := by
    have := oddGirth_three_le hg
    omega
  rw [hindex] at h
  have hfinal := h.trans (spectralAsymmetry_square_le G hG)
  exact_mod_cast hfinal
#print axioms Paper7OddIntegral.proposition3_square_bound

theorem check_Proposition3 : BackfillPaper7.Challenge.Proposition3 := by
  intro V _ _ G _ g hG hg
  exact ⟨proposition3_prime_divisibility G g hG hg,
    proposition3_three_divisibility G g hG hg,
    proposition3_asymmetric_values G g hG hg,
    proposition3_square_bound G g hG hg⟩
#print axioms Paper7OddIntegral.check_Proposition3

end Paper7OddIntegral
