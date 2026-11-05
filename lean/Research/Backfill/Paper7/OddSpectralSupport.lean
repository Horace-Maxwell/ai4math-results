import Research.Backfill.Paper7.OddPrimeDivisibility
import Research.Backfill.Paper7.OddMultisetPairing
import Research.Backfill.Paper7.OddMomentVandermonde

/-! The graph support consists of actual unequal signed spectral multiplicities. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace Paper7OddIntegral
open BackfillPaper7.Challenge

variable {V : Type} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

def spectralAsymmetry : Finset ℤ := asymmetricSupport (integerSpectrum G)
#print axioms Paper7OddIntegral.spectralAsymmetry

def signedMultiplicity (z : ℤ) : ℝ :=
  ((integerSpectrum G).count z : ℝ) - ((integerSpectrum G).count (-z) : ℝ)
#print axioms Paper7OddIntegral.signedMultiplicity

theorem spectralAsymmetry_spec (hG : IsIntegralGraph G) (z : ℤ)
    (hz : z ∈ spectralAsymmetry G) :
    2 ≤ z ∧ mult G (z : ℝ) ≠ mult G (-(z : ℝ)) := by
  have h := Finset.mem_filter.mp hz
  refine ⟨(Finset.mem_filter.mp h.1).2, ?_⟩
  have hn := h.2
  rw [integerSpectrum_count G hG z, integerSpectrum_count G hG (-z),
    Int.cast_neg] at hn
  exact hn
#print axioms Paper7OddIntegral.spectralAsymmetry_spec

theorem odd_spectral_support_moment (hG : IsIntegralGraph G) (L : ℕ) (hL : Odd L) :
    (∑ z ∈ spectralAsymmetry G, signedMultiplicity G z * ((z : ℝ) ^ L - z)) =
      (((G.adjMatrix ℤ) ^ L).trace : ℝ) := by
  let F : ℤ → ℝ := fun z => (z : ℝ) ^ L - z
  have hL0 : L ≠ 0 := by
    intro h
    subst L
    norm_num at hL
  have hodd (z : ℤ) : F (-z) = -F z := by
    dsimp only [F]
    rw [Int.cast_neg, hL.neg_pow]
    ring
  have hsmall (z : ℤ) (hz : ¬ 2 ≤ |z|) : F z = 0 := by
    have hb : -(2 : ℤ) < z ∧ z < 2 := abs_lt.mp (lt_of_not_ge hz)
    have hc : z = -1 ∨ z = 0 ∨ z = 1 := by omega
    rcases hc with rfl | rfl | rfl
    · simp only [F, Int.cast_neg, Int.cast_one, hL.neg_one_pow, sub_self]
    · simp only [F, Int.cast_zero, zero_pow hL0, sub_self]
    · simp only [F, Int.cast_one, one_pow, sub_self]
  calc
    _ = ((integerSpectrum G).map F).sum := (odd_sum_pairing _ F hodd hsmall).symm
    _ = ((spec G).map (fun x => x ^ L - x)).sum := by
      rw [← integerSpectrum_cast G hG, Multiset.map_map]
      rfl
    _ = (((G.adjMatrix ℤ) ^ L).trace : ℝ) := by
      rw [Multiset.sum_map_sub, Paper7Moments.graph_moment_eq_int_trace,
        Multiset.map_id', Paper7Moments.graph_first_moment_zero, sub_zero]
#print axioms Paper7OddIntegral.odd_spectral_support_moment

theorem spectralAsymmetry_card (g : ℕ) (hG : IsIntegralGraph G) (hg : IsOddGirth G g) :
    (g - 1) / 2 ≤ (spectralAsymmetry G).card := by
  apply odd_moment_support_card_lower (spectralAsymmetry G) (signedMultiplicity G) g
  · intro z hz
    exact (spectralAsymmetry_spec G hG z hz).1
  · intro j _ hjg
    have hodd : Odd (2 * j + 1) := ⟨j, by omega⟩
    rw [odd_spectral_support_moment G hG _ hodd,
      Paper7Moments.trace_odd_lt_oddGirth G hg _ hodd hjg, Int.cast_zero]
  · rw [odd_spectral_support_moment G hG g hg.1,
      Paper7Moments.trace_oddGirth G hg]
    have hgpos : (0 : ℝ) < (g : ℝ) := by
      have h := oddGirth_three_le hg
      exact_mod_cast (show 0 < g by omega)
    have hcpos : (0 : ℝ) < (cycleCount G g : ℝ) := by
      exact_mod_cast Paper7OddWalk.cycleCount_oddGirth_pos hg
    push_cast
    positivity
#print axioms Paper7OddIntegral.spectralAsymmetry_card

theorem proposition3_asymmetric_values (g : ℕ) (hG : IsIntegralGraph G)
    (hg : IsOddGirth G g) :
    ∃ S : Finset ℤ,
      (∀ v ∈ S, 2 ≤ v ∧ mult G (v : ℝ) ≠ mult G (-(v : ℝ))) ∧
      (g - 1) / 2 ≤ S.card := by
  exact ⟨spectralAsymmetry G, spectralAsymmetry_spec G hG,
    spectralAsymmetry_card G g hG hg⟩
#print axioms Paper7OddIntegral.proposition3_asymmetric_values

theorem spectralAsymmetry_square_le (hG : IsIntegralGraph G) :
    (∑ z ∈ spectralAsymmetry G, (z : ℝ) ^ 2) ≤ 2 * (G.edgeFinset.card : ℝ) := by
  have h := asymmetric_support_square_le (integerSpectrum G)
  have hm := Paper7Moments.graph_moment_eq_int_trace G 2
  rw [← integerSpectrum_cast G hG, Multiset.map_map,
    Paper7Moments.trace_square G] at hm
  have hm' : ((integerSpectrum G).map (fun z => (z : ℝ) ^ 2)).sum =
      2 * (G.edgeFinset.card : ℝ) := by
    simpa only [Multiset.bind_def, Multiset.pure_def, Multiset.bind_singleton,
      Multiset.map_map, Function.comp_apply, Int.cast_mul, Int.cast_ofNat,
      Int.cast_natCast] using hm
  exact h.trans_eq hm'
#print axioms Paper7OddIntegral.spectralAsymmetry_square_le

end Paper7OddIntegral
