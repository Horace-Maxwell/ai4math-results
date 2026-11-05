import Research.Backfill.Paper7.SpectralMoments

/-! Integer-valued storage for the complete integral graph spectrum. -/
set_option autoImplicit false
noncomputable section
namespace Paper7OddIntegral
open BackfillPaper7.Challenge

variable {V : Type} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

def integerSpectrum : Multiset ℤ := (spec G).map Int.floor
#print axioms Paper7OddIntegral.integerSpectrum

theorem integerSpectrum_cast (hG : IsIntegralGraph G) :
    (integerSpectrum G).map (fun z : ℤ => (z : ℝ)) = spec G := by
  rw [integerSpectrum, Multiset.map_map]
  calc
    _ = (spec G).map id := by
      apply Multiset.map_congr rfl
      intro x hx
      obtain ⟨z, rfl⟩ := Paper7Moments.integral_spec_entry G hG x hx
      simp only [Function.comp_apply, Int.floor_intCast, id_eq]
    _ = spec G := Multiset.map_id _
#print axioms Paper7OddIntegral.integerSpectrum_cast

theorem integerSpectrum_count (hG : IsIntegralGraph G) (z : ℤ) :
    (integerSpectrum G).count z = mult G (z : ℝ) := by
  classical
  have h := Multiset.count_map_eq_count' (fun z : ℤ => (z : ℝ))
    (integerSpectrum G) Int.cast_injective z
  rw [integerSpectrum_cast G hG] at h
  exact h.symm
#print axioms Paper7OddIntegral.integerSpectrum_count

theorem integerSpectrum_moment (hG : IsIntegralGraph G) (k : ℕ) :
    ((integerSpectrum G).map (fun z => z ^ k)).sum = ((G.adjMatrix ℤ) ^ k).trace := by
  have h := Paper7Moments.graph_moment_eq_int_trace G k
  rw [← integerSpectrum_cast G hG, Multiset.map_map] at h
  apply (Int.cast_injective : Function.Injective (fun z : ℤ => (z : ℝ)))
  simpa only [Int.cast_multiset_sum, Multiset.map_map, Function.comp_apply,
    Int.cast_pow] using h
#print axioms Paper7OddIntegral.integerSpectrum_moment

theorem integerSpectrum_sum (hG : IsIntegralGraph G) : (integerSpectrum G).sum = 0 := by
  simpa only [pow_one, Multiset.map_id', SimpleGraph.trace_adjMatrix]
    using integerSpectrum_moment G hG 1
#print axioms Paper7OddIntegral.integerSpectrum_sum

end Paper7OddIntegral
