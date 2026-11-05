import Research.Backfill.Paper7.IntroUnicyclicSpectralWindow
import Research.Backfill.Paper7.IntegerSpectrum
import Research.Backfill.Paper7.BoundedSpectralSums
import Research.Backfill.Paper7.SpectrumGraphBasics

/-! Exact multiplicity sums for the full original spectrum of every integral
unicyclic graph of order at most 21. The nine integers are the proved window,
not a supplied spectrum profile or a graph catalogue. -/
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators

namespace Paper7IntroOddMultiplicity
open BackfillPaper7.Challenge Paper7OddIntegral Paper7IntroGeneral

def integerWindowValue (i : Fin 9) : ℤ := (i.val : ℤ) - 4
#print axioms Paper7IntroOddMultiplicity.integerWindowValue

theorem integerWindowValue_injective : Function.Injective integerWindowValue := by
  intro i j h
  apply Fin.ext
  dsimp only [integerWindowValue] at h
  omega
#print axioms Paper7IntroOddMultiplicity.integerWindowValue_injective

theorem intro21_integerSpectrum_bounds
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (b : ℕ)
    (hG : IsUnicyclicWithCycle G b) (hI : IsIntegralGraph G)
    (hn : Fintype.card V ≤ 21) (z : ℤ) (hz : z ∈ integerSpectrum G) :
    -4 ≤ z ∧ z ≤ 4 := by
  have hzr : (z : ℝ) ∈ spec G := by
    rw [← integerSpectrum_cast G hI]
    exact Multiset.mem_map.mpr ⟨z, hz, rfl⟩
  obtain ⟨t, he, htlo, hthi⟩ := integral_unicyclic21_spectrum_window G hG hI hn z hzr
  have hzt : z = t := by exact_mod_cast he
  exact hzt.symm ▸ ⟨htlo, hthi⟩
#print axioms Paper7IntroOddMultiplicity.intro21_integerSpectrum_bounds

theorem intro21_integerSpectrum_cover
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (b : ℕ)
    (hG : IsUnicyclicWithCycle G b) (hI : IsIntegralGraph G)
    (hn : Fintype.card V ≤ 21) :
    ∀ z ∈ integerSpectrum G, ∃ i : Fin 9, integerWindowValue i = z := by
  intro z hz
  obtain ⟨hlo, hhi⟩ := intro21_integerSpectrum_bounds G b hG hI hn z hz
  have hcast : ((z + 4).toNat : ℤ) = z + 4 := Int.toNat_of_nonneg (by omega)
  let i : Fin 9 := ⟨(z + 4).toNat, by omega⟩
  refine ⟨i, ?_⟩
  change ((z + 4).toNat : ℤ) - 4 = z
  omega
#print axioms Paper7IntroOddMultiplicity.intro21_integerSpectrum_cover

theorem intro21_integer_window_moment
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (b : ℕ)
    (hG : IsUnicyclicWithCycle G b) (hI : IsIntegralGraph G)
    (hn : Fintype.card V ≤ 21) (k : ℕ) :
    (∑ i : Fin 9, ((integerSpectrum G).count (integerWindowValue i) : ℤ) *
      integerWindowValue i ^ k) = ((G.adjMatrix ℤ) ^ k).trace := by
  have h : ((integerSpectrum G).map (fun z => z ^ k)).sum =
      ∑ i : Fin 9, ((integerSpectrum G).count (integerWindowValue i) : ℤ) *
        integerWindowValue i ^ k := by
    simpa only [nsmul_eq_mul] using Paper7PruningSpectrum.finite_count_sum
      (integerSpectrum G) integerWindowValue integerWindowValue_injective
      (intro21_integerSpectrum_cover G b hG hI hn) (fun z : ℤ => z ^ k)
  exact h.symm.trans (integerSpectrum_moment G hI k)
#print axioms Paper7IntroOddMultiplicity.intro21_integer_window_moment

theorem intro21_integer_window_card
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (b : ℕ)
    (hG : IsUnicyclicWithCycle G b) (hI : IsIntegralGraph G)
    (hn : Fintype.card V ≤ 21) :
    (∑ i : Fin 9, (integerSpectrum G).count (integerWindowValue i)) = Fintype.card V := by
  calc
    _ = (integerSpectrum G).card :=
      (Paper7PruningSpectrum.finite_count_card (integerSpectrum G) integerWindowValue
        integerWindowValue_injective (intro21_integerSpectrum_cover G b hG hI hn)).symm
    _ = (spec G).card := by simp only [integerSpectrum, Multiset.card_map]
    _ = Fintype.card V := Paper7Spectrum.spec_card G
#print axioms Paper7IntroOddMultiplicity.intro21_integer_window_card

end Paper7IntroOddMultiplicity
