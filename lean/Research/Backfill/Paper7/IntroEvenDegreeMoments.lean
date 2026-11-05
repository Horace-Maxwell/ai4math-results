import Research.Backfill.Paper7.IntroEvenBipartiteSpectrum
import Research.Backfill.Paper7.IntroOddSignedMoments

/-! Exact degree and spectral moments in the original arbitrary even
unicyclic range. The degree identity counts all branching, on or off the cycle. -/
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators

namespace Paper7IntroEven
open BackfillPaper7.Challenge Paper7OddIntegral Paper7Unicyclic
open Paper7IntroOddMultiplicity

def degreeDeviation {V : Type} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : ℤ :=
  ∑ v : V, ((G.degree v : ℤ) - 2) ^ 2
#print axioms Paper7IntroEven.degreeDeviation

theorem degreeDeviation_nonneg {V : Type} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : 0 ≤ degreeDeviation G :=
  Finset.sum_nonneg (fun _ _ => sq_nonneg _)
#print axioms Paper7IntroEven.degreeDeviation_nonneg

theorem unicyclic_degreeDeviation_eq_branch_mass
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (b : ℕ)
    (hG : IsUnicyclicWithCycle G b) :
    degreeDeviation G = ∑ v : V, ((G.degree v : ℤ) - 1) * ((G.degree v : ℤ) - 2) := by
  have hdegrees : (∑ v : V, (G.degree v : ℤ)) = 2 * (Fintype.card V : ℤ) := by
    have h := G.sum_degrees_eq_twice_card_edges
    rw [unicyclic_card_edges G hG] at h
    exact_mod_cast h
  have hdiff : (∑ v : V, ((G.degree v : ℤ) - 1) * ((G.degree v : ℤ) - 2)) =
      degreeDeviation G + (∑ v : V, (G.degree v : ℤ)) - 2 * (Fintype.card V : ℤ) := by
    calc
      _ = ∑ v : V, (((G.degree v : ℤ) - 2) ^ 2 + (G.degree v : ℤ) - 2) := by
        apply Finset.sum_congr rfl
        intro v _
        ring
      _ = _ := by
        simp only [degreeDeviation, Finset.sum_sub_distrib, Finset.sum_add_distrib,
          Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        ring
  rw [hdegrees] at hdiff
  linarith
#print axioms Paper7IntroEven.unicyclic_degreeDeviation_eq_branch_mass

theorem unicyclic_trace_four_degreeDeviation
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (b : ℕ)
    (hG : IsUnicyclicWithCycle G b) :
    ((G.adjMatrix ℤ) ^ 4).trace = 2 * degreeDeviation G +
      6 * (Fintype.card V : ℤ) + 8 * (cycleCount G 4 : ℤ) := by
  have hdegrees : (∑ v : V, (G.degree v : ℤ)) = 2 * (Fintype.card V : ℤ) := by
    have h := G.sum_degrees_eq_twice_card_edges
    rw [unicyclic_card_edges G hG] at h
    exact_mod_cast h
  have hsum : (∑ v : V, (G.degree v : ℤ) * ((G.degree v : ℤ) - 1)) =
      degreeDeviation G + 3 * (∑ v : V, (G.degree v : ℤ)) -
        4 * (Fintype.card V : ℤ) := by
    calc
      _ = ∑ v : V, (((G.degree v : ℤ) - 2) ^ 2 + 3 * (G.degree v : ℤ) - 4) := by
        apply Finset.sum_congr rfl
        intro v _
        ring
      _ = _ := by
        simp only [degreeDeviation, Finset.sum_sub_distrib, Finset.sum_add_distrib,
          ← Finset.mul_sum, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        ring
  rw [Paper7Moments.trace_four, unicyclic_card_edges G hG, hsum, hdegrees]
  ring
#print axioms Paper7IntroEven.unicyclic_trace_four_degreeDeviation

theorem intro21_even_multiplicity_card
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (b : ℕ)
    (hG : IsUnicyclicWithCycle G b) (hI : IsIntegralGraph G)
    (hn : Fintype.card V ≤ 21) (hb : Even b) :
    (integerSpectrum G).count 0 + 2 * ((integerSpectrum G).count 1 +
      (integerSpectrum G).count 2 + (integerSpectrum G).count 3 +
      (integerSpectrum G).count 4) = Fintype.card V := by
  have h := intro21_multiplicity_total G b hG hI hn
  have h1 := even_unicyclic_integer_count_neg G b hG hI hb 1
  have h2 := even_unicyclic_integer_count_neg G b hG hI hb 2
  have h3 := even_unicyclic_integer_count_neg G b hG hI hb 3
  have h4 := even_unicyclic_integer_count_neg G b hG hI hb 4
  dsimp only [pairedIntegerMultiplicity] at h
  rw [← h1, ← h2, ← h3, ← h4] at h
  omega
#print axioms Paper7IntroEven.intro21_even_multiplicity_card

theorem intro21_even_second_moment
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (b : ℕ)
    (hG : IsUnicyclicWithCycle G b) (hI : IsIntegralGraph G)
    (hn : Fintype.card V ≤ 21) (hb : Even b) :
    (integerSpectrum G).count 1 + 4 * (integerSpectrum G).count 2 +
      9 * (integerSpectrum G).count 3 + 16 * (integerSpectrum G).count 4 =
        Fintype.card V := by
  have h := intro21_paired_second_moment G b hG hI hn
  have h1 := even_unicyclic_integer_count_neg G b hG hI hb 1
  have h2 := even_unicyclic_integer_count_neg G b hG hI hb 2
  have h3 := even_unicyclic_integer_count_neg G b hG hI hb 3
  have h4 := even_unicyclic_integer_count_neg G b hG hI hb 4
  dsimp only [pairedIntegerMultiplicity] at h
  rw [← h1, ← h2, ← h3, ← h4] at h
  omega
#print axioms Paper7IntroEven.intro21_even_second_moment

theorem intro21_even_branch_moment
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (b : ℕ)
    (hG : IsUnicyclicWithCycle G b) (hI : IsIntegralGraph G)
    (hn : Fintype.card V ≤ 21) (hb : Even b) :
    degreeDeviation G + 2 * (Fintype.card V : ℤ) + 4 * (cycleCount G 4 : ℤ) =
      12 * ((integerSpectrum G).count 2 : ℤ) +
      72 * ((integerSpectrum G).count 3 : ℤ) + 240 * ((integerSpectrum G).count 4 : ℤ) := by
  have hfour := intro21_integer_window_moment G b hG hI hn 4
  rw [unicyclic_trace_four_degreeDeviation G b hG] at hfour
  norm_num [Fin.sum_univ_succ, integerWindowValue] at hfour
  have h1 := even_unicyclic_integer_count_neg G b hG hI hb 1
  have h2 := even_unicyclic_integer_count_neg G b hG hI hb 2
  have h3 := even_unicyclic_integer_count_neg G b hG hI hb 3
  have h4 := even_unicyclic_integer_count_neg G b hG hI hb 4
  rw [← h1, ← h2, ← h3, ← h4] at hfour
  have htwo : ((integerSpectrum G).count 1 : ℤ) + 4 * ((integerSpectrum G).count 2 : ℤ) +
      9 * ((integerSpectrum G).count 3 : ℤ) + 16 * ((integerSpectrum G).count 4 : ℤ) =
        (Fintype.card V : ℤ) := by
    exact_mod_cast intro21_even_second_moment G b hG hI hn hb
  linarith
#print axioms Paper7IntroEven.intro21_even_branch_moment

end Paper7IntroEven
