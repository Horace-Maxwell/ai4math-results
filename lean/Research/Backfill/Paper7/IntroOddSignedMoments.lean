import Research.Backfill.Paper7.IntroIntegerWindowCounts
import Research.Backfill.Paper7.Corollary31Graph

/-! Necessary signed multiplicity equations derived from the actual complete
graph spectrum, original odd unicyclicity, and the original order bound. -/
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators

namespace Paper7IntroOddMultiplicity
open BackfillPaper7.Challenge Paper7OddIntegral Paper7Unicyclic

def signedIntegerMultiplicity {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (z : ℤ) : ℤ :=
  ((integerSpectrum G).count z : ℤ) - ((integerSpectrum G).count (-z) : ℤ)
#print axioms Paper7IntroOddMultiplicity.signedIntegerMultiplicity

def pairedIntegerMultiplicity {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (z : ℤ) : ℤ :=
  ((integerSpectrum G).count z : ℤ) + ((integerSpectrum G).count (-z) : ℤ)
#print axioms Paper7IntroOddMultiplicity.pairedIntegerMultiplicity

theorem intro21_multiplicity_total
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (b : ℕ)
    (hG : IsUnicyclicWithCycle G b) (hI : IsIntegralGraph G)
    (hn : Fintype.card V ≤ 21) :
    ((integerSpectrum G).count 0 : ℤ) + pairedIntegerMultiplicity G 1 +
      pairedIntegerMultiplicity G 2 + pairedIntegerMultiplicity G 3 +
      pairedIntegerMultiplicity G 4 = (Fintype.card V : ℤ) := by
  have h : (∑ i : Fin 9, ((integerSpectrum G).count (integerWindowValue i) : ℤ)) =
      (Fintype.card V : ℤ) := by exact_mod_cast intro21_integer_window_card G b hG hI hn
  norm_num [Fin.sum_univ_succ, integerWindowValue] at h
  dsimp only [pairedIntegerMultiplicity]
  linarith
#print axioms Paper7IntroOddMultiplicity.intro21_multiplicity_total

theorem intro21_signed_first_moment
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (b : ℕ)
    (hG : IsUnicyclicWithCycle G b) (hI : IsIntegralGraph G)
    (hn : Fintype.card V ≤ 21) :
    signedIntegerMultiplicity G 1 + 2 * signedIntegerMultiplicity G 2 +
      3 * signedIntegerMultiplicity G 3 + 4 * signedIntegerMultiplicity G 4 = 0 := by
  have h := intro21_integer_window_moment G b hG hI hn 1
  norm_num [Fin.sum_univ_succ, integerWindowValue, SimpleGraph.trace_adjMatrix] at h
  dsimp only [signedIntegerMultiplicity]
  linarith
#print axioms Paper7IntroOddMultiplicity.intro21_signed_first_moment

theorem intro21_paired_second_moment
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (b : ℕ)
    (hG : IsUnicyclicWithCycle G b) (hI : IsIntegralGraph G)
    (hn : Fintype.card V ≤ 21) :
    pairedIntegerMultiplicity G 1 + 4 * pairedIntegerMultiplicity G 2 +
      9 * pairedIntegerMultiplicity G 3 + 16 * pairedIntegerMultiplicity G 4 =
        2 * (Fintype.card V : ℤ) := by
  have h := intro21_integer_window_moment G b hG hI hn 2
  rw [Paper7Moments.trace_square, unicyclic_card_edges G hG] at h
  norm_num [Fin.sum_univ_succ, integerWindowValue] at h
  dsimp only [pairedIntegerMultiplicity]
  linarith
#print axioms Paper7IntroOddMultiplicity.intro21_paired_second_moment

theorem intro21_odd_cycle_eq_three
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (b : ℕ)
    (hG : IsUnicyclicWithCycle G b) (hI : IsIntegralGraph G)
    (hn : Fintype.card V ≤ 21) (hb : Odd b) : b = 3 := by
  by_contra hne
  have h := ((Paper7Corollary31.corollary31_graph G b hI hG hb).2.2 hne).2
  omega
#print axioms Paper7IntroOddMultiplicity.intro21_odd_cycle_eq_three

theorem intro21_signed_third_moment
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (b : ℕ)
    (hG : IsUnicyclicWithCycle G b) (hI : IsIntegralGraph G)
    (hn : Fintype.card V ≤ 21) (hb : Odd b) :
    signedIntegerMultiplicity G 1 + 8 * signedIntegerMultiplicity G 2 +
      27 * signedIntegerMultiplicity G 3 + 64 * signedIntegerMultiplicity G 4 = 6 := by
  have hthree := intro21_odd_cycle_eq_three G b hG hI hn hb
  subst b
  have h := intro21_integer_window_moment G 3 hG hI hn 3
  rw [Paper7Moments.trace_oddGirth G (unicyclic_isOddGirth hG hb),
    unicyclic_cycleCount hG 3] at h
  norm_num [Fin.sum_univ_succ, integerWindowValue] at h
  dsimp only [signedIntegerMultiplicity]
  linarith
#print axioms Paper7IntroOddMultiplicity.intro21_signed_third_moment

theorem abs_signedIntegerMultiplicity_le
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (z : ℤ) :
    |signedIntegerMultiplicity G z| ≤ pairedIntegerMultiplicity G z := by
  dsimp only [signedIntegerMultiplicity, pairedIntegerMultiplicity]
  exact abs_le.mpr ⟨by omega, by omega⟩
#print axioms Paper7IntroOddMultiplicity.abs_signedIntegerMultiplicity_le

theorem intro21_signed_square_cost
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (b : ℕ)
    (hG : IsUnicyclicWithCycle G b) (hI : IsIntegralGraph G)
    (hn : Fintype.card V ≤ 21) :
    |signedIntegerMultiplicity G 1| + 4 * |signedIntegerMultiplicity G 2| +
      9 * |signedIntegerMultiplicity G 3| + 16 * |signedIntegerMultiplicity G 4| ≤ 42 := by
  have htwo := intro21_paired_second_moment G b hG hI hn
  have h1 := abs_signedIntegerMultiplicity_le G 1
  have h2 := abs_signedIntegerMultiplicity_le G 2
  have h3 := abs_signedIntegerMultiplicity_le G 3
  have h4 := abs_signedIntegerMultiplicity_le G 4
  have hnZ : (Fintype.card V : ℤ) ≤ 21 := by exact_mod_cast hn
  linarith
#print axioms Paper7IntroOddMultiplicity.intro21_signed_square_cost

theorem intro21_signed_multiplicity_relations
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (b : ℕ)
    (hG : IsUnicyclicWithCycle G b) (hI : IsIntegralGraph G)
    (hn : Fintype.card V ≤ 21) (hb : Odd b) :
    signedIntegerMultiplicity G 2 = 1 - 4 * signedIntegerMultiplicity G 3 -
      10 * signedIntegerMultiplicity G 4 ∧
    signedIntegerMultiplicity G 1 = -2 + 5 * signedIntegerMultiplicity G 3 +
      16 * signedIntegerMultiplicity G 4 := by
  have hfirst := intro21_signed_first_moment G b hG hI hn
  have hthird := intro21_signed_third_moment G b hG hI hn hb
  constructor <;> omega
#print axioms Paper7IntroOddMultiplicity.intro21_signed_multiplicity_relations

end Paper7IntroOddMultiplicity
