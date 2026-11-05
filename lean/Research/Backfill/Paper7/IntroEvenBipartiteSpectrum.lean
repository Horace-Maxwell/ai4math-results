import Research.Backfill.Paper7.UnicyclicBasic
import Research.Backfill.Paper7.OddWalkExtraction
import Research.Backfill.Paper7.IntroForestPolynomialParity
import Research.Backfill.Paper7.IntegerSpectrum
import Research.Backfill.Paper7.SpectrumGraphBasics

/-! Bipartiteness and actual multiplicity symmetry for arbitrary even
unicyclic graphs. No constraint on the off-cycle trees is imposed. -/
set_option autoImplicit false
noncomputable section
open scoped Classical

namespace Paper7IntroEven
open SimpleGraph Polynomial BackfillPaper7.Challenge
open BackfillPaper7.Challenge.Legacy.Algebra Paper7Unicyclic Paper7OddIntegral

theorem even_unicyclic_colorable_two
    {V : Type} [DecidableEq V] (G : SimpleGraph V) (b : ℕ)
    (hG : IsUnicyclicWithCycle G b) (hb : Even b) : G.Colorable 2 := by
  apply SimpleGraph.two_colorable_iff_forall_loop_even.mpr
  intro u w
  apply Nat.not_odd_iff_even.mp
  intro hodd
  obtain ⟨s, _hs, huniq⟩ := unicyclic_cycle_unique_data hG
  obtain ⟨v, c, hc, hcodd, _hle, _hedges⟩ :=
    Paper7OddWalk.exists_odd_cycle_length_le w hodd
  have hlen : c.length = b := (huniq c.length c.edges.toFinset ⟨v, c, hc, rfl, rfl⟩).1
  have hceven : Even c.length := hlen.symm ▸ hb
  exact (Nat.not_odd_iff_even.mpr hceven) hcodd
#print axioms Paper7IntroEven.even_unicyclic_colorable_two

theorem even_unicyclic_graphPhi_comp_neg
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (b : ℕ)
    (hG : IsUnicyclicWithCycle G b) (hb : Even b) :
    (graphPhi G).comp (-X) = C ((-1 : ℤ) ^ Fintype.card V) * graphPhi G := by
  obtain ⟨c⟩ := even_unicyclic_colorable_two G b hG hb
  apply Polynomial.funext
  intro x
  simpa only [Polynomial.eval_comp, Polynomial.eval_neg, Polynomial.eval_X,
    Polynomial.eval_mul, Polynomial.eval_C] using
    Paper7IntroOddForest.twoColor_graphPhi_eval_neg G c x
#print axioms Paper7IntroEven.even_unicyclic_graphPhi_comp_neg

theorem even_unicyclic_spec_neg
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (b : ℕ)
    (hG : IsUnicyclicWithCycle G b) (hb : Even b) :
    (spec G).map (fun x : ℝ => -x) = spec G := by
  have h := congrArg (fun f : Polynomial ℤ => f.map (Int.castRingHom ℝ))
    (even_unicyclic_graphPhi_comp_neg G b hG hb)
  simp only [Polynomial.map_comp, Polynomial.map_neg, Polynomial.map_X,
    Polynomial.map_mul, Polynomial.map_C] at h
  rw [Paper7Spectrum.graphPhi_map G ℝ] at h
  have hnz : (Int.castRingHom ℝ) ((-1 : ℤ) ^ Fintype.card V) ≠ 0 := by
    change (((-1 : ℤ) ^ Fintype.card V : ℤ) : ℝ) ≠ 0
    exact_mod_cast pow_ne_zero (Fintype.card V) (by norm_num : (-1 : ℤ) ≠ 0)
  have hr := congrArg Polynomial.roots h
  rw [Polynomial.roots_comp_neg_X, Polynomial.roots_C_mul _ hnz] at hr
  exact hr
#print axioms Paper7IntroEven.even_unicyclic_spec_neg

theorem even_unicyclic_integer_count_neg
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (b : ℕ)
    (hG : IsUnicyclicWithCycle G b) (hI : IsIntegralGraph G) (hb : Even b) (z : ℤ) :
    (integerSpectrum G).count z = (integerSpectrum G).count (-z) := by
  have h := Multiset.count_map_eq_count' (fun x : ℝ => -x) (spec G)
    neg_injective (z : ℝ)
  rw [even_unicyclic_spec_neg G b hG hb] at h
  rw [integerSpectrum_count G hI z, integerSpectrum_count G hI (-z), Int.cast_neg]
  exact h.symm
#print axioms Paper7IntroEven.even_unicyclic_integer_count_neg

end Paper7IntroEven
