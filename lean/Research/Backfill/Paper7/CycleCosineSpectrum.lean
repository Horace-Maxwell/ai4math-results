import Research.Backfill.Paper7.CycleFiniteBridge
import Research.Backfill.Paper7.ChallengeV2

/-! From the complete complex Fourier factorization to the actual real
characteristic-root multiset. Every frequency, including equal cosines, remains. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Polynomial
namespace Paper7Lemma41
open BackfillPaper7.Challenge

def cycleCosine (b : ℕ) (k : ZMod b) : ℝ :=
  2 * Real.cos (2 * Real.pi * ((k.val : ℝ) / b))
#print axioms Paper7Lemma41.cycleCosine

theorem character_pair_eq_cycleCosine (b : ℕ) [NeZero b] (k : ZMod b) :
    ZMod.stdAddChar k + ZMod.stdAddChar (-k) = (cycleCosine b k : ℂ) := by
  change ZMod.stdAddChar k + ZMod.stdAddChar (-k) =
    ((2 * Real.cos (2 * Real.pi * ((k.val : ℝ) / b)) : ℝ) : ℂ)
  simp only [ZMod.stdAddChar_apply]
  rw [AddChar.map_neg_eq_inv, Circle.coe_inv_eq_conj, Complex.add_conj,
    ZMod.toCircle_eq_circleExp, Circle.coe_exp, Complex.exp_ofReal_mul_I_re]
#print axioms Paper7Lemma41.character_pair_eq_cycleCosine

theorem cycleGraph_charpoly_real (b : ℕ) [NeZero b] (hb : 3 ≤ b) :
    ((SimpleGraph.cycleGraph b).adjMatrix ℝ).charpoly =
      ∏ k : ZMod b, (X - C (cycleCosine b k)) := by
  have hA : ((SimpleGraph.cycleGraph b).adjMatrix ℝ).map (algebraMap ℝ ℂ) =
      (SimpleGraph.cycleGraph b).adjMatrix ℂ := by
    apply Matrix.ext
    intro i j
    by_cases h : (SimpleGraph.cycleGraph b).Adj i j <;>
      simp [SimpleGraph.adjMatrix_apply, h]
  apply Polynomial.map_injective (algebraMap ℝ ℂ) Complex.ofReal_injective
  rw [← Matrix.charpoly_map, hA, cycleGraph_charpoly_complex b hb]
  simp only [Polynomial.map_prod, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
  apply Finset.prod_congr rfl
  intro k _
  exact congrArg (fun z : ℂ => (X - C z : Polynomial ℂ))
    (character_pair_eq_cycleCosine b k)
#print axioms Paper7Lemma41.cycleGraph_charpoly_real

/-- Complete spectrum with multiplicity; a multiset map, not a set image. -/
theorem cycleGraph_spec (b : ℕ) [NeZero b] (hb : 3 ≤ b) :
    spec (SimpleGraph.cycleGraph b) =
      (Finset.univ.val : Multiset (ZMod b)).map (cycleCosine b) := by
  have hp : (∏ k : ZMod b, (X - C (cycleCosine b k) : Polynomial ℝ)) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro k _
    exact Polynomial.X_sub_C_ne_zero _
  rw [spec, eigs, cycleGraph_charpoly_real b hb, Polynomial.roots_prod _ _ hp]
  simp_rw [Polynomial.roots_X_sub_C]
  exact Multiset.bind_singleton _ (cycleCosine b)
#print axioms Paper7Lemma41.cycleGraph_spec

theorem cycleGraph_Ngt_one_frequency_count (b : ℕ) [NeZero b] (hb : 3 ≤ b) :
    Ngt (SimpleGraph.cycleGraph b) 1 =
      (Finset.univ.filter (fun k : ZMod b => 1 < cycleCosine b k)).card := by
  rw [Ngt, cycleGraph_spec b hb, Multiset.filter_map, Multiset.card_map]
  rfl
#print axioms Paper7Lemma41.cycleGraph_Ngt_one_frequency_count

end Paper7Lemma41
