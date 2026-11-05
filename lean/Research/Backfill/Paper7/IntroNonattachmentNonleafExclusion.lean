import Research.Backfill.Paper7.IntroSubdividedStarCountAlgebra
import Research.Backfill.Paper7.IntroAttachmentCycleFourthConstraint
import Research.Backfill.Paper7.IntroCycleNeighborMomentLower
import Research.Backfill.Paper7.IntroSubdividedStarInvisibleBudget

/-! Eliminate the nonattachment-nonleaf branch in the original graph.
All moment, cardinality, and invisibility data are derived on one actual
arm witness. The attachment itself and the full Intro classification are
not conclusions of this source. -/
set_option autoImplicit false
noncomputable section
open scoped Classical Matrix BigOperators

namespace Paper7IntroStarExclusion
open SimpleGraph Matrix BackfillPaper7.Challenge
open BackfillPaper7.Challenge.Legacy.Algebra
open Paper7IntroStarConstraints Paper7IntroCycleMomentLower
open Paper7IntroStarInvisible Paper7IntroTwoWalkCollision Paper7IntroFour

theorem intro21_even_no_nonattachment_nonleaf
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (b : ℕ)
    (hG : IsUnicyclicWithCycle G b) (hI : IsIntegralGraph G)
    (hn : Fintype.card V ≤ 21) (hb : Even b)
    (r : V) (w : G.Walk r r) (hw : w.IsCycle) (hlen : w.length = b)
    (C : (deleteVertices G {q | q ∈ w.support}).ConnectedComponent)
    (a : C.supp) (c : {q : V // q ∈ w.support}) (hac : G.Adj a.val.val c.val) :
    ¬ ∃ x : C.supp, x ≠ a ∧ 2 ≤ G.degree x.val.val := by
  intro hex
  obtain ⟨Y, leaf, _i₀, f, hY, hm, hlt, hdeg, hinj, _hcover, _hNa, hNy, hNl,
    _hf, _hAf, _h₀, hweights, _ha, hc, _hN, hd, _hrel, ht⟩ :=
    intro21_even_actual_attachment_cycle_fourth_constraint
      G b hG hI hn hb r w hw hlen C a c hac hex
  obtain ⟨hd3, hlow⟩ := cycle_vertex_external_neighbor_moment_lower
    G w hw c.val a.val.val c.property a.val.property hac.symm
  have hd3R : (3 : ℝ) ≤ (G.degree c.val : ℝ) := by exact_mod_cast hd3
  have hdegR : (G.degree a.val.val : ℝ) = (Y.card : ℝ) + 1 := by exact_mod_cast hdeg
  have hlow' : (G.degree c.val : ℝ) ^ 2 + (Y.card : ℝ) + 2 ≤
      ((G.adjMatrix ℝ) ^ 4) c.val c.val := by
    rw [hdegR] at hlow
    linarith only [hlow]
  have hm3 : Y.card = 3 := arm_count_eq_three_of_moment_constraints
    Y.card (G.degree c.val : ℝ) (((G.adjMatrix ℝ) ^ 4) c.val c.val)
    hm hlt hd3R hd ht hlow'
  have hd6 : (G.degree c.val : ℝ) = 6 := by
    norm_num [hm3] at hd
    exact hd
  have ht51 : ((G.adjMatrix ℝ) ^ 4) c.val c.val = 51 := by
    rw [hm3, hd6] at ht
    norm_num at ht
    exact ht
  have hc15 : f c.val = 15 := by
    rw [hm3] at hc
    norm_num at hc
    exact hc
  have hcnot : c.val ∉ Y := by rw [hY]; exact Finset.notMem_erase c.val _
  have hcY : ∀ i : Y, c.val ≠ i.val := by
    intro i he
    exact hcnot (he.symm ▸ i.property)
  have hcL : ∀ i : Y, c.val ≠ leaf i := by
    intro i he
    have hl := (hweights i).1
    rw [he] at hc15
    linarith only [hc15, hl]
  have hca : c.val ≠ a.val.val := hac.ne.symm
  have htriangle := even_unicyclic_no_triangle G b hG hb
  have hbudget := unicyclic_subdivided_star_fourth_moment_budget
    G b hG htriangle a.val.val c.val Y leaf hinj hca hcY hcL hNy hNl
  rw [ht51, hd6, hm3] at hbudget
  have hnR : (Fintype.card V : ℝ) ≤ 21 := by exact_mod_cast hn
  norm_num at hbudget
  linarith only [hbudget, hnR]
#print axioms Paper7IntroStarExclusion.intro21_even_no_nonattachment_nonleaf

theorem intro21_even_nonattachment_degree_one
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (b : ℕ)
    (hG : IsUnicyclicWithCycle G b) (hI : IsIntegralGraph G)
    (hn : Fintype.card V ≤ 21) (hb : Even b)
    (r : V) (w : G.Walk r r) (hw : w.IsCycle) (hlen : w.length = b)
    (C : (deleteVertices G {q | q ∈ w.support}).ConnectedComponent)
    (a : C.supp) (c : {q : V // q ∈ w.support}) (hac : G.Adj a.val.val c.val)
    (x : C.supp) (hxa : x ≠ a) : G.degree x.val.val = 1 := by
  have hpos := unicyclic_positive_degree G b hG x.val.val
  have hnot := intro21_even_no_nonattachment_nonleaf G b hG hI hn hb r w hw hlen C a c hac
  by_contra hne
  have hx2 : 2 ≤ G.degree x.val.val := by omega
  exact hnot ⟨x, hxa, hx2⟩
#print axioms Paper7IntroStarExclusion.intro21_even_nonattachment_degree_one

end Paper7IntroStarExclusion
