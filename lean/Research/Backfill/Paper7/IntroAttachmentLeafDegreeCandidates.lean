import Research.Backfill.Paper7.IntroPureLeafStarScalarCandidates
import Research.Backfill.Paper7.IntroAttachmentNotTwoLeaves
import Research.Backfill.Paper7.IntroPureLeafStarPolynomialBounds
import Research.Backfill.Paper7.IntroPureLeafStarCycleFourthConstraint
import Research.Backfill.Paper7.IntroUnicyclicInvisibleFourthMoment
import Research.Backfill.Paper7.IntroCycleNeighborMomentLower

/-! Original-graph necessary candidates. A nonempty canonical leaf set is
obtained once, and its same vertices feed both polynomial and fourth-moment
identities. No leaf shape, spectral count, moment, or candidate table is assumed. -/
set_option autoImplicit false
noncomputable section
open scoped Classical Matrix BigOperators

namespace Paper7IntroLeafDegreeCandidates
open SimpleGraph Matrix BackfillPaper7.Challenge
open BackfillPaper7.Challenge.Legacy.Algebra
open Paper7IntroAttachmentLeafStar Paper7IntroLeafStarWeights Paper7IntroFour
open Paper7IntroPureLeafMoments Paper7IntroPureLeafConstraints
open Paper7IntroCycleMomentLower Paper7IntroTwoWalkCollision

theorem intro21_even_attachment_leaf_degree_candidates
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (b : ℕ)
    (hG : IsUnicyclicWithCycle G b) (hI : IsIntegralGraph G)
    (hn : Fintype.card V ≤ 21) (hb : Even b)
    (r : V) (w : G.Walk r r) (hw : w.IsCycle) (hlen : w.length = b)
    (C : (deleteVertices G {q | q ∈ w.support}).ConnectedComponent)
    (a : C.supp) (c : {q : V // q ∈ w.support}) (hac : G.Adj a.val.val c.val) :
    let m := ((G.neighborFinset a.val.val).erase c.val).card
    let d := G.degree c.val
    m = 0 ∨ m = 1 ∨ (m = 3 ∧ (d = 3 ∨ d = 4)) ∨ (m = 4 ∧ d = 6) ∨
      (m = 5 ∧ d = 7) ∨ (m = 7 ∧ d = 5) := by
  let m := ((G.neighborFinset a.val.val).erase c.val).card
  let d := G.degree c.val
  change m = 0 ∨ m = 1 ∨ (m = 3 ∧ (d = 3 ∨ d = 4)) ∨ (m = 4 ∧ d = 6) ∨
    (m = 5 ∧ d = 7) ∨ (m = 7 ∧ d = 5)
  by_cases hm0 : m = 0
  · exact Or.inl hm0
  right
  have hleaves : ((G.neighborFinset a.val.val).erase c.val).Nonempty :=
    Finset.card_pos.mp (by change 0 < m; omega)
  obtain ⟨Y, i₀, _eps, _f, hY, hm1, hm7, _hm9, hdeg, _hne, _hinj,
    _hdata, _hcover, hNa, hNl, _rest⟩ :=
    intro21_even_actual_leaf_star_perron_weights G b hG hI hn hb r w hw hlen C a c hac hleaves
  have hcY : c.val ∉ Y := by rw [hY]; exact Finset.notMem_erase c.val _
  have hNa' : G.neighborFinset a.val.val = insert c.val Y := by
    ext z
    simp only [SimpleGraph.mem_neighborFinset, Finset.mem_insert]
    rw [hNa z]
    constructor
    · rintro (hzc | ⟨i, hzi⟩)
      · exact Or.inl hzc
      · exact Or.inr (hzi.symm ▸ i.property)
    · rintro (hzc | hzY)
      · exact Or.inl hzc
      · exact Or.inr ⟨⟨z, hzY⟩, rfl⟩
  have hNl' : ∀ y ∈ Y, ∀ z, G.Adj y z ↔ z = a.val.val := by
    intro y hy z
    exact hNl ⟨y, hy⟩ z
  have hbound := intro21_even_spectrum_abs_le_three G b hG hI hn hb
  obtain ⟨hQ, hP⟩ := integral_radius_three_pure_leaf_star_polynomial_bounds
    G hI hbound a.val.val c.val Y hcY hNa' hNl' i₀.val i₀.property
  have hM := pure_leaf_star_cycle_fourth_constraint
    G hI hbound a.val.val c.val Y hcY hNa' hNl' i₀.val i₀.property
  have hm2 : Y.card ≠ 2 := by
    rw [hY]
    exact intro21_even_attachment_leaf_card_ne_two G b hG hI hn hb r w hw hlen C a c hac
  obtain ⟨hd3, hlower⟩ := cycle_vertex_external_neighbor_moment_lower
    G w hw c.val a.val.val c.property a.val.property hac.symm
  have hdegR : (G.degree a.val.val : ℝ) = (Y.card : ℝ) + 1 := by exact_mod_cast hdeg
  rw [hdegR, hM] at hlower
  have hlow : (G.degree c.val : ℝ) ^ 2 + (Y.card : ℝ) + 2 ≤
      (14 - 2 * (Y.card : ℝ)) * (G.degree c.val : ℝ) - (Y.card : ℝ) ^ 3 +
        11 * (Y.card : ℝ) ^ 2 - 21 * (Y.card : ℝ) - 13 := by linarith
  have htriangle := even_unicyclic_no_triangle G b hG hb
  have hupper := unicyclic_fourth_moment_invisible_bound
    G b hG htriangle c.val ∅ (by simp)
  rw [hM] at hupper
  simp only [Finset.card_empty, Nat.cast_zero, add_zero] at hupper
  have hcases := pure_leaf_star_scalar_candidate_reduction
    Y.card (G.degree c.val) (Fintype.card V) hm1 hm7 hm2 hd3 hn hQ hP hlow hupper
  simpa only [hY] using hcases
#print axioms Paper7IntroLeafDegreeCandidates.intro21_even_attachment_leaf_degree_candidates

end Paper7IntroLeafDegreeCandidates
