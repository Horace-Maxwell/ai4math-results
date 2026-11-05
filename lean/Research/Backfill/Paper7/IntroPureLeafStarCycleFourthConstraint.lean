import Research.Backfill.Paper7.IntroRadiusThreeSLeafTransport
import Research.Backfill.Paper7.IntroPureLeafStarAttachmentMoments
import Research.Backfill.Paper7.IntroPureLeafStarLocalMoments
import Research.Backfill.Paper7.IntroAttachmentLeafStarShape

/-! The actual leaf and attachment moments, together with the seven-root
S transport, determine the fourth moment at the other neighbor c.
All three interfaces use the same graph, leaf set, and selected leaf.
No moment value, Perron norm, or classification conclusion is assumed. -/
set_option autoImplicit false
noncomputable section
open scoped Classical Matrix BigOperators

namespace Paper7IntroPureLeafConstraints
open Matrix SimpleGraph BackfillPaper7.Challenge Paper7OddIntegral
open BackfillPaper7.Challenge.Legacy.Algebra
open Paper7IntroProjectors Paper7IntroSLeafTransport Paper7IntroPureLeafMoments
open Paper7IntroAttachmentLeafStar Paper7IntroFour

theorem pure_leaf_star_cycle_fourth_constraint
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hI : IsIntegralGraph G)
    (hbound : ∀ t ∈ spec G, |t| ≤ 3) (a c : V)
    (Y : Finset V) (hc : c ∉ Y)
    (hNa : G.neighborFinset a = insert c Y)
    (hNl : ∀ y ∈ Y, ∀ z, G.Adj y z ↔ z = a)
    (l : V) (hl : l ∈ Y) :
    ((G.adjMatrix ℝ) ^ 4) c c =
      (14 - 2 * (Y.card : ℝ)) * (G.degree c : ℝ) - (Y.card : ℝ) ^ 3 +
        11 * (Y.card : ℝ) ^ 2 - 21 * (Y.card : ℝ) - 13 := by
  obtain ⟨hm4, hm6⟩ := pure_leaf_star_attachment_even_moments G a c Y hc hNa hNl
  have hdeg : G.degree a = Y.card + 1 := by
    rw [← G.card_neighborFinset_eq_degree, hNa, Finset.card_insert_of_notMem hc]
  have hm2 : ((G.adjMatrix ℝ) ^ 2) a a = (Y.card : ℝ) + 1 := by
    rw [pow_two, G.adjMatrix_mul_self_apply_self]
    exact_mod_cast hdeg
  have hleaf := pure_leaf_star_leaf_S_diagonal G a c Y hc hNa hNl l hl
  have hS := integral_radius_three_S_leaf_neighbor_diagonal G hI hbound l a (hNl l hl)
  rw [hleaf] at hS
  simp only [radiusThreeS, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply,
    smul_eq_mul, hm2, hm4, hm6] at hS
  nlinarith only [hS]
#print axioms Paper7IntroPureLeafConstraints.pure_leaf_star_cycle_fourth_constraint

theorem intro21_even_actual_leaf_star_cycle_fourth_constraint
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (b : ℕ)
    (hG : IsUnicyclicWithCycle G b) (hI : IsIntegralGraph G)
    (hn : Fintype.card V ≤ 21) (hb : Even b)
    (r : V) (w : G.Walk r r) (hw : w.IsCycle) (hlen : w.length = b)
    (C : (deleteVertices G {q | q ∈ w.support}).ConnectedComponent)
    (a : C.supp) (c : {q : V // q ∈ w.support}) (hac : G.Adj a.val.val c.val)
    (hleaves : ((G.neighborFinset a.val.val).erase c.val).Nonempty) :
    ∃ (Y : Finset V) (l : V),
      Y = (G.neighborFinset a.val.val).erase c.val ∧ l ∈ Y ∧
      G.degree a.val.val = Y.card + 1 ∧ a.val.val ≠ c.val ∧
      Function.Injective (fun i : Y => i.val) ∧
      (∀ i : Y, (∃ x : C.supp, x.val.val = i.val) ∧
        G.degree i.val = 1 ∧ i.val ≠ a.val.val ∧ i.val ≠ c.val) ∧
      (∀ x : C.supp, x = a ∨ ∃ i : Y, x.val.val = i.val) ∧
      (∀ z : V, G.Adj a.val.val z ↔ z = c.val ∨ ∃ i : Y, z = i.val) ∧
      (∀ (i : Y) (z : V), G.Adj i.val z ↔ z = a.val.val) ∧
      ((G.adjMatrix ℝ) ^ 4) c.val c.val =
        (14 - 2 * (Y.card : ℝ)) * (G.degree c.val : ℝ) - (Y.card : ℝ) ^ 3 +
          11 * (Y.card : ℝ) ^ 2 - 21 * (Y.card : ℝ) - 13 := by
  obtain ⟨Y, hY, hda, hne, hinj, hdata, hcover, hNa, hNl⟩ :=
    intro21_even_actual_attachment_leaf_star G b hG hI hn hb r w hw hlen C a c hac
  have hYpos : Y.Nonempty := by rw [hY]; exact hleaves
  obtain ⟨l, hl⟩ := hYpos
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
  have hmoment := pure_leaf_star_cycle_fourth_constraint
    G hI hbound a.val.val c.val Y hcY hNa' hNl' l hl
  exact ⟨Y, l, hY, hl, hda, hne, hinj, hdata, hcover, hNa, hNl, hmoment⟩
#print axioms Paper7IntroPureLeafConstraints.intro21_even_actual_leaf_star_cycle_fourth_constraint

end Paper7IntroPureLeafConstraints
