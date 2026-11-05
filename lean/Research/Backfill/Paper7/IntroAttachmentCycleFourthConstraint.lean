import Research.Backfill.Paper7.IntroAttachmentAnnihilatorRelation
import Research.Backfill.Paper7.IntroAttachmentEvenMoments
import Research.Backfill.Paper7.IntroAttachmentNormDegreeConstraints

/-! Join the genuine local M4/M6 values with the actual reduced
annihilator, on one selected arm witness. The original graph wrapper retains
all normalized data and does not identify separate existential wrappers. -/
set_option autoImplicit false
noncomputable section
open scoped Classical Matrix BigOperators

namespace Paper7IntroStarConstraints
open SimpleGraph Matrix BackfillPaper7.Challenge
open BackfillPaper7.Challenge.Legacy.Algebra
open Paper7IntroAttachmentMoments Paper7IntroFour Paper7UnicyclicAttachment

theorem subdivided_star_cycle_fourth_constraint
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hI : IsIntegralGraph G) (hbound : ∀ t ∈ spec G, |t| ≤ 3)
    (a c : V) (Y : Finset V) (leaf : Y → V) (i₀ : Y)
    (hc : c ∉ Y) (hNa : G.neighborFinset a = insert c Y)
    (hal : ∀ i : Y, a ≠ leaf i)
    (hNy : ∀ (i : Y) z, G.Adj i.val z ↔ z = a ∨ z = leaf i)
    (hNl : ∀ (i : Y) z, G.Adj (leaf i) z ↔ z = i.val)
    (hbridge : ∀ v, G.Adj a v → G.IsBridge s(a, v)) :
    ((G.adjMatrix ℝ) ^ 6) a a - 13 * ((G.adjMatrix ℝ) ^ 4) a a +
        36 * (G.degree a : ℝ) = 0 ∧
      ((G.adjMatrix ℝ) ^ 4) c c =
        (13 - 2 * (Y.card : ℝ)) * (G.degree c : ℝ) -
          (Y.card : ℝ) ^ 3 + 8 * (Y.card : ℝ) ^ 2 - 36 := by
  have hrel := subdivided_arm_attachment_even_relation
    G hI hbound a i₀.val (leaf i₀) (hal i₀) (hNy i₀) (hNl i₀)
  obtain ⟨hdeg, hm4, hm6⟩ :=
    subdivided_star_attachment_even_moments G a c Y leaf hc hNa hal hNy hNl hbridge
  have hdegR : (G.degree a : ℝ) = (Y.card : ℝ) + 1 := by exact_mod_cast hdeg
  refine ⟨hrel, ?_⟩
  nlinarith only [hrel, hm4, hm6, hdegR]
#print axioms Paper7IntroStarConstraints.subdivided_star_cycle_fourth_constraint

theorem intro21_even_actual_attachment_cycle_fourth_constraint
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (b : ℕ)
    (hG : IsUnicyclicWithCycle G b) (hI : IsIntegralGraph G)
    (hn : Fintype.card V ≤ 21) (hb : Even b)
    (r : V) (w : G.Walk r r) (hw : w.IsCycle) (hlen : w.length = b)
    (C : (deleteVertices G {q | q ∈ w.support}).ConnectedComponent)
    (a : C.supp) (c : {q : V // q ∈ w.support}) (hac : G.Adj a.val.val c.val)
    (hex : ∃ x : C.supp, x ≠ a ∧ 2 ≤ G.degree x.val.val) :
    ∃ (Y : Finset V) (leaf : Y → V) (i₀ : Y) (f : V → ℝ),
      Y = (G.neighborFinset a.val.val).erase c.val ∧
      3 ≤ Y.card ∧ Y.card < 8 ∧ G.degree a.val.val = Y.card + 1 ∧
      Function.Injective leaf ∧
      (∀ x : C.supp, x = a ∨ ∃ i : Y, x.val.val = i.val ∨ x.val.val = leaf i) ∧
      (∀ z : V, G.Adj a.val.val z ↔ z = c.val ∨ ∃ i : Y, z = i.val) ∧
      (∀ (i : Y) (z : V), G.Adj i.val z ↔ z = a.val.val ∨ z = leaf i) ∧
      (∀ (i : Y) (z : V), G.Adj (leaf i) z ↔ z = i.val) ∧
      (∀ v, 0 < f v) ∧ G.adjMatrix ℝ *ᵥ f = (3 : ℝ) • f ∧
      f (leaf i₀) = 1 ∧ (∀ i : Y, f (leaf i) = 1 ∧ f i.val = 3) ∧
      f a.val.val = 8 ∧ f c.val = 3 * (8 - (Y.card : ℝ)) ∧
      (f ⬝ᵥ f) = 720 / ((Y.card : ℝ) - 2) ∧
      (G.degree c.val : ℝ) = -(Y.card : ℝ) ^ 2 + 9 * (Y.card : ℝ) - 12 ∧
      ((G.adjMatrix ℝ) ^ 6) a.val.val a.val.val -
          13 * ((G.adjMatrix ℝ) ^ 4) a.val.val a.val.val +
            36 * (G.degree a.val.val : ℝ) = 0 ∧
      ((G.adjMatrix ℝ) ^ 4) c.val c.val =
        (13 - 2 * (Y.card : ℝ)) * (G.degree c.val : ℝ) -
          (Y.card : ℝ) ^ 3 + 8 * (Y.card : ℝ) ^ 2 - 36 := by
  obtain ⟨Y, leaf, i₀, f, hY, hm, hlt, hdeg, hinj, hcover, hNa, hNy, hNl,
    hf, hAf, h₀, hweights, ha, hc, hN, hd⟩ :=
    intro21_even_actual_attachment_norm_degree_constraints G b hG hI hn hb r w hw hlen C a c hac hex
  have hcY : c.val ∉ Y := by rw [hY]; exact Finset.notMem_erase c.val _
  have hNa' : G.neighborFinset a.val.val = insert c.val Y := by
    ext z
    rw [G.mem_neighborFinset, Finset.mem_insert]
    constructor
    · intro haz
      rcases (hNa z).mp haz with hzc | ⟨i, hzi⟩
      · exact Or.inl hzc
      · exact Or.inr (hzi.symm ▸ i.property)
    · rintro (hzc | hzY)
      · exact (hNa z).mpr (Or.inl hzc)
      · exact (hNa z).mpr (Or.inr ⟨⟨z, hzY⟩, rfl⟩)
  have hal : ∀ i : Y, a.val.val ≠ leaf i := by
    intro i he
    have hl := (hweights i).1
    rw [he] at ha
    linarith
  have hbridge : ∀ v, G.Adj a.val.val v → G.IsBridge s(a.val.val, v) := by
    intro v hav
    exact unicyclic_off_cycle_edge_isBridge G b hG r w hw hlen a.val.val v a.val.property hav
  obtain ⟨hrel, hm4c⟩ := subdivided_star_cycle_fourth_constraint G hI
    (intro21_even_spectrum_abs_le_three G b hG hI hn hb)
    a.val.val c.val Y leaf i₀ hcY hNa' hal hNy hNl hbridge
  exact ⟨Y, leaf, i₀, f, hY, hm, hlt, hdeg, hinj, hcover, hNa, hNy, hNl,
    hf, hAf, h₀, hweights, ha, hc, hN, hd, hrel, hm4c⟩
#print axioms Paper7IntroStarConstraints.intro21_even_actual_attachment_cycle_fourth_constraint

end Paper7IntroStarConstraints
