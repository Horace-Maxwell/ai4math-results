import Research.Backfill.Paper7.IntroAttachmentSubdividedStarShape
import Research.Backfill.Paper7.IntroSubdividedStarPerronWeights

/-! The original graph hypotheses supply the actual complete arm shape,
the simple positive eigenvalue three, and the normalized Perron vector.
Local walk moments and a numerical value of the squared norm remain absent. -/
set_option autoImplicit false
noncomputable section
open scoped Classical Matrix BigOperators

namespace Paper7IntroStarWeights
open SimpleGraph Matrix BackfillPaper7.Challenge Paper7OddIntegral
open BackfillPaper7.Challenge.Legacy.Algebra
open Paper7IntroAttachmentShape Paper7IntroProjectors Paper7IntroEven Paper7IntroFour

theorem intro21_even_actual_attachment_perron_weights
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (b : ℕ)
    (hG : IsUnicyclicWithCycle G b) (hI : IsIntegralGraph G)
    (hn : Fintype.card V ≤ 21) (hb : Even b)
    (r : V) (w : G.Walk r r) (hw : w.IsCycle) (hlen : w.length = b)
    (C : (deleteVertices G {q | q ∈ w.support}).ConnectedComponent)
    (a : C.supp) (c : {q : V // q ∈ w.support}) (hac : G.Adj a.val.val c.val)
    (hex : ∃ x : C.supp, x ≠ a ∧ 2 ≤ G.degree x.val.val) :
    ∃ (Y : Finset V) (leaf : Y → V) (eps f : V → ℝ),
      Y = (G.neighborFinset a.val.val).erase c.val ∧
      3 ≤ Y.card ∧ Y.card < 8 ∧ G.degree a.val.val = Y.card + 1 ∧
      Function.Injective leaf ∧
      (∀ x : C.supp, x = a ∨ ∃ i : Y, x.val.val = i.val ∨ x.val.val = leaf i) ∧
      (∀ z : V, G.Adj a.val.val z ↔ z = c.val ∨ ∃ i : Y, z = i.val) ∧
      (∀ (i : Y) (z : V), G.Adj i.val z ↔ z = a.val.val ∨ z = leaf i) ∧
      (∀ (i : Y) (z : V), G.Adj (leaf i) z ↔ z = i.val) ∧
      (∀ v, eps v = 1 ∨ eps v = -1) ∧
      (∀ u v, G.Adj u v → eps u = -eps v) ∧
      (∀ v, 0 < f v) ∧ G.adjMatrix ℝ *ᵥ f = (3 : ℝ) • f ∧
      (∀ i : Y, f (leaf i) = 1 ∧ f i.val = 3) ∧
      f a.val.val = 8 ∧ f c.val = 3 * (8 - (Y.card : ℝ)) ∧
      (∀ i : Y, eps (leaf i) = eps a.val.val ∧ eps i.val = -eps a.val.val) ∧
      eps c.val = -eps a.val.val ∧
      (∀ u v, radiusThreeS (G.adjMatrix ℝ) u v =
          (360 / (f ⬝ᵥ f)) * f u * f v * (1 + eps u * eps v) ∧
        radiusThreeT (G.adjMatrix ℝ) u v =
          (120 / (f ⬝ᵥ f)) * f u * f v * (1 - eps u * eps v)) ∧
      (∑ v, if eps v = 1 then f v ^ 2 else 0) = (f ⬝ᵥ f) / 2 ∧
      (∑ v, if eps v = -1 then f v ^ 2 else 0) = (f ⬝ᵥ f) / 2 ∧
      (∀ i : Y, radiusThreeS (G.adjMatrix ℝ) (leaf i) (leaf i) =
          720 / (f ⬝ᵥ f) ∧
        radiusThreeT (G.adjMatrix ℝ) (leaf i) c.val =
          (720 / (f ⬝ᵥ f)) * (8 - (Y.card : ℝ))) := by
  obtain ⟨Y, leaf, hY, hm, hda, _hYC, _hlC, hinj, hdata,
    hcover, hNa, hNy, hNl⟩ :=
    intro21_even_actual_attachment_subdivided_star G b hG hI hn hb r w hw hlen C a c hac hex
  have hYpos : Y.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨y, hy⟩ := hYpos
  let i₀ : Y := ⟨y, hy⟩
  have hthree := intro21_even_nonleaf_component_count_three
    G b hG hI hn hb r w hw hlen C a c hac hex
  have hB := even_unicyclic_colorable_two G b hG hb
  have hbound := intro21_even_spectrum_abs_le_three G b hG hI hn hb
  obtain ⟨eps, f, hs, hflip, hf, h₀, hAf, hproj, hp, hnrm⟩ :=
    connected_bipartite_integral_radius_three_projectors G hG.1 hI hB hbound hthree (leaf i₀)
  have hcY : c.val ∉ Y := by rw [hY]; exact Finset.notMem_erase c.val _
  have hal : ∀ i : Y, a.val.val ≠ leaf i := by
    intro i
    exact (hdata i).2.2.2.2.1.symm
  obtain ⟨hweights, ha, hc, hlt⟩ := subdivided_star_normalized_perron_weights
    G Y leaf a.val.val c.val i₀ hcY hal hNa hNy hNl f hf hAf h₀
  obtain ⟨hsgn, hcs⟩ := subdivided_star_bipartite_signs
    G Y leaf a.val.val c.val hNa hNy eps hflip
  have hsq : eps a.val.val * eps a.val.val = 1 := by
    rcases hs a.val.val with h | h
    · rw [h]; norm_num
    · rw [h]; norm_num
  refine ⟨Y, leaf, eps, f, hY, hm, hlt, hda, hinj, hcover, hNa, hNy, hNl,
    hs, hflip, hf, hAf, hweights, ha, hc, hsgn, hcs, hproj, hp, hnrm, ?_⟩
  intro i
  have hl := (hweights i).1
  have hls := (hsgn i).1
  have hprod : eps (leaf i) * eps c.val = -1 := by
    rw [hls, hcs, mul_neg, hsq]
  constructor
  · rw [(hproj (leaf i) (leaf i)).1, hl, hls, hsq]
    ring
  · rw [(hproj (leaf i) c.val).2, hl, hc, hprod]
    ring
#print axioms Paper7IntroStarWeights.intro21_even_actual_attachment_perron_weights

end Paper7IntroStarWeights
