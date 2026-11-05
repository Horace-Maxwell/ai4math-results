import Research.Backfill.Paper7.IntroAttachmentLeafStarShape
import Research.Backfill.Paper7.IntroLeafStarPerronWeights
import Research.Backfill.Paper7.IntroCycleNeighborMomentLower

/-! The original graph supplies the canonical leaf star, count-three,
bipartition and normalized Perron vector. Nonempty canonical leaves select
an anchor only. No local walk moment or numerical norm is assumed. -/
set_option autoImplicit false
noncomputable section
open scoped Classical Matrix BigOperators

namespace Paper7IntroLeafStarWeights
open SimpleGraph Matrix BackfillPaper7.Challenge Paper7OddIntegral
open BackfillPaper7.Challenge.Legacy.Algebra
open Paper7IntroAttachmentLeafStar Paper7IntroProjectors
open Paper7IntroEven Paper7IntroFour Paper7IntroCycleNeighborhood Paper7IntroCycleMomentLower

theorem intro21_even_actual_leaf_star_perron_weights
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (b : ℕ)
    (hG : IsUnicyclicWithCycle G b) (hI : IsIntegralGraph G)
    (hn : Fintype.card V ≤ 21) (hb : Even b)
    (r : V) (w : G.Walk r r) (hw : w.IsCycle) (hlen : w.length = b)
    (C : (deleteVertices G {q | q ∈ w.support}).ConnectedComponent)
    (a : C.supp) (c : {q : V // q ∈ w.support}) (hac : G.Adj a.val.val c.val)
    (hleaves : ((G.neighborFinset a.val.val).erase c.val).Nonempty) :
    ∃ (Y : Finset V) (i₀ : Y) (eps f : V → ℝ),
      Y = (G.neighborFinset a.val.val).erase c.val ∧
      1 ≤ Y.card ∧ Y.card ≤ 7 ∧ Y.card < 9 ∧
      G.degree a.val.val = Y.card + 1 ∧ a.val.val ≠ c.val ∧
      Function.Injective (fun i : Y => i.val) ∧
      (∀ i : Y, (∃ x : C.supp, x.val.val = i.val) ∧
        G.degree i.val = 1 ∧ i.val ≠ a.val.val ∧ i.val ≠ c.val) ∧
      (∀ x : C.supp, x = a ∨ ∃ i : Y, x.val.val = i.val) ∧
      (∀ z : V, G.Adj a.val.val z ↔ z = c.val ∨ ∃ i : Y, z = i.val) ∧
      (∀ (i : Y) (z : V), G.Adj i.val z ↔ z = a.val.val) ∧
      (integerSpectrum G).count 3 = 1 ∧
      (∀ v, eps v = 1 ∨ eps v = -1) ∧
      (∀ u v, G.Adj u v → eps u = -eps v) ∧
      (∀ v, 0 < f v) ∧ G.adjMatrix ℝ *ᵥ f = (3 : ℝ) • f ∧
      f i₀.val = 1 ∧ (∀ i : Y, f i.val = 1) ∧
      f a.val.val = 3 ∧ f c.val = 9 - (Y.card : ℝ) ∧
      (∀ i : Y, eps i.val = -eps a.val.val) ∧ eps c.val = -eps a.val.val ∧
      (∀ u v, radiusThreeS (G.adjMatrix ℝ) u v =
          (360 / (f ⬝ᵥ f)) * f u * f v * (1 + eps u * eps v) ∧
        radiusThreeT (G.adjMatrix ℝ) u v =
          (120 / (f ⬝ᵥ f)) * f u * f v * (1 - eps u * eps v)) ∧
      (∑ v, if eps v = 1 then f v ^ 2 else 0) = (f ⬝ᵥ f) / 2 ∧
      (∑ v, if eps v = -1 then f v ^ 2 else 0) = (f ⬝ᵥ f) / 2 := by
  obtain ⟨Y, hY, hda, hne, hinj, hdata, hcover, hNa, hNl⟩ :=
    intro21_even_actual_attachment_leaf_star G b hG hI hn hb r w hw hlen C a c hac
  have hYpos : Y.Nonempty := by rw [hY]; exact hleaves
  obtain ⟨y, hy⟩ := hYpos
  let i₀ : Y := ⟨y, hy⟩
  have hmpos : 1 ≤ Y.card := Finset.card_pos.mpr ⟨y, hy⟩
  have hda8 := intro21_even_degree_le_eight G b hG hI hn hb a.val.val
  have hm7 : Y.card ≤ 7 := by omega
  have hdc3 := (cycle_vertex_external_neighbor_moment_lower
    G w hw c.val a.val.val c.property a.val.property hac.symm).1
  have hthree : (integerSpectrum G).count 3 = 1 := by
    rcases intro21_even_actual_spectral_alternatives G b hG hI hn hb with
      hC4 | hC6 | hR3 | hR4
    · obtain ⟨e⟩ : Nonempty (G ≃g cycleGraph 4) := hC4
      have hdc2 := cycle_iso_degree_two G 4 (by norm_num) e c.val
      omega
    · obtain ⟨e⟩ : Nonempty (G ≃g cycleGraph 6) := hC6
      have hdc2 := cycle_iso_degree_two G 6 (by norm_num) e c.val
      omega
    · obtain ⟨_z, _u, _v, _hz, _hu, _hv, _hn, _hm, _hlimit, hthree, _hfour, _hdev⟩ := hR3
      exact hthree
    · obtain ⟨_z, _u, _v, _hz, _hu, _hv, _hn, _hm, _hlimit, _hthree, hfour, _hdev⟩ := hR4
      exact (intro21_even_no_top_four G b hG hI hn hb hfour).elim
  have hB := even_unicyclic_colorable_two G b hG hb
  have hbound := intro21_even_spectrum_abs_le_three G b hG hI hn hb
  obtain ⟨eps, f, hs, hflip, hf, h₀, hAf, hproj, hp, hnrm⟩ :=
    connected_bipartite_integral_radius_three_projectors G hG.1 hI hB hbound hthree i₀.val
  have hcY : c.val ∉ Y := by rw [hY]; exact Finset.notMem_erase c.val _
  obtain ⟨hweights, ha, hc, hlt⟩ := leaf_star_normalized_perron_weights
    G Y a.val.val c.val i₀ hcY hNa hNl f hf hAf h₀
  have hsgn : ∀ i : Y, eps i.val = -eps a.val.val := by
    intro i
    exact hflip i.val a.val.val ((hNl i a.val.val).mpr rfl)
  have hcs : eps c.val = -eps a.val.val := hflip c.val a.val.val hac.symm
  exact ⟨Y, i₀, eps, f, hY, hmpos, hm7, hlt, hda, hne, hinj, hdata, hcover,
    hNa, hNl, hthree, hs, hflip, hf, hAf, h₀, hweights, ha, hc, hsgn, hcs, hproj, hp, hnrm⟩
#print axioms Paper7IntroLeafStarWeights.intro21_even_actual_leaf_star_perron_weights

end Paper7IntroLeafStarWeights
