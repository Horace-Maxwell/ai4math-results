import Research.Backfill.Paper7.IntroSmallSideExternalStar
import Research.Backfill.Paper7.IntroThreeLeafIntegerPerron
import Research.Backfill.Paper7.IntroCycleExternalNeighborLeafStar

/-! The original m=3,d=3 branch supplies its own single normalized integer
Perron witness. Each actual external neighbor is transported through the
already proved original-graph star theorem. No star, coverage, coordinate
integrality or square-budget premise is added to the original graph. -/
set_option autoImplicit false
noncomputable section
open scoped Classical Matrix BigOperators

namespace Paper7IntroThreeLeafExternal
open SimpleGraph Matrix BackfillPaper7.Challenge Paper7OddIntegral
open BackfillPaper7.Challenge.Legacy.Algebra
open Paper7IntroProjectors Paper7IntroIntegerPerron Paper7IntroExternalLeafStar

theorem intro21_even_three_leaf_degree_three_external_leaves
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (b : ℕ)
    (hG : IsUnicyclicWithCycle G b) (hI : IsIntegralGraph G)
    (hn : Fintype.card V ≤ 21) (hb : Even b)
    (r : V) (w : G.Walk r r) (hw : w.IsCycle) (hlen : w.length = b)
    (C : (deleteVertices G {q | q ∈ w.support}).ConnectedComponent)
    (a : C.supp) (c : {q : V // q ∈ w.support}) (hac : G.Adj a.val.val c.val)
    (hm : ((G.neighborFinset a.val.val).erase c.val).card = 3)
    (hd : G.degree c.val = 3) :
    ∃ (Y : Finset V) (i₀ : Y) (eps f : V → ℝ) (z : V → ℤ),
      Y = (G.neighborFinset a.val.val).erase c.val ∧ Y.card = 3 ∧
      G.degree a.val.val = Y.card + 1 ∧ a.val.val ≠ c.val ∧
      (∀ i : Y, (∃ x : C.supp, x.val.val = i.val) ∧
        G.degree i.val = 1 ∧ i.val ≠ a.val.val ∧ i.val ≠ c.val) ∧
      (∀ x : C.supp, x = a ∨ ∃ i : Y, x.val.val = i.val) ∧
      (∀ t : V, G.Adj a.val.val t ↔ t = c.val ∨ ∃ i : Y, t = i.val) ∧
      (∀ (i : Y) (t : V), G.Adj i.val t ↔ t = a.val.val) ∧
      (∀ v, eps v = 1 ∨ eps v = -1) ∧
      (∀ u v, G.Adj u v → eps u = -eps v) ∧
      (∀ v, 0 < f v) ∧ G.adjMatrix ℝ *ᵥ f = (3 : ℝ) • f ∧
      f i₀.val = 1 ∧ (∀ i : Y, f i.val = 1) ∧
      f a.val.val = 3 ∧ f c.val = 6 ∧
      (∀ i : Y, eps i.val = -eps a.val.val) ∧ eps c.val = -eps a.val.val ∧
      (∀ u v, radiusThreeS (G.adjMatrix ℝ) u v =
          (360 / (f ⬝ᵥ f)) * f u * f v * (1 + eps u * eps v) ∧
        radiusThreeT (G.adjMatrix ℝ) u v =
          (120 / (f ⬝ᵥ f)) * f u * f v * (1 - eps u * eps v)) ∧
      (f ⬝ᵥ f) = 360 ∧ (∀ v, 0 < z v) ∧
      (∀ v, eps v = eps i₀.val → f v = (z v : ℝ)) ∧
      (∀ v, eps v = -eps i₀.val → f v = 3 * (z v : ℝ)) ∧
      (∑ v, if eps v = eps i₀.val then z v ^ 2 else 0) = 180 ∧
      (∑ v, if eps v = -eps i₀.val then z v ^ 2 else 0) = 20 ∧
      (∀ v, v ∈ w.support → eps v = -eps i₀.val →
        ∀ x, x ∉ w.support → G.Adj x v →
          (G.neighborFinset x).erase v = ∅ ∧ G.neighborFinset x = {v} ∧
          (∀ t, G.Adj x t ↔ t = v) ∧ G.degree x = 1 ∧ f x = (z v : ℝ)) := by
  obtain ⟨Y, i₀, eps, f, hY, hmY, hda, hne, hdata, hcover, hNa, hNl,
    hs, hflip, hf, hAf, h₀, hweights, ha, hc, hsgn, hcs, hproj, hcase⟩ :=
    intro21_even_three_leaf_integer_perron G b hG hI hn hb r w hw hlen
      C a c hac hm (Or.inl hd)
  rcases hcase with ⟨⟨_hd, hN⟩, z, hz, hsame, hopp, hsumU, hsumW⟩ |
      ⟨⟨hfour, _hN⟩, _hz⟩
  · refine ⟨Y, i₀, eps, f, z, hY, hmY, hda, hne, hdata, hcover, hNa, hNl,
      hs, hflip, hf, hAf, h₀, hweights, ha, hc, hsgn, hcs, hproj, hN, hz,
      hsame, hopp, hsumU, hsumW, ?_⟩
    intro v hv hvs x hx hxv
    obtain ⟨X, hX, hvX, hNx, hNy, _hdataX, _hdx, hcases⟩ :=
      intro21_even_cycle_external_neighbor_leaf_star G b hG hI hn hb r w hw hlen
        v x hv hx hxv
    have hcard : X.card = 0 ∨ X.card = 1 ∨ X.card = 3 := by
      rcases hcases with hzero | hone | ⟨hthree, _hdv⟩
      · exact Or.inl hzero
      · exact Or.inr (Or.inl hone)
      · exact Or.inr (Or.inr hthree)
    obtain ⟨hXempty, hsingle, hneighbor, hdegree, hweight⟩ :=
      small_integer_side_external_star_is_leaf G eps f z i₀.val v x X
        hflip hAf hz hopp hsumW hvs hxv hvX hNx hNy hcard
    have herase : (G.neighborFinset x).erase v = ∅ := by rw [← hX]; exact hXempty
    exact ⟨herase, hsingle, hneighbor, hdegree, hweight⟩
  · omega
#print axioms Paper7IntroThreeLeafExternal.intro21_even_three_leaf_degree_three_external_leaves

end Paper7IntroThreeLeafExternal
