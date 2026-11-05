import Research.Backfill.Paper7.IntroRadiusThreeIntegerCoordinates
import Research.Backfill.Paper7.IntroAttachmentLeafStarMomentNorm

/-! The m=3,d=3/4 branch is a genuine original graph branch. The
integer coordinates and side square sums are conclusions, obtained from
one 783 witness and actual 758 integer S/T entries. The sign side is
relative to that witness's selected leaf, never assumed positive. -/
set_option autoImplicit false
noncomputable section
open scoped Classical Matrix BigOperators

namespace Paper7IntroIntegerPerron
open Matrix SimpleGraph BackfillPaper7.Challenge Paper7OddIntegral
open BackfillPaper7.Challenge.Legacy.Algebra
open Paper7IntroProjectors Paper7IntroLeafStarWeights

theorem intro21_even_three_leaf_integer_perron
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (b : ℕ)
    (hG : IsUnicyclicWithCycle G b) (hI : IsIntegralGraph G)
    (hn : Fintype.card V ≤ 21) (hb : Even b)
    (r : V) (w : G.Walk r r) (hw : w.IsCycle) (hlen : w.length = b)
    (C : (deleteVertices G {q | q ∈ w.support}).ConnectedComponent)
    (a : C.supp) (c : {q : V // q ∈ w.support}) (hac : G.Adj a.val.val c.val)
    (hm : ((G.neighborFinset a.val.val).erase c.val).card = 3)
    (hd : G.degree c.val = 3 ∨ G.degree c.val = 4) :
    ∃ (Y : Finset V) (i₀ : Y) (eps f : V → ℝ),
      Y = (G.neighborFinset a.val.val).erase c.val ∧ Y.card = 3 ∧
      G.degree a.val.val = Y.card + 1 ∧ a.val.val ≠ c.val ∧
      (∀ i : Y, (∃ x : C.supp, x.val.val = i.val) ∧
        G.degree i.val = 1 ∧ i.val ≠ a.val.val ∧ i.val ≠ c.val) ∧
      (∀ x : C.supp, x = a ∨ ∃ i : Y, x.val.val = i.val) ∧
      (∀ z : V, G.Adj a.val.val z ↔ z = c.val ∨ ∃ i : Y, z = i.val) ∧
      (∀ (i : Y) (z : V), G.Adj i.val z ↔ z = a.val.val) ∧
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
      (((G.degree c.val = 3 ∧ (f ⬝ᵥ f) = 360) ∧
        ∃ z : V → ℤ, (∀ v, 0 < z v) ∧
          (∀ v, eps v = eps i₀.val → f v = (z v : ℝ)) ∧
          (∀ v, eps v = -eps i₀.val → f v = 3 * (z v : ℝ)) ∧
          (∑ v, if eps v = eps i₀.val then z v ^ 2 else 0) = 180 ∧
          (∑ v, if eps v = -eps i₀.val then z v ^ 2 else 0) = 20) ∨
       ((G.degree c.val = 4 ∧ (f ⬝ᵥ f) = 240) ∧
        ∃ z : V → ℤ, (∀ v, 0 < z v) ∧ (∀ v, f v = (z v : ℝ)) ∧
          (∑ v, if eps v = eps i₀.val then z v ^ 2 else 0) = 120 ∧
          (∑ v, if eps v = -eps i₀.val then z v ^ 2 else 0) = 120)) := by
  have hleaves : ((G.neighborFinset a.val.val).erase c.val).Nonempty := by
    apply Finset.card_pos.mp
    omega
  obtain ⟨Y, i₀, eps, f, hY, _hmpos, _hm7, _hlt, hda, hne, _hinj, hdata,
    hcover, hNa, hNl, _hthree, hs, hflip, hf, hAf, h₀, hweights, ha, hc,
    hsgn, hcs, hproj, hp, hnrm, _hmom, _hNpos, _hqpos, hnorm⟩ :=
    intro21_even_actual_leaf_star_moment_norm G b hG hI hn hb r w hw hlen C a c hac hleaves
  have hmY : Y.card = 3 := by rw [hY]; exact hm
  have hfc : f c.val = 6 := by
    rw [hmY] at hc
    norm_num at hc
    exact hc
  refine ⟨Y, i₀, eps, f, hY, hmY, hda, hne, hdata, hcover, hNa, hNl,
    hs, hflip, hf, hAf, h₀, hweights, ha, hfc, hsgn, hcs, hproj, ?_⟩
  rcases hd with hd | hd
  · have hN : (f ⬝ᵥ f) = 360 := by
      rw [hmY, hd] at hnorm
      norm_num at hnorm
      exact hnorm
    exact Or.inl ⟨⟨hd, hN⟩,
      radius_three_norm360_integer_coordinates G eps f i₀.val hs hf h₀ hN hproj hp hnrm⟩
  · have hN : (f ⬝ᵥ f) = 240 := by
      rw [hmY, hd] at hnorm
      norm_num at hnorm
      exact hnorm
    exact Or.inr ⟨⟨hd, hN⟩,
      radius_three_norm240_integer_coordinates G eps f i₀.val hs hf h₀ hN hproj hp hnrm⟩
#print axioms Paper7IntroIntegerPerron.intro21_even_three_leaf_integer_perron

end Paper7IntroIntegerPerron
