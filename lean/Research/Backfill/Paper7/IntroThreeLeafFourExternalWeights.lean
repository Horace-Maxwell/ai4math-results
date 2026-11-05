import Research.Backfill.Paper7.IntroThreeLeafSaturatedStarWeights
import Research.Backfill.Paper7.IntroAttachmentThreeFourColumn
import Research.Backfill.Paper7.IntroCycleExternalNeighborLeafStar

/-! Original m3,d4 graph hypotheses provide the same saturated Perron
witness and every actual external star. No column, moment, norm, star
coverage or coordinate integrality is added to the original assumptions.
The final cycle-case contradiction is a separate remaining obligation. -/
set_option autoImplicit false
noncomputable section
open scoped Classical Matrix BigOperators

namespace Paper7IntroThreeFourExternal
open SimpleGraph Matrix BackfillPaper7.Challenge
open BackfillPaper7.Challenge.Legacy.Algebra
open Paper7IntroThreeFourColumn Paper7IntroExternalLeafStar
open Paper7IntroThreeLeafStarWeights

theorem intro21_even_three_leaf_degree_four_external_weights
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (b : ℕ)
    (hG : IsUnicyclicWithCycle G b) (hI : IsIntegralGraph G)
    (hn : Fintype.card V ≤ 21) (hb : Even b)
    (r : V) (w : G.Walk r r) (hw : w.IsCycle) (hlen : w.length = b)
    (C : (deleteVertices G {q | q ∈ w.support}).ConnectedComponent)
    (a : C.supp) (c : {q : V // q ∈ w.support}) (hac : G.Adj a.val.val c.val)
    (hm : ((G.neighborFinset a.val.val).erase c.val).card = 3)
    (hd : G.degree c.val = 4) :
    ∃ (Y : Finset V) (eps f : V → ℝ),
      Y = (G.neighborFinset a.val.val).erase c.val ∧ Y.card = 3 ∧
      c.val ∉ Y ∧ G.neighborFinset a.val.val = insert c.val Y ∧
      (∀ y ∈ Y, ∀ z, G.Adj y z ↔ z = a.val.val) ∧
      (∀ y ∈ Y, y ∉ w.support) ∧
      (∀ v, eps v = 1 ∨ eps v = -1) ∧
      (∀ u v, G.Adj u v → eps u = -eps v) ∧
      (∀ v, 0 < f v) ∧ G.adjMatrix ℝ *ᵥ f = (3 : ℝ) • f ∧
      f a.val.val = 3 ∧ f c.val = 6 ∧
      (∀ t, eps t = eps c.val → t ≠ c.val → t ∉ Y →
        f t = 3 * ((G.adjMatrix ℝ) ^ 2) t c.val) ∧
      (∀ x, x ∉ w.support → x ≠ a.val.val → G.Adj x c.val →
        G.neighborFinset x = {c.val} ∧ G.degree x = 1 ∧ f x = 2) ∧
      (∀ u, u ∈ w.support → G.Adj u c.val →
        ∀ x, x ∉ w.support → G.Adj x u →
          f x = 3 ∧ (f u = 9 ∨ f u = 8 ∨ f u = 6)) := by
  obtain ⟨Y, _i₀, eps, f, hY, hY3, hcY, hNa, hNl, hdata, _hcover,
      hs, hflip, hf, hAf, _hbase, _hleaf, ha, hc, _hN, _hside, _hM, hcol⟩ :=
    intro21_even_three_leaf_degree_four_perron_column
      G b hG hI hn hb r w hw hlen C a c hac hm hd
  have haout : a.val.val ∉ w.support := a.val.property
  have hYout : ∀ y ∈ Y, y ∉ w.support := by
    intro y hy
    obtain ⟨⟨v, hv⟩, _hd, _hya, _hyc⟩ := hdata ⟨y, hy⟩
    have hv' : v.val.val = y := hv
    rw [← hv']
    exact v.val.property
  have hcstars : ∀ x, x ∉ w.support → x ≠ a.val.val → G.Adj x c.val →
      G.neighborFinset x = {c.val} ∧ G.degree x = 1 ∧ f x = 2 := by
    intro x hx hxa hxc
    obtain ⟨Z, _hZ, hcZ, hNx, hNz, _hZdata, _hdegree, hcases⟩ :=
      intro21_even_cycle_external_neighbor_leaf_star
        G b hG hI hn hb r w hw hlen c.val x c.property hx hxc
    have hcount : Z.card = 0 ∨ Z.card = 1 ∨ Z.card = 3 := by
      rcases hcases with h0 | h1 | h3
      · exact Or.inl h0
      · exact Or.inr (Or.inl h1)
      · exact Or.inr (Or.inr h3.1)
    exact (saturated_other_star_at_c G eps f hflip hAf a.val.val c.val x
      Y Z hNl hxa hcZ hNx hNz hcount hc hcol).2
  have hnbrstars : ∀ u, u ∈ w.support → G.Adj u c.val →
      ∀ x, x ∉ w.support → G.Adj x u →
        f x = 3 ∧ (f u = 9 ∨ f u = 8 ∨ f u = 6) := by
    intro u hu huc x hx hxu
    obtain ⟨Z, _hZ, huZ, hNx, hNz, _hZdata, _hdegree, hcases⟩ :=
      intro21_even_cycle_external_neighbor_leaf_star
        G b hG hI hn hb r w hw hlen u x hu hx hxu
    have hxc : x ≠ c.val := by
      intro he
      exact hx (he.symm ▸ c.property)
    have hxY : x ∉ Y := by
      intro he
      have hua : u = a.val.val := (hNl x he u).mp hxu
      exact haout (hua ▸ hu)
    have hcount : Z.card = 0 ∨ Z.card = 1 ∨ Z.card = 3 := by
      rcases hcases with h0 | h1 | h3
      · exact Or.inl h0
      · exact Or.inr (Or.inl h1)
      · exact Or.inr (Or.inr h3.1)
    have he := saturated_star_at_cycle_neighbor G eps f hflip hAf c.val u x
      Y Z huc hxc hxY huZ hNx hNz hcount hcol
    exact ⟨he.1, he.2.2.2⟩
  exact ⟨Y, eps, f, hY, hY3, hcY, hNa, hNl, hYout, hs, hflip, hf, hAf,
    ha, hc, hcol, hcstars, hnbrstars⟩
#print axioms Paper7IntroThreeFourExternal.intro21_even_three_leaf_degree_four_external_weights

end Paper7IntroThreeFourExternal
