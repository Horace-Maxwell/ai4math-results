import Research.Backfill.Paper7.IntroThreeLeafFourExternalWeights
import Research.Backfill.Paper7.IntroUnicyclicCycleCompleteNeighbors

/-! Same actual m3,d4 witness: the two actual cycle neighbors have weight sum 13.
This source adds no graph hypotheses and does not yet exclude the branch. -/
set_option autoImplicit false
noncomputable section
open scoped Classical Matrix BigOperators

namespace Paper7IntroThreeFourNeighborSum
open SimpleGraph Matrix BackfillPaper7.Challenge
open BackfillPaper7.Challenge.Legacy.Algebra
open Paper7IntroThreeFourExternal Paper7IntroCycleCompleteNeighbors

theorem degree_four_cycle_neighbor_sum
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (f : V → ℝ)
    (hAf : G.adjMatrix ℝ *ᵥ f = (3 : ℝ) • f)
    (S : Set V) (a c u v : V) (haout : a ∉ S)
    (hu : u ∈ S) (hv : v ∈ S) (huv : u ≠ v)
    (hca : G.Adj c a) (hcu : G.Adj c u) (hcv : G.Adj c v)
    (hcomplete : ∀ x, x ∈ S → (G.Adj c x ↔ x = u ∨ x = v))
    (hd : G.degree c = 4) (hfa : f a = 3) (hfc : f c = 6)
    (hother : ∀ x, x ∉ S → x ≠ a → G.Adj x c → f x = 2) :
    f u + f v = 13 := by
  let N := G.neighborFinset c
  have huN : u ∈ N := (G.mem_neighborFinset c u).mpr hcu
  have hvN : v ∈ N := (G.mem_neighborFinset c v).mpr hcv
  have haN : a ∈ N := (G.mem_neighborFinset c a).mpr hca
  have hau : a ≠ u := by
    intro he
    exact haout (he.symm ▸ hu)
  have hav : a ≠ v := by
    intro he
    exact haout (he.symm ▸ hv)
  have hvNu : v ∈ N.erase u := Finset.mem_erase.mpr ⟨huv.symm, hvN⟩
  have haNuv : a ∈ (N.erase u).erase v :=
    Finset.mem_erase.mpr ⟨hav, Finset.mem_erase.mpr ⟨hau, haN⟩⟩
  let E := ((N.erase u).erase v).erase a
  have hN4 : N.card = 4 := by
    simpa only [N, G.card_neighborFinset_eq_degree] using hd
  have hEc : E.card = 1 := by
    have h1 := Finset.card_erase_of_mem huN
    have h2 := Finset.card_erase_of_mem hvNu
    have h3 := Finset.card_erase_of_mem haNuv
    change (((N.erase u).erase v).erase a).card = 1
    omega
  have hEweight : ∀ x ∈ E, f x = 2 := by
    intro x hx
    obtain ⟨hxa, hxuv⟩ := Finset.mem_erase.mp hx
    obtain ⟨hxv, hxu⟩ := Finset.mem_erase.mp hxuv
    obtain ⟨hxu', hxN⟩ := Finset.mem_erase.mp hxu
    have hxout : x ∉ S := by
      intro hxS
      rcases (hcomplete x hxS).mp ((G.mem_neighborFinset c x).mp hxN) with he | he
      · exact hxu' he
      · exact hxv he
    exact hother x hxout hxa ((G.mem_neighborFinset c x).mp hxN).symm
  have hEsum : (∑ x ∈ E, f x) = 2 := by
    calc
      (∑ x ∈ E, f x) = ∑ _x ∈ E, (2 : ℝ) :=
        Finset.sum_congr rfl (fun x hx => hEweight x hx)
      _ = 2 := by simp [hEc]
  have h1 := Finset.sum_erase_add N f huN
  have h2 := Finset.sum_erase_add (N.erase u) f hvNu
  have h3 := Finset.sum_erase_add ((N.erase u).erase v) f haNuv
  have hrow : (∑ x ∈ N, f x) = 3 * f c := by
    simpa only [N, G.adjMatrix_mulVec_apply, Pi.smul_apply, smul_eq_mul]
      using congrFun hAf c
  change (∑ x ∈ ((N.erase u).erase v).erase a, f x) = 2 at hEsum
  linarith only [h1, h2, h3, hEsum, hrow, hfa, hfc]
#print axioms Paper7IntroThreeFourNeighborSum.degree_four_cycle_neighbor_sum

theorem intro21_even_three_leaf_degree_four_cycle_neighbor_sum
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (b : ℕ)
    (hG : IsUnicyclicWithCycle G b) (hI : IsIntegralGraph G)
    (hn : Fintype.card V ≤ 21) (hb : Even b)
    (r : V) (w : G.Walk r r) (hw : w.IsCycle) (hlen : w.length = b)
    (C : (deleteVertices G {q | q ∈ w.support}).ConnectedComponent)
    (a : C.supp) (c : {q : V // q ∈ w.support}) (hac : G.Adj a.val.val c.val)
    (hm : ((G.neighborFinset a.val.val).erase c.val).card = 3)
    (hd : G.degree c.val = 4) :
    ∃ (Y : Finset V) (eps f : V → ℝ) (u v : V),
      Y = (G.neighborFinset a.val.val).erase c.val ∧ Y.card = 3 ∧
      c.val ∉ Y ∧ G.neighborFinset a.val.val = insert c.val Y ∧
      (∀ y ∈ Y, ∀ z, G.Adj y z ↔ z = a.val.val) ∧
      (∀ y ∈ Y, y ∉ w.support) ∧
      (∀ z, eps z = 1 ∨ eps z = -1) ∧
      (∀ x z, G.Adj x z → eps x = -eps z) ∧
      (∀ z, 0 < f z) ∧ G.adjMatrix ℝ *ᵥ f = (3 : ℝ) • f ∧
      f a.val.val = 3 ∧ f c.val = 6 ∧
      (∀ t, eps t = eps c.val → t ≠ c.val → t ∉ Y →
        f t = 3 * ((G.adjMatrix ℝ) ^ 2) t c.val) ∧
      (∀ x, x ∉ w.support → x ≠ a.val.val → G.Adj x c.val →
        G.neighborFinset x = {c.val} ∧ G.degree x = 1 ∧ f x = 2) ∧
      (∀ z, z ∈ w.support → G.Adj z c.val →
        ∀ x, x ∉ w.support → G.Adj x z →
          f x = 3 ∧ (f z = 9 ∨ f z = 8 ∨ f z = 6)) ∧
      u ∈ w.support ∧ v ∈ w.support ∧ u ≠ v ∧
      G.Adj c.val u ∧ G.Adj c.val v ∧
      (∀ z, z ∈ w.support → (G.Adj c.val z ↔ z = u ∨ z = v)) ∧
      f u + f v = 13 := by
  obtain ⟨Y, eps, f, hY, hY3, hcY, hNa, hNl, hYout, hs, hflip, hf, hAf,
      hfa, hfc, hcol, hcstars, hnbrstars⟩ :=
    intro21_even_three_leaf_degree_four_external_weights
      G b hG hI hn hb r w hw hlen C a c hac hm hd
  obtain ⟨u, v, hu, hv, huv, hcu, hcv, hcomplete⟩ :=
    unicyclic_cycle_two_neighbors_complete G b hG r w hw hlen c.val c.property
  have hsum : f u + f v = 13 :=
    degree_four_cycle_neighbor_sum G f hAf {q | q ∈ w.support}
      a.val.val c.val u v a.val.property hu hv huv hac.symm hcu hcv hcomplete
      hd hfa hfc (fun x hx hxa hxc => (hcstars x hx hxa hxc).2.2)
  exact ⟨Y, eps, f, u, v, hY, hY3, hcY, hNa, hNl, hYout, hs, hflip, hf, hAf,
    hfa, hfc, hcol, hcstars, hnbrstars, hu, hv, huv, hcu, hcv, hcomplete, hsum⟩
#print axioms Paper7IntroThreeFourNeighborSum.intro21_even_three_leaf_degree_four_cycle_neighbor_sum

end Paper7IntroThreeFourNeighborSum
