import Research.Backfill.Paper7.IntroThreeLeafDegreeThreeFourthCorrection
import Research.Backfill.Paper7.IntroThreeLeafNonfourSideBudget

/-! Original m3,d3 exclusion candidate. The fourth-correction witness and
nonfour budget parent remain pending until their actual successful producers
are bound. This file introduces no extra original-graph premise. -/
set_option autoImplicit false
noncomputable section
open scoped Classical Matrix BigOperators

namespace Paper7IntroThreeThreeExclusion
open SimpleGraph Matrix BackfillPaper7.Challenge
open BackfillPaper7.Challenge.Legacy.Algebra
open Paper7IntroThreeLeafFourthCorrection Paper7IntroThreeLeafNonfourBudget
open Paper7IntroTwoStepTopology Paper7ThreeLeafDegreeThreeBudget

theorem intro21_even_not_three_leaf_degree_three
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (b : ℕ)
    (hG : IsUnicyclicWithCycle G b) (hI : IsIntegralGraph G)
    (hn : Fintype.card V ≤ 21) (hb : Even b)
    (r : V) (w : G.Walk r r) (hw : w.IsCycle) (hlen : w.length = b)
    (C : (deleteVertices G {q | q ∈ w.support}).ConnectedComponent)
    (a : C.supp) (c : {q : V // q ∈ w.support}) (hac : G.Adj a.val.val c.val)
    (hm : ((G.neighborFinset a.val.val).erase c.val).card = 3)
    (hd : G.degree c.val = 3) :
    False := by
  obtain ⟨Y, i₀, eps, f, z, _hY, _hmY, _hda, _hne, hdata, _hcover, hNa, _hNl,
    _hs, hflip, _hf, hAf, _h₀, _hweights, ha, _hc, hsgn, hcs, _hproj, _hN, hz,
    _hsame, hopp, _hsumU, hsumW, _hexternal,
    u, v, s, t, K, J, hu, hv, huv, hcu, hcv, _hNc, _hfullc, _huW, _hvW, hsumZ,
    hsC, hsc, hus, hfullu, htC, htc, hvt, hfullv, hK, hJ, _hKmem, _hJmem,
    _hNu, _hNv, _hKleaf, _hJleaf, _hKsum, _hJsum, hfs, hft, _hm4, hcount⟩ :=
    intro21_even_three_leaf_degree_three_fourth_correction G b hG hI hn hb
      r w hw hlen C a c hac hm hd
  by_cases hb4 : b = 4
  · obtain ⟨j, hj, hjc, _hju, _hjv, huj, hvj, _hnotcj, _hsupp, _hcommon,
        _hfilter, _hA2, _hA2rev, _hjcomplete⟩ :=
      unicyclic_four_circle_from_neighbors G b hG r w hw hlen hb4
        c.val u v c.property hu hv huv hcu hcv
    have hjs : j = s := ((hfullu j hj).mp huj).resolve_left hjc
    have hjt : j = t := ((hfullv j hj).mp hvj).resolve_left hjc
    have hst : s = t := hjs.symm.trans hjt
    have hkj : K.card + J.card = 4 := by
      simpa only [hb4, ↓reduceIte] using hcount
    have hkjR : (K.card : ℝ) + (J.card : ℝ) = 4 := by exact_mod_cast hkj
    have hxyR : (z u : ℝ) + (z v : ℝ) = 5 := by exact_mod_cast hsumZ
    have hjR : (J.card : ℝ) = 4 - (K.card : ℝ) := by linarith only [hkjR]
    have hyR : (z v : ℝ) = 5 - (z u : ℝ) := by linarith only [hxyR]
    have hrows := hfs
    rw [hst, hft, hjR, hyR] at hrows
    have hidentityR : 14 * (z u : ℝ) - 25 = 5 * (K.card : ℝ) := by
      nlinarith only [hrows]
    have hidentity : 14 * z u - 25 = 5 * (K.card : ℤ) := by
      exact_mod_cast hidentityR
    exact four_cycle_integer_contradiction (z u) (z v) (K.card : ℤ)
      (hz u) (hz v) hsumZ hidentity
  · have hc_same : eps c.val = eps i₀.val := by linarith only [hcs, hsgn i₀]
    have haW : eps a.val.val = -eps c.val := by linarith only [hcs]
    have hscale : ∀ x, eps x = -eps c.val → f x = 3 * (z x : ℝ) := by
      intro x hx
      apply hopp x
      rw [← hc_same]
      exact hx
    have hside : (∑ x, if eps x = -eps c.val then z x ^ 2 else 0) = 20 := by
      simpa only [hc_same] using hsumW
    have hNa' : G.neighborFinset a.val.val = insert c.val Y := by
      ext q
      simp only [SimpleGraph.mem_neighborFinset, Finset.mem_insert]
      rw [hNa q]
      constructor
      · rintro (hqc | ⟨i, hqi⟩)
        · exact Or.inl hqc
        · exact Or.inr (hqi.symm ▸ i.property)
      · rintro (hqc | hqY)
        · exact Or.inl hqc
        · exact Or.inr ⟨⟨q, hqY⟩, rfl⟩
    have hYout : ∀ x ∈ Y, x ∉ w.support := by
      intro x hx
      obtain ⟨y, hy⟩ := (hdata ⟨x, hx⟩).1
      change y.val.val = x at hy
      rw [← hy]
      exact y.val.property
    have hkj : K.card + J.card = 6 := by
      simpa only [hb4, ↓reduceIte] using hcount
    rcases le_total (z u) (z v) with horder | horder
    · exact three_leaf_nonfour_same_witness_budget_contradiction
        G b hG r w hw hlen hb4 eps f z hflip hAf hz
        a.val.val c.val u v s t Y K J a.val.property hu hv hsC htC
        huv hsc htc hcu hcv hus hvt hNa' hYout haW ha hscale hside
        hsumZ horder hK hJ hkj hfs hft
    · have hsumZ' : z v + z u = 5 := by omega
      have hkj' : J.card + K.card = 6 := by omega
      exact three_leaf_nonfour_same_witness_budget_contradiction
        G b hG r w hw hlen hb4 eps f z hflip hAf hz
        a.val.val c.val v u t s Y J K a.val.property hv hu htC hsC
        huv.symm htc hsc hcv hcu hvt hus hNa' hYout haW ha hscale hside
        hsumZ' horder hJ hK hkj' hft hfs
#print axioms Paper7IntroThreeThreeExclusion.intro21_even_not_three_leaf_degree_three

end Paper7IntroThreeThreeExclusion
