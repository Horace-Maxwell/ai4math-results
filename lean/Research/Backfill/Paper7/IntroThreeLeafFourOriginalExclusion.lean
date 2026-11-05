import Research.Backfill.Paper7.IntroThreeLeafFourNeighborAlternatives
import Research.Backfill.Paper7.IntroUnicyclicCircleTwoStep

/-! Original m3,d4 exclusion candidate. Both cycle cases retain the same
Perron witness. Pending parents are not successful proof dependencies yet. -/
set_option autoImplicit false
noncomputable section
open scoped Classical Matrix BigOperators

namespace Paper7IntroThreeFourExclusion
open SimpleGraph Matrix BackfillPaper7.Challenge
open BackfillPaper7.Challenge.Legacy.Algebra
open Paper7IntroThreeFourNeighborSum Paper7IntroThreeFourAlternatives
open Paper7IntroTwoStepTopology Paper7IntroExternalLeafStar Paper7IntroFourCycleWeights

theorem intro21_even_not_three_leaf_degree_four
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (b : ℕ)
    (hG : IsUnicyclicWithCycle G b) (hI : IsIntegralGraph G)
    (hn : Fintype.card V ≤ 21) (hb : Even b)
    (r : V) (w : G.Walk r r) (hw : w.IsCycle) (hlen : w.length = b)
    (C : (deleteVertices G {q | q ∈ w.support}).ConnectedComponent)
    (a : C.supp) (c : {q : V // q ∈ w.support}) (hac : G.Adj a.val.val c.val)
    (hm : ((G.neighborFinset a.val.val).erase c.val).card = 3)
    (hd : G.degree c.val = 4) :
    False := by
  obtain ⟨Y, eps, f, u, v, _hY, _hY3, _hcY, hNa, hNl, hYout, _hs, hflip,
      hf, hAf, _hfa, hfc, hcol, hcstars, hnbrstars, hu, hv, huv, hcu, hcv,
      _hcomplete, hsum⟩ :=
    intro21_even_three_leaf_degree_four_cycle_neighbor_sum
      G b hG hI hn hb r w hw hlen C a c hac hm hd
  by_cases hb4 : b = 4
  · obtain ⟨j, hj, hjc, _hju, _hjv, huj, _hvj, _hnotcj, _hsupp, _hcommon,
        _hfilter, _hA2, hA2rev, hjcomplete⟩ :=
      unicyclic_four_circle_from_neighbors G b hG r w hw hlen hb4
        c.val u v c.property hu hv huv hcu hcv
    have hepsj : eps j = eps c.val := by
      linarith only [hflip j u huj.symm, hflip u c.val hcu.symm]
    have hjY : j ∉ Y := by
      intro he
      exact hYout j he hj
    have hfj : f j = 6 := by
      have he := hcol j hepsj hjc hjY
      rw [hA2rev] at he
      norm_num at he
      exact he
    have houtside : ∀ x, x ∉ w.support → G.Adj x j → f x = 2 := by
      intro x hx hxj
      have hxa : x ≠ a.val.val := by
        intro he
        have hjN : j ∈ G.neighborFinset a.val.val :=
          (G.mem_neighborFinset a.val.val j).mpr (he ▸ hxj)
        rw [hNa] at hjN
        rcases Finset.mem_insert.mp hjN with hjc' | hjY'
        · exact hjc hjc'
        · exact hYout j hjY' hj
      have hnotxc : ¬ G.Adj x c.val := by
        intro hxc
        have hNx := (hcstars x hx hxa hxc).1
        have hjN : j ∈ G.neighborFinset x := (G.mem_neighborFinset x j).mpr hxj
        rw [hNx] at hjN
        exact hjc (Finset.mem_singleton.mp hjN)
      obtain ⟨Z, _hZ, _hjZ, hNx, hNz, hZdata, _hdegree, _hcases⟩ :=
        intro21_even_cycle_external_neighbor_leaf_star
          G b hG hI hn hb r w hw hlen j x hj hx hxj
      have hZempty : Z = ∅ := by
        apply Finset.not_nonempty_iff_eq_empty.mp
        rintro ⟨z, hz⟩
        have hzx : G.Adj z x := (hNz z hz x).mpr rfl
        have hzc : z ≠ c.val := by
          intro he
          exact (hZdata z hz).1 (he.symm ▸ c.property)
        have hzY : z ∉ Y := by
          intro he
          exact hxa ((hNl z he x).mp hzx)
        have hepsz : eps z = eps c.val := by
          linarith only [hflip z x hzx, hflip x j hxj, hepsj]
        have hentry : ((G.adjMatrix ℝ) ^ 2) z c.val = 0 := by
          have he := (actual_leaf_square_entry G z x c.val (hNz z hz)).2
          simpa only [hnotxc, ↓reduceIte] using he
        have hzcol := hcol z hepsz hzc hzY
        rw [hentry, mul_zero] at hzcol
        have hzpos := hf z
        linarith only [hzcol, hzpos]
      have hsingle : G.neighborFinset x = {j} := by
        simpa only [hZempty, Finset.insert_empty] using hNx
      have hrow : f j = 3 * f x := by
        simpa only [G.adjMatrix_mulVec_apply, hsingle, Finset.sum_singleton,
          Pi.smul_apply, smul_eq_mul] using congrFun hAf x
      linarith only [hrow, hfj]
    let N := G.neighborFinset j
    have huN : u ∈ N := by
      apply (G.mem_neighborFinset j u).mpr
      exact (hjcomplete u hu).mpr (Or.inl rfl)
    have hvN : v ∈ N := by
      apply (G.mem_neighborFinset j v).mpr
      exact (hjcomplete v hv).mpr (Or.inr rfl)
    have hvNu : v ∈ N.erase u := Finset.mem_erase.mpr ⟨huv.symm, hvN⟩
    let E := (N.erase u).erase v
    have hEweight : ∀ x ∈ E, f x = 2 := by
      intro x hxE
      obtain ⟨hxv, hxuN⟩ := Finset.mem_erase.mp hxE
      obtain ⟨hxu, hxN⟩ := Finset.mem_erase.mp hxuN
      have hxout : x ∉ w.support := by
        intro hxS
        rcases (hjcomplete x hxS).mp ((G.mem_neighborFinset j x).mp hxN) with he | he
        · exact hxu he
        · exact hxv he
      exact houtside x hxout ((G.mem_neighborFinset j x).mp hxN).symm
    have hEsum : (∑ x ∈ E, f x) = (E.card : ℝ) * 2 := by
      calc
        (∑ x ∈ E, f x) = ∑ _x ∈ E, (2 : ℝ) :=
          Finset.sum_congr rfl (fun x hx => hEweight x hx)
        _ = _ := by simp
    have h1 := Finset.sum_erase_add N f huN
    have h2 := Finset.sum_erase_add (N.erase u) f hvNu
    have hrow : (∑ x ∈ N, f x) = 3 * f j := by
      simpa only [N, G.adjMatrix_mulVec_apply, Pi.smul_apply, smul_eq_mul]
        using congrFun hAf j
    change (∑ x ∈ (N.erase u).erase v, f x) = (E.card : ℝ) * 2 at hEsum
    have hcardR : 2 * (E.card : ℝ) = 5 := by
      linarith only [h1, h2, hEsum, hrow, hfj, hsum]
    have hcard : 2 * E.card = 5 := by exact_mod_cast hcardR
    omega
  · have hclass : ∀ p, p ∈ w.support → G.Adj c.val p →
        f p = 3 ∨ f p = 6 ∨ f p = 8 ∨ f p = 9 := by
      intro p hp hcp
      obtain ⟨j, hj, hjc, _hjp, hpj, hpcomplete, _hcommon, _hfilter, _hA2, hA2rev⟩ :=
        unicyclic_nonfour_circle_continuation G b hG r w hw hlen hb4
          c.val p c.property hp hcp
      have hepsj : eps j = eps c.val := by
        linarith only [hflip j p hpj.symm, hflip p c.val hcp.symm]
      have hjY : j ∉ Y := by
        intro he
        exact hYout j he hj
      have hfj : f j = 3 := by
        have he := hcol j hepsj hjc hjY
        rw [hA2rev, mul_one] at he
        exact he
      have he := cycle_neighbor_weight_alternatives G f hAf {q | q ∈ w.support}
        p c.val j hjc.symm hcp.symm hpj hpcomplete hfc
        (hnbrstars p hp hcp.symm)
      exact he.1 hfj
    have huclass := hclass u hu hcu
    have hvclass := hclass v hv hcv
    rcases huclass with hu' | hu' | hu' | hu' <;>
      rcases hvclass with hv' | hv' | hv' | hv' <;>
      linarith only [hsum, hu', hv']
#print axioms Paper7IntroThreeFourExclusion.intro21_even_not_three_leaf_degree_four

end Paper7IntroThreeFourExclusion
