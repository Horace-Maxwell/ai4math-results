import Research.TaskH.Seven.SevenCommonFourColors

/-! A symbolic finite-label argument, with no mask/graph enumeration.
Same-color intersecting large labels close the actual crossing C7. -/

set_option autoImplicit false
universe u w
namespace TaskH.Seven
open SimpleGraph _root_.TaskH.Challenge
open scoped Classical
variable {V : Type u} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem three_crossing_elements {A : Type w} [DecidableEq A]
    (I J : Finset A) (hI : 2 ≤ I.card) (hJ : 2 ≤ J.card)
    (hinter : (I ∩ J).Nonempty) (hunion : 3 ≤ (I ∪ J).card) :
    ∃ i j k : A, i ≠ j ∧ i ≠ k ∧ j ≠ k ∧ i ∈ I ∧ j ∈ I ∧ j ∈ J ∧ k ∈ J := by
  obtain ⟨j, hj⟩ := hinter
  have hjI := (Finset.mem_inter.mp hj).1
  have hjJ := (Finset.mem_inter.mp hj).2
  obtain ⟨i, hi, hij⟩ := Finset.exists_mem_ne (by omega : 1 < I.card) j
  obtain ⟨k, hk, hkj⟩ := Finset.exists_mem_ne (by omega : 1 < J.card) j
  by_cases hik : i = k
  · subst k
    obtain ⟨l, hl, hli, hlj⟩ : ∃ l : A, l ∈ I ∪ J ∧ l ≠ i ∧ l ≠ j := by
      by_contra! hh
      have hs : I ∪ J ⊆ {i, j} := by
        intro l hl
        by_cases hli : l = i
        · exact Finset.mem_insert.mpr (Or.inl hli)
        · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr (hh l hl hli)))
      have hc := Finset.card_le_card hs
      have hp : ({i, j} : Finset A).card ≤ 2 := Finset.card_le_two
      omega
    rcases Finset.mem_union.mp hl with hlI | hlJ
    · exact ⟨l, j, i, hlj, hli, Ne.symm hij, hlI, hjI, hjJ, hk⟩
    · exact ⟨i, j, l, hij, Ne.symm hli, Ne.symm hlj, hi, hjI, hjJ, hlJ⟩
  · exact ⟨i, j, k, hij, hik, Ne.symm hkj, hi, hjI, hjJ, hk⟩

theorem common_four_big_label_unique
    (hcrit : IsCriticalPlus 7 G) (hc : modCycleCount 7 G = 2880) {v : V}
    {c : (G.induce {x | x ≠ v}).Coloring (Fin 7)}
    (F : DegreeTwelveFrame G v c) (hfour : F.commonColors.card = 4)
    (D : Finset V) (hD : D ⊆ ((insert v (G.neighborFinset v))ᶜ : Finset V))
    (z : V) (hzD : z ∈ D) (hzbig : 3 ≤ (commonPoolHits F z).card)
    (x : V) (hx : x ∈ multiCommonPool F D) : x = z := by
  classical
  by_contra hxz
  have hxD := (Finset.mem_filter.mp hx).1
  have hxmulti := (Finset.mem_filter.mp hx).2
  let I := commonPoolHits F z
  let J := commonPoolHits F x
  change 3 ≤ I.card at hzbig
  change 2 ≤ J.card at hxmulti
  have hu : (I ∪ J).card ≤ 4 := by
    simpa only [Fintype.card_coe, hfour] using (Finset.card_le_univ (I ∪ J))
  have hcIJ := Finset.card_union_add_card_inter I J
  have hinter : (I ∩ J).Nonempty := Finset.card_pos.mp (by omega)
  have hunion : 3 ≤ (I ∪ J).card := by
    have hh := Finset.card_le_card (Finset.subset_union_left : I ⊆ I ∪ J)
    omega
  obtain ⟨i, j, k, hij, hik, hjk, hi, hjI, hjJ, hk⟩ :=
    three_crossing_elements I J (by omega) hxmulti hinter hunion
  have hzout := Finset.mem_compl.mp (hD hzD)
  have hxout := Finset.mem_compl.mp (hD hxD)
  have hzv : z ≠ v := by intro he; exact hzout (Finset.mem_insert.mpr (Or.inl he))
  have hxv : x ≠ v := by intro he; exact hxout (Finset.mem_insert.mpr (Or.inl he))
  obtain ⟨gamma, _hg, hcolor⟩ := common_four_multi_color hcrit hc F hfour
  have hcz := hcolor ⟨z, hzv⟩ hzout (by change 2 ≤ I.card; omega)
  have hcx := hcolor ⟨x, hxv⟩ hxout hxmulti
  exact common_three_rep_crossing_same_color_false (equality_rainbowSevenCycles hcrit hc)
    F i j k hij hik hjk ⟨z, hzv⟩ ⟨x, hxv⟩ hzout hxout (Ne.symm hxz)
    ((mem_commonPoolHits F z i).mp hi) ((mem_commonPoolHits F z j).mp hjI)
    ((mem_commonPoolHits F x j).mp hjJ) ((mem_commonPoolHits F x k).mp hk)
    (hcz.trans hcx.symm)

theorem common_four_incidence_le_card_add_five
    (hcrit : IsCriticalPlus 7 G) (hc : modCycleCount 7 G = 2880)
    (hnot : ¬ IsCompleteOfOrder G 8) {v : V}
    {c : (G.induce {x | x ≠ v}).Coloring (Fin 7)}
    (F : DegreeTwelveFrame G v c) (hfour : F.commonColors.card = 4)
    (D : Finset V) (hD : D ⊆ ((insert v (G.neighborFinset v))ᶜ : Finset V)) :
    (∑ z ∈ D, (commonPoolHits F z).card) ≤ D.card + 5 := by
  classical
  let f : V → ℕ := fun z => (commonPoolHits F z).card
  let M := multiCommonPool F D
  by_cases hbig : ∃ z ∈ D, 3 ≤ f z
  · obtain ⟨z, hz, hzb⟩ := hbig
    have hrow : ∀ x ∈ D.erase z, f x ≤ 1 := by
      intro x hx
      by_contra! hxm
      have hxM : x ∈ M := Finset.mem_filter.mpr
        ⟨(Finset.mem_erase.mp hx).2, by change 2 ≤ f x; omega⟩
      have he := common_four_big_label_unique hcrit hc F hfour D hD z hz hzb x hxM
      exact (Finset.mem_erase.mp hx).1 he
    have hrest : (∑ x ∈ D.erase z, f x) ≤ (D.erase z).card := by
      calc
        _ ≤ ∑ _x ∈ D.erase z, 1 := Finset.sum_le_sum hrow
        _ = _ := by simp
    have hzcap : f z ≤ 4 := by
      simpa only [Fintype.card_coe, hfour] using (Finset.card_le_univ (commonPoolHits F z))
    have hsum := Finset.sum_erase_add D f hz
    have hcard := Finset.card_erase_add_one hz
    change (∑ z ∈ D, f z) ≤ D.card + 5
    omega
  · have hrow : ∀ z ∈ D, f z ≤ 1 + (if z ∈ M then 1 else 0 : ℕ) := by
      intro z hz
      have hsmall : f z ≤ 2 := by
        by_contra! h
        exact hbig ⟨z, hz, by omega⟩
      by_cases hm : z ∈ M
      · rw [ite_eq_left hm]
        omega
      · rw [ite_eq_right hm]
        have hn : ¬ 2 ≤ f z := by intro h; exact hm (Finset.mem_filter.mpr ⟨hz, h⟩)
        omega
    have hfilter : D.filter (fun z => z ∈ M) = M := by
      ext z
      simp only [Finset.mem_filter]
      exact ⟨fun h => h.2, fun h => ⟨(Finset.mem_filter.mp h).1, h⟩⟩
    have hind : (∑ z ∈ D, if z ∈ M then 1 else 0 : ℕ) = M.card := by
      rw [Finset.sum_boole, hfilter, Nat.cast_id]
    have hsum : (∑ z ∈ D, f z) ≤ D.card + M.card := by
      calc
        _ ≤ ∑ z ∈ D, (1 + (if z ∈ M then 1 else 0 : ℕ)) := Finset.sum_le_sum hrow
        _ = _ := by rw [Finset.sum_add_distrib, hind]; simp
    have hM : M.card ≤ 5 := common_four_multi_card_le_five hcrit hc hnot F hfour D hD
    change (∑ z ∈ D, f z) ≤ D.card + 5
    omega

end TaskH.Seven
#print axioms TaskH.Seven.three_crossing_elements
#print axioms TaskH.Seven.common_four_big_label_unique
#print axioms TaskH.Seven.common_four_incidence_le_card_add_five
