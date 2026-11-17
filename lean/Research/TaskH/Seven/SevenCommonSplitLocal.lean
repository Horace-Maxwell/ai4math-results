import Research.TaskH.Seven.SevenRootedFivePaths

/-! Actual common/split local rigidity. The two paths below have five edges
and six distinct root neighbors, then the original root closes a genuine C7. -/

set_option autoImplicit false
universe u
namespace TaskH.Seven
open SimpleGraph _root_.TaskH.Challenge
open scoped Classical
variable {V : Type u} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem degreeTwelve_common_split_extra_edge_false
    (hcrit : IsCriticalPlus 7 G) (hc : modCycleCount 7 G = 2880)
    (hnot : ¬ IsCompleteOfOrder G 8) {v : V}
    {c : (G.induce {x | x ≠ v}).Coloring (Fin 7)} (hv : G.degree v = 12)
    (F : DegreeTwelveFrame G v c)
    (gamma rho : Fin 5) (hgr : gamma ≠ rho)
    (ep eq er : Fin 2) (hpq : ep ≠ eq)
    (hap : G.Adj (F.center 0).val (F.leaf gamma ep).val)
    (hbq : G.Adj (F.center 1).val (F.leaf gamma eq).val)
    (har : G.Adj (F.center 0).val (F.leaf rho er).val)
    (hbr : G.Adj (F.center 1).val (F.leaf rho er).val)
    (j : Fin 5) (hjg : j ≠ gamma) (et : Fin 2)
    (hpt : G.Adj (F.leaf gamma ep).val (F.leaf j et).val) : False := by
  let a := F.center 0
  let b := F.center 1
  let p := F.leaf gamma ep
  let q := F.leaf gamma eq
  let r := F.leaf rho er
  let t := F.leaf j et
  have hab : a ≠ b := by
    intro he
    exact F.center_center_ne (by decide : (0 : Fin 2) ≠ 1) (congrArg Subtype.val he)
  have hcp : ∀ k : Fin 2, ∀ i : Fin 5, ∀ e : Fin 2,
      F.center k ≠ F.leaf i e := by
    intro k i e he
    exact F.center_leaf_ne k i e (congrArg Subtype.val he)
  have hlp : ∀ {i j : Fin 5}, i ≠ j → ∀ e d : Fin 2,
      F.leaf i e ≠ F.leaf j d := by
    intro i j hij e d he
    exact F.leaf_leaf_ne hij e d (congrArg Subtype.val he)
  have hpqn : p ≠ q := by
    intro he
    exact hpq (F.leaf_same_pair_injective gamma (congrArg Subtype.val he))
  have hpr : p ≠ r := hlp hgr ep er
  have hqr : q ≠ r := hlp hgr eq er
  have htp : t ≠ p := hlp hjg et ep
  have htq : t ≠ q := hlp hjg et eq
  have hapn : a ≠ p := hcp 0 gamma ep
  have haqn : a ≠ q := hcp 0 gamma eq
  have harn : a ≠ r := hcp 0 rho er
  have hatn : a ≠ t := hcp 0 j et
  have hbpn : b ≠ p := hcp 1 gamma ep
  have hbqn : b ≠ q := hcp 1 gamma eq
  have hbrn : b ≠ r := hcp 1 rho er
  have hbtn : b ≠ t := hcp 1 j et
  have hcolor : neighborColor v c p = neighborColor v c q := by
    exact (F.leaf_color gamma ep).trans (F.leaf_color gamma eq).symm
  have hr : RainbowSevenCycles G := equality_rainbowSevenCycles hcrit hc
  by_cases htr : t = r
  · have hprEdge : G.Adj p.val r.val := by
      change G.Adj p.val t.val at hpt
      rw [htr] at hpt
      exact hpt
    obtain ⟨eta, heg, her⟩ : ∃ eta : Fin 5, eta ≠ gamma ∧ eta ≠ rho := by
      by_contra! hh
      have hsub : (Finset.univ : Finset (Fin 5)) ⊆ {gamma, rho} := by
        intro i _hi
        by_cases hig : i = gamma
        · exact Finset.mem_insert.mpr (Or.inl hig)
        · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr (hh i hig)))
      have hle := Finset.card_le_card hsub
      have hpair : ({gamma, rho} : Finset (Fin 5)).card ≤ 2 := Finset.card_le_two
      have hfive : 5 ≤ ({gamma, rho} : Finset (Fin 5)).card := by
        simpa only [Finset.card_univ, Fintype.card_fin] using hle
      omega
    obtain ⟨eu, hau⟩ := F.center_meets_pair hcrit hc hnot hv 0 eta
    let u := F.leaf eta eu
    have hua : u ≠ a := Ne.symm (hcp 0 eta eu)
    have hub : u ≠ b := Ne.symm (hcp 1 eta eu)
    have hup : u ≠ p := hlp heg eu ep
    have huq : u ≠ q := hlp heg eu eq
    have hur : u ≠ r := hlp her eu er
    let f : Fin 6 → G.neighborSet v := ![q, b, r, p, a, u]
    have hf : Function.Injective f := by
      change Function.Injective ![q, b, r, p, a, u]
      unfold Matrix.vecCons
      refine Fin.cons_injective_of_injective ?_ ?_
      · simpa only [Fin.range_cons, Matrix.range_empty, Set.mem_insert_iff,
          Set.mem_empty_iff_false, or_false, not_or] using
          (show q ≠ b ∧ q ≠ r ∧ q ≠ p ∧ q ≠ a ∧ q ≠ u from
            ⟨Ne.symm hbqn, hqr, Ne.symm hpqn, Ne.symm haqn, Ne.symm huq⟩)
      refine Fin.cons_injective_of_injective ?_ ?_
      · simpa only [Fin.range_cons, Matrix.range_empty, Set.mem_insert_iff,
          Set.mem_empty_iff_false, or_false, not_or] using
          (show b ≠ r ∧ b ≠ p ∧ b ≠ a ∧ b ≠ u from
            ⟨hbrn, hbpn, Ne.symm hab, Ne.symm hub⟩)
      refine Fin.cons_injective_of_injective ?_ ?_
      · simpa only [Fin.range_cons, Matrix.range_empty, Set.mem_insert_iff,
          Set.mem_empty_iff_false, or_false, not_or] using
          (show r ≠ p ∧ r ≠ a ∧ r ≠ u from
            ⟨Ne.symm hpr, Ne.symm harn, Ne.symm hur⟩)
      refine Fin.cons_injective_of_injective ?_ ?_
      · simpa only [Fin.range_cons, Matrix.range_empty, Set.mem_insert_iff,
          Set.mem_empty_iff_false, or_false, not_or] using
          (show p ≠ a ∧ p ≠ u from ⟨Ne.symm hapn, Ne.symm hup⟩)
      exact injective_pair_iff_ne.mpr (Ne.symm hua)
    have hcol : neighborColor v c (f 0) = neighborColor v c (f 3) := hcolor.symm
    exact neighbor_five_path_same_color_false hr v c f hf hbq.symm hbr
      hprEdge.symm hap.symm hau 0 3 (by decide) hcol
  · let f : Fin 6 → G.neighborSet v := ![t, p, a, r, b, q]
    have hf : Function.Injective f := by
      change Function.Injective ![t, p, a, r, b, q]
      unfold Matrix.vecCons
      refine Fin.cons_injective_of_injective ?_ ?_
      · simpa only [Fin.range_cons, Matrix.range_empty, Set.mem_insert_iff,
          Set.mem_empty_iff_false, or_false, not_or] using
          (show t ≠ p ∧ t ≠ a ∧ t ≠ r ∧ t ≠ b ∧ t ≠ q from
            ⟨htp, Ne.symm hatn, htr, Ne.symm hbtn, htq⟩)
      refine Fin.cons_injective_of_injective ?_ ?_
      · simpa only [Fin.range_cons, Matrix.range_empty, Set.mem_insert_iff,
          Set.mem_empty_iff_false, or_false, not_or] using
          (show p ≠ a ∧ p ≠ r ∧ p ≠ b ∧ p ≠ q from
            ⟨Ne.symm hapn, hpr, Ne.symm hbpn, hpqn⟩)
      refine Fin.cons_injective_of_injective ?_ ?_
      · simpa only [Fin.range_cons, Matrix.range_empty, Set.mem_insert_iff,
          Set.mem_empty_iff_false, or_false, not_or] using
          (show a ≠ r ∧ a ≠ b ∧ a ≠ q from ⟨harn, hab, haqn⟩)
      refine Fin.cons_injective_of_injective ?_ ?_
      · simpa only [Fin.range_cons, Matrix.range_empty, Set.mem_insert_iff,
          Set.mem_empty_iff_false, or_false, not_or] using
          (show r ≠ b ∧ r ≠ q from ⟨Ne.symm hbrn, Ne.symm hqr⟩)
      exact injective_pair_iff_ne.mpr hbqn
    have hcol : neighborColor v c (f 1) = neighborColor v c (f 5) := hcolor
    exact neighbor_five_path_same_color_false hr v c f hf hpt.symm hap.symm har
      hbr.symm hbq 1 5 (by decide) hcol


theorem degreeTwelve_common_split_both_leaves_no_extra_edges
    (hcrit : IsCriticalPlus 7 G) (hc : modCycleCount 7 G = 2880)
    (hnot : ¬ IsCompleteOfOrder G 8) {v : V}
    {c : (G.induce {x | x ≠ v}).Coloring (Fin 7)} (hv : G.degree v = 12)
    (F : DegreeTwelveFrame G v c)
    (gamma rho : Fin 5) (hgr : gamma ≠ rho)
    (ep eq er : Fin 2) (hpq : ep ≠ eq)
    (hap : G.Adj (F.center 0).val (F.leaf gamma ep).val)
    (hbq : G.Adj (F.center 1).val (F.leaf gamma eq).val)
    (har : G.Adj (F.center 0).val (F.leaf rho er).val)
    (hbr : G.Adj (F.center 1).val (F.leaf rho er).val)
    (j : Fin 5) (hjg : j ≠ gamma) (et : Fin 2) :
    ¬ G.Adj (F.leaf gamma ep).val (F.leaf j et).val ∧
      ¬ G.Adj (F.leaf gamma eq).val (F.leaf j et).val := by
  refine ⟨fun he => degreeTwelve_common_split_extra_edge_false hcrit hc hnot hv
    F gamma rho hgr ep eq er hpq hap hbq har hbr j hjg et he, ?_⟩
  intro he
  have hsa : G.Adj (F.swapCenters.center 0).val (F.swapCenters.leaf gamma eq).val := by
    simpa only [F.swapCenters_center_zero, F.swapCenters_leaf] using hbq
  have hsb : G.Adj (F.swapCenters.center 1).val (F.swapCenters.leaf gamma ep).val := by
    simpa only [F.swapCenters_center_one, F.swapCenters_leaf] using hap
  have hsra : G.Adj (F.swapCenters.center 0).val (F.swapCenters.leaf rho er).val := by
    simpa only [F.swapCenters_center_zero, F.swapCenters_leaf] using hbr
  have hsrb : G.Adj (F.swapCenters.center 1).val (F.swapCenters.leaf rho er).val := by
    simpa only [F.swapCenters_center_one, F.swapCenters_leaf] using har
  exact degreeTwelve_common_split_extra_edge_false hcrit hc hnot hv F.swapCenters
    gamma rho hgr eq ep er (Ne.symm hpq) hsa hsb hsra hsrb j hjg et he


theorem degreeTwelve_common_split_leaf_internal_neighbor_iff
    (hcrit : IsCriticalPlus 7 G) (hc : modCycleCount 7 G = 2880)
    (hnot : ¬ IsCompleteOfOrder G 8) {v : V}
    {c : (G.induce {x | x ≠ v}).Coloring (Fin 7)} (hv : G.degree v = 12)
    (F : DegreeTwelveFrame G v c)
    (gamma rho : Fin 5) (hgr : gamma ≠ rho)
    (ep eq er : Fin 2) (hpq : ep ≠ eq)
    (hap : G.Adj (F.center 0).val (F.leaf gamma ep).val)
    (hbp : ¬ G.Adj (F.center 1).val (F.leaf gamma ep).val)
    (hbq : G.Adj (F.center 1).val (F.leaf gamma eq).val)
    (har : G.Adj (F.center 0).val (F.leaf rho er).val)
    (hbr : G.Adj (F.center 1).val (F.leaf rho er).val)
    (z : G.neighborSet v) :
    G.Adj (F.leaf gamma ep).val z.val ↔ z = F.center 0 := by
  constructor
  · intro hpz
    rcases F.neighbor_cases z with ⟨j, rfl⟩ | ⟨i, e, rfl⟩
    · fin_cases j
      · rfl
      · exact (hbp hpz.symm).elim
    · by_cases hig : i = gamma
      · subst i
        exact (F.leaf_same_pair_not_adj gamma ep e hpz).elim
      · exact (degreeTwelve_common_split_extra_edge_false hcrit hc hnot hv F
          gamma rho hgr ep eq er hpq hap hbq har hbr i hig e hpz).elim
  · intro hz
    rw [hz]
    exact hap.symm

end TaskH.Seven
#print axioms TaskH.Seven.degreeTwelve_common_split_extra_edge_false

#print axioms TaskH.Seven.degreeTwelve_common_split_both_leaves_no_extra_edges

#print axioms TaskH.Seven.degreeTwelve_common_split_leaf_internal_neighbor_iff
