import Research.TaskH.Seven.SevenSplitPoolIncidence

/-! A selected actual common representative has no edge to any split leaf,
and its outside neighbors have no split-leaf incidence. -/

set_option autoImplicit false
universe u
namespace TaskH.Seven
open SimpleGraph _root_.TaskH.Challenge
open scoped Classical
variable {V : Type u} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem split_leaf_not_adj_commonRep
    (hcrit : IsCriticalPlus 7 G) (hc : modCycleCount 7 G = 2880)
    (hnot : ¬ IsCompleteOfOrder G 8) {v : V}
    {c : (G.induce {x | x ≠ v}).Coloring (Fin 7)} (hv : G.degree v = 12)
    (F : DegreeTwelveFrame G v c) (gamma : Fin 5) (hg : gamma ∉ F.commonColors)
    (rho : ↥F.commonColors) (e : Fin 2) :
    ¬ G.Adj (F.leaf gamma e).val (F.commonRep rho).val := by
  have hgr : gamma ≠ rho.val := by intro he; exact hg (he.symm ▸ rho.property)
  let er : Fin 2 := Classical.choose (Finset.mem_filter.mp rho.property).2
  have hra : G.Adj (F.center 0).val (F.leaf rho.val er).val := F.commonRep_adj_zero rho
  have hrb : G.Adj (F.center 1).val (F.leaf rho.val er).val := F.commonRep_adj_one rho
  have hs := F.splitPair_of_not_common hcrit hc hnot hv gamma hg
  rcases hs with h | h
  · have H := degreeTwelve_common_split_both_leaves_no_extra_edges hcrit hc hnot hv F
      gamma rho.val hgr 0 1 er (by decide) h.1 h.2.2.1 hra hrb rho.val (Ne.symm hgr) er
    fin_cases e
    · exact H.1
    · exact H.2
  · have H := degreeTwelve_common_split_both_leaves_no_extra_edges hcrit hc hnot hv F
      gamma rho.val hgr 1 0 er (by decide) h.1 h.2.2.1 hra hrb rho.val (Ne.symm hgr) er
    fin_cases e
    · exact H.2
    · exact H.1

theorem common_split_outside_overlap_at_zero_false
    (hr : RainbowSevenCycles G) {v : V}
    {c : (G.induce {x | x ≠ v}).Coloring (Fin 7)}
    (F : DegreeTwelveFrame G v c) (gamma rho : Fin 5) (hgr : gamma ≠ rho)
    (ep eq er : Fin 2) (hpq : ep ≠ eq)
    (hap : G.Adj (F.center 0).val (F.leaf gamma ep).val)
    (hbq : G.Adj (F.center 1).val (F.leaf gamma eq).val)
    (hbr : G.Adj (F.center 1).val (F.leaf rho er).val)
    (z : {x : V // x ≠ v}) (hz : z.val ∉ insert v (G.neighborFinset v))
    (hzr : G.Adj z.val (F.leaf rho er).val)
    (hzp : G.Adj z.val (F.leaf gamma ep).val) : False := by
  let a := F.center 0
  let b := F.center 1
  let p := F.leaf gamma ep
  let q := F.leaf gamma eq
  let r := F.leaf rho er
  have hpqn : p.val ≠ q.val := (F.leaf_same_pair_injective gamma).ne hpq
  have hpr := F.leaf_leaf_ne hgr ep er
  have hqr := F.leaf_leaf_ne hgr eq er
  have hapn := F.center_leaf_ne 0 gamma ep
  have haqn := F.center_leaf_ne 0 gamma eq
  have harn := F.center_leaf_ne 0 rho er
  have hbpn := F.center_leaf_ne 1 gamma ep
  have hbqn := F.center_leaf_ne 1 gamma eq
  have hbrn := F.center_leaf_ne 1 rho er
  have hab := F.center_center_ne (by decide : (0 : Fin 2) ≠ 1)
  have hza := outside_closed_ne_neighbor z.val hz a
  have hzb := outside_closed_ne_neighbor z.val hz b
  have hzp' := outside_closed_ne_neighbor z.val hz p
  have hzq' := outside_closed_ne_neighbor z.val hz q
  have hzr' := outside_closed_ne_neighbor z.val hz r
  let t : Fin 6 → V := ![q.val, b.val, r.val, z.val, p.val, a.val]
  have ht : Function.Injective t := by
    change Function.Injective ![q.val, b.val, r.val, z.val, p.val, a.val]
    unfold Matrix.vecCons
    refine Fin.cons_injective_of_injective ?_ ?_
    · simpa only [Fin.range_cons, Matrix.range_empty, Set.mem_insert_iff,
        Set.mem_empty_iff_false, or_false, not_or] using
        (show q.val ≠ b.val ∧ q.val ≠ r.val ∧ q.val ≠ z.val ∧ q.val ≠ p.val ∧ q.val ≠ a.val from ⟨Ne.symm hbqn, hqr, Ne.symm hzq', Ne.symm hpqn, Ne.symm haqn⟩)
    refine Fin.cons_injective_of_injective ?_ ?_
    · simpa only [Fin.range_cons, Matrix.range_empty, Set.mem_insert_iff,
        Set.mem_empty_iff_false, or_false, not_or] using
        (show b.val ≠ r.val ∧ b.val ≠ z.val ∧ b.val ≠ p.val ∧ b.val ≠ a.val from ⟨hbrn, Ne.symm hzb, hbpn, Ne.symm hab⟩)
    refine Fin.cons_injective_of_injective ?_ ?_
    · simpa only [Fin.range_cons, Matrix.range_empty, Set.mem_insert_iff,
        Set.mem_empty_iff_false, or_false, not_or] using
        (show r.val ≠ z.val ∧ r.val ≠ p.val ∧ r.val ≠ a.val from ⟨Ne.symm hzr', Ne.symm hpr, Ne.symm harn⟩)
    refine Fin.cons_injective_of_injective ?_ ?_
    · simpa only [Fin.range_cons, Matrix.range_empty, Set.mem_insert_iff,
        Set.mem_empty_iff_false, or_false, not_or] using
        (show z.val ≠ p.val ∧ z.val ≠ a.val from ⟨hzp', hza⟩)
    exact injective_pair_iff_ne.mpr (Ne.symm hapn)
  have htv : ∀ i : Fin 6, t i ≠ v := by
    intro i
    fin_cases i
    · exact q.property.ne.symm
    · exact b.property.ne.symm
    · exact r.property.ne.symm
    · exact z.property
    · exact p.property.ne.symm
    · exact a.property.ne.symm
  have hcolor : c ⟨t 0, htv 0⟩ = c ⟨t 4, htv 4⟩ :=
    (F.leaf_color gamma eq).trans (F.leaf_color gamma ep).symm
  exact rooted_five_path_same_color_false hr v c t ht htv q.property a.property
    hbq.symm hbr hzr.symm hzp hap.symm 0 4 (by decide) hcolor

theorem splitPoolHits_empty_at_commonRep_neighbor
    (hcrit : IsCriticalPlus 7 G) (hc : modCycleCount 7 G = 2880)
    (hnot : ¬ IsCompleteOfOrder G 8) {v : V}
    {c : (G.induce {x | x ≠ v}).Coloring (Fin 7)} (hv : G.degree v = 12)
    (F : DegreeTwelveFrame G v c) (rho : ↥F.commonColors)
    (z : {x : V // x ≠ v}) (hz : z.val ∉ insert v (G.neighborFinset v))
    (hzr : G.Adj z.val (F.commonRep rho).val) : splitPoolHits F z.val = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro t ht
  have ht' := (mem_splitPoolHits F z.val t).mp ht
  have hgr : t.1 ≠ rho.val := by intro he; exact ht'.1 (he.symm ▸ rho.property)
  let er : Fin 2 := Classical.choose (Finset.mem_filter.mp rho.property).2
  have hra : G.Adj (F.center 0).val (F.leaf rho.val er).val := F.commonRep_adj_zero rho
  have hrb : G.Adj (F.center 1).val (F.leaf rho.val er).val := F.commonRep_adj_one rho
  have hs := F.splitPair_of_not_common hcrit hc hnot hv t.1 ht'.1
  have hr : RainbowSevenCycles G := equality_rainbowSevenCycles hcrit hc
  have H : ∀ ep eq : Fin 2, ep ≠ eq →
      G.Adj (F.center 0).val (F.leaf t.1 ep).val →
      G.Adj (F.center 1).val (F.leaf t.1 eq).val →
      G.Adj z.val (F.leaf t.1 ep).val → False := by
    intro ep eq hpq hap hbq hzp
    exact common_split_outside_overlap_at_zero_false hr F t.1 rho.val hgr ep eq er
      hpq hap hbq hrb z hz hzr hzp
  have Hswap : ∀ ep eq : Fin 2, ep ≠ eq →
      G.Adj (F.center 0).val (F.leaf t.1 ep).val →
      G.Adj (F.center 1).val (F.leaf t.1 eq).val →
      G.Adj z.val (F.leaf t.1 eq).val → False := by
    intro ep eq hpq hap hbq hzq
    have hsa : G.Adj (F.swapCenters.center 0).val (F.swapCenters.leaf t.1 eq).val := by
      simpa only [F.swapCenters_center_zero, F.swapCenters_leaf] using hbq
    have hsb : G.Adj (F.swapCenters.center 1).val (F.swapCenters.leaf t.1 ep).val := by
      simpa only [F.swapCenters_center_one, F.swapCenters_leaf] using hap
    have hsr : G.Adj (F.swapCenters.center 1).val (F.swapCenters.leaf rho.val er).val := by
      simpa only [F.swapCenters_center_one, F.swapCenters_leaf] using hra
    exact common_split_outside_overlap_at_zero_false hr F.swapCenters t.1 rho.val hgr
      eq ep er (Ne.symm hpq) hsa hsb hsr z hz hzr hzq
  rcases hs with h | h <;> rcases t with ⟨gamma, e⟩ <;> fin_cases e
  · exact H 0 1 (by decide) h.1 h.2.2.1 ht'.2
  · exact Hswap 0 1 (by decide) h.1 h.2.2.1 ht'.2
  · exact Hswap 1 0 (by decide) h.1 h.2.2.1 ht'.2
  · exact H 1 0 (by decide) h.1 h.2.2.1 ht'.2

end TaskH.Seven
#print axioms TaskH.Seven.split_leaf_not_adj_commonRep
#print axioms TaskH.Seven.common_split_outside_overlap_at_zero_false
#print axioms TaskH.Seven.splitPoolHits_empty_at_commonRep_neighbor
