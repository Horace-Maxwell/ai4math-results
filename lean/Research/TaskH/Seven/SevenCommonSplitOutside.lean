import Research.TaskH.Seven.SevenCommonSplitLocal
import Research.TaskH.Seven.SevenDegreeTwelveClassOrder

/-! Each actual split leaf has at least ten outside neighbors when another
pair is common. The internal two-neighbor bound is proved, not postulated. -/

set_option autoImplicit false
universe u
namespace TaskH.Seven
open SimpleGraph _root_.TaskH.Challenge
open scoped Classical
variable {V : Type u} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem degreeTwelve_common_split_leaf_outside_card_ge_ten
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
    (hbr : G.Adj (F.center 1).val (F.leaf rho er).val) :
    10 ≤ ((G.neighborFinset (F.leaf gamma ep).val).filter
      (fun z => z ∉ insert v (G.neighborFinset v))).card := by
  classical
  let p := (F.leaf gamma ep).val
  let N := insert v (G.neighborFinset v)
  let I := (G.neighborFinset p).filter (fun z => z ∈ N)
  have hsub : I ⊆ {v, (F.center 0).val} := by
    intro z hz
    have hzp : G.Adj p z := (G.mem_neighborFinset p z).mp (Finset.mem_filter.mp hz).1
    have hzN := (Finset.mem_filter.mp hz).2
    rcases Finset.mem_insert.mp hzN with h | h
    · exact Finset.mem_insert.mpr (Or.inl h)
    · let zz : G.neighborSet v := ⟨z, (G.mem_neighborFinset v z).mp h⟩
      have he : zz = F.center 0 :=
        (degreeTwelve_common_split_leaf_internal_neighbor_iff hcrit hc hnot hv F
          gamma rho hgr ep eq er hpq hap hbp hbq har hbr zz).mp hzp
      exact Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr
        (congrArg Subtype.val he)))
  have hI : I.card ≤ 2 :=
    (Finset.card_le_card hsub).trans Finset.card_le_two
  have hpdegree := equality_noncomplete_degree_ge_twelve hcrit hc hnot p
  have hpart := Finset.card_filter_add_card_filter_not (s := G.neighborFinset p)
    (p := fun z => z ∈ N)
  rw [G.card_neighborFinset_eq_degree] at hpart
  change I.card + ((G.neighborFinset p).filter (fun z => z ∉ N)).card = G.degree p at hpart
  change 10 ≤ ((G.neighborFinset p).filter (fun z => z ∉ N)).card
  omega


theorem degreeTwelve_common_split_other_leaf_outside_card_ge_ten
    (hcrit : IsCriticalPlus 7 G) (hc : modCycleCount 7 G = 2880)
    (hnot : ¬ IsCompleteOfOrder G 8) {v : V}
    {c : (G.induce {x | x ≠ v}).Coloring (Fin 7)} (hv : G.degree v = 12)
    (F : DegreeTwelveFrame G v c)
    (gamma rho : Fin 5) (hgr : gamma ≠ rho)
    (ep eq er : Fin 2) (hpq : ep ≠ eq)
    (hap : G.Adj (F.center 0).val (F.leaf gamma ep).val)
    (hbq : G.Adj (F.center 1).val (F.leaf gamma eq).val)
    (haq : ¬ G.Adj (F.center 0).val (F.leaf gamma eq).val)
    (har : G.Adj (F.center 0).val (F.leaf rho er).val)
    (hbr : G.Adj (F.center 1).val (F.leaf rho er).val) :
    10 ≤ ((G.neighborFinset (F.leaf gamma eq).val).filter
      (fun z => z ∉ insert v (G.neighborFinset v))).card := by
  have hsa : G.Adj (F.swapCenters.center 0).val (F.swapCenters.leaf gamma eq).val := by
    simpa only [F.swapCenters_center_zero, F.swapCenters_leaf] using hbq
  have hsna : ¬ G.Adj (F.swapCenters.center 1).val (F.swapCenters.leaf gamma eq).val := by
    simpa only [F.swapCenters_center_one, F.swapCenters_leaf] using haq
  have hsb : G.Adj (F.swapCenters.center 1).val (F.swapCenters.leaf gamma ep).val := by
    simpa only [F.swapCenters_center_one, F.swapCenters_leaf] using hap
  have hsra : G.Adj (F.swapCenters.center 0).val (F.swapCenters.leaf rho er).val := by
    simpa only [F.swapCenters_center_zero, F.swapCenters_leaf] using hbr
  have hsrb : G.Adj (F.swapCenters.center 1).val (F.swapCenters.leaf rho er).val := by
    simpa only [F.swapCenters_center_one, F.swapCenters_leaf] using har
  exact degreeTwelve_common_split_leaf_outside_card_ge_ten hcrit hc hnot hv F.swapCenters
    gamma rho hgr eq ep er (Ne.symm hpq) hsa hsna hsb hsra hsrb

end TaskH.Seven
#print axioms TaskH.Seven.degreeTwelve_common_split_leaf_outside_card_ge_ten

#print axioms TaskH.Seven.degreeTwelve_common_split_other_leaf_outside_card_ge_ten
