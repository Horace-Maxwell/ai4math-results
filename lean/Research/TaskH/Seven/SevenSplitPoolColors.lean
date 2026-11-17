import Research.TaskH.Seven.SevenSplitPairCoordinates

/-! The true path x-z-y-center-r-othercenter gives both the no-same-split-
color rule and all common/center color exclusions for an outside leaf pool. -/

set_option autoImplicit false
universe u
namespace TaskH.Seven
open SimpleGraph _root_.TaskH.Challenge
open scoped Classical
variable {V : Type u} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem outside_closed_ne_neighbor {v : V} (z : V)
    (hz : z ∉ insert v (G.neighborFinset v)) (w : G.neighborSet v) : z ≠ w.val := by
  intro he
  apply hz
  exact Finset.mem_insert.mpr (Or.inr ((G.mem_neighborFinset v z).mpr
    (by rw [he]; exact w.property)))

theorem split_pool_two_leaf_constraints_at_zero
    (hr : RainbowSevenCycles G) {v : V}
    {c : (G.induce {x | x ≠ v}).Coloring (Fin 7)}
    (F : DegreeTwelveFrame G v c) (gamma eta rho : Fin 5)
    (hgr : gamma ≠ rho) (her : eta ≠ rho) (ex ey er : Fin 2)
    (hxy : (F.leaf gamma ex).val ≠ (F.leaf eta ey).val)
    (hya : G.Adj (F.center 0).val (F.leaf eta ey).val)
    (hra : G.Adj (F.center 0).val (F.leaf rho er).val)
    (hrb : G.Adj (F.center 1).val (F.leaf rho er).val)
    (z : {x : V // x ≠ v}) (hz : z.val ∉ insert v (G.neighborFinset v))
    (hzx : G.Adj z.val (F.leaf gamma ex).val)
    (hzy : G.Adj z.val (F.leaf eta ey).val) :
    gamma ≠ eta ∧ c z ≠ neighborColor v c (F.center 0) ∧
      c z ≠ neighborColor v c (F.center 1) ∧ c z ≠ (F.pairIndex rho).val := by
  let x := F.leaf gamma ex
  let y := F.leaf eta ey
  let r := F.leaf rho er
  let a := F.center 0
  let b := F.center 1
  have hxr := F.leaf_leaf_ne hgr ex er
  have hyr := F.leaf_leaf_ne her ey er
  have hax := F.center_leaf_ne 0 gamma ex
  have hay := F.center_leaf_ne 0 eta ey
  have har := F.center_leaf_ne 0 rho er
  have hbx := F.center_leaf_ne 1 gamma ex
  have hby := F.center_leaf_ne 1 eta ey
  have hbr := F.center_leaf_ne 1 rho er
  have hab := F.center_center_ne (by decide : (0 : Fin 2) ≠ 1)
  have hzx' := outside_closed_ne_neighbor z.val hz x
  have hzy' := outside_closed_ne_neighbor z.val hz y
  have hzr' := outside_closed_ne_neighbor z.val hz r
  have hza' := outside_closed_ne_neighbor z.val hz a
  have hzb' := outside_closed_ne_neighbor z.val hz b
  let t : Fin 6 → V := ![x.val, z.val, y.val, a.val, r.val, b.val]
  have ht : Function.Injective t := by
    intro i j he
    fin_cases i <;> fin_cases j <;> simp_all [t, x, y, r, a, b]
  have htv : ∀ i : Fin 6, t i ≠ v := by
    intro i
    fin_cases i
    · exact x.property.ne.symm
    · exact z.property
    · exact y.property.ne.symm
    · exact a.property.ne.symm
    · exact r.property.ne.symm
    · exact b.property.ne.symm
  have hinj := rooted_five_path_colors_injective hr v c t ht htv
    x.property b.property hzx.symm hzy hya.symm hra hrb.symm
  let col : Fin 6 → Fin 7 := fun i => c ⟨t i, htv i⟩
  have h0 : col 0 = (F.pairIndex gamma).val := F.leaf_color gamma ex
  have h1 : col 1 = c z := rfl
  have h2 : col 2 = (F.pairIndex eta).val := F.leaf_color eta ey
  have h3 : col 3 = neighborColor v c (F.center 0) := rfl
  have h4 : col 4 = (F.pairIndex rho).val := F.leaf_color rho er
  have h5 : col 5 = neighborColor v c (F.center 1) := rfl
  have hge : gamma ≠ eta := by
    intro he
    have hcol : col 0 = col 2 := by rw [h0, h2, he]
    have hh := hinj hcol
    norm_num at hh
  have hn : ∀ i : Fin 6, i ≠ 1 → col 1 ≠ col i := by
    intro i hi he
    exact hi (hinj he).symm
  refine ⟨hge, ?_, ?_, ?_⟩
  · simpa only [h1, h3] using hn 3 (by decide)
  · simpa only [h1, h5] using hn 5 (by decide)
  · simpa only [h1, h4] using hn 4 (by decide)

theorem split_pool_two_leaf_constraints
    (hcrit : IsCriticalPlus 7 G) (hc : modCycleCount 7 G = 2880)
    (hnot : ¬ IsCompleteOfOrder G 8) {v : V}
    {c : (G.induce {x | x ≠ v}).Coloring (Fin 7)} (hv : G.degree v = 12)
    (F : DegreeTwelveFrame G v c) (gamma eta rho : Fin 5)
    (hgamma : gamma ∉ F.commonColors) (heta : eta ∉ F.commonColors)
    (hrho : rho ∈ F.commonColors) (ex ey : Fin 2)
    (hxy : (F.leaf gamma ex).val ≠ (F.leaf eta ey).val)
    (z : {x : V // x ≠ v}) (hz : z.val ∉ insert v (G.neighborFinset v))
    (hzx : G.Adj z.val (F.leaf gamma ex).val)
    (hzy : G.Adj z.val (F.leaf eta ey).val) :
    gamma ≠ eta ∧ c z ≠ neighborColor v c (F.center 0) ∧
      c z ≠ neighborColor v c (F.center 1) ∧ c z ≠ (F.pairIndex rho).val := by
  have hgr : gamma ≠ rho := by intro he; exact hgamma (he.symm ▸ hrho)
  have her : eta ≠ rho := by intro he; exact heta (he.symm ▸ hrho)
  obtain ⟨er, hra, hrb⟩ := (Finset.mem_filter.mp hrho).2
  have hsplit := F.splitPair_of_not_common hcrit hc hnot hv eta heta
  have hy : G.Adj (F.center 0).val (F.leaf eta ey).val ∨
      G.Adj (F.center 1).val (F.leaf eta ey).val := by
    rcases hsplit with h | h <;> fin_cases ey <;> simp_all
  have hr : RainbowSevenCycles G := equality_rainbowSevenCycles hcrit hc
  rcases hy with hya | hyb
  · exact split_pool_two_leaf_constraints_at_zero hr F gamma eta rho hgr her ex ey er
      hxy hya hra hrb z hz hzx hzy
  · have hya : G.Adj (F.swapCenters.center 0).val (F.swapCenters.leaf eta ey).val := by
      simpa only [F.swapCenters_center_zero, F.swapCenters_leaf] using hyb
    have hsra : G.Adj (F.swapCenters.center 0).val (F.swapCenters.leaf rho er).val := by
      simpa only [F.swapCenters_center_zero, F.swapCenters_leaf] using hrb
    have hsrb : G.Adj (F.swapCenters.center 1).val (F.swapCenters.leaf rho er).val := by
      simpa only [F.swapCenters_center_one, F.swapCenters_leaf] using hra
    have H := split_pool_two_leaf_constraints_at_zero hr F.swapCenters gamma eta rho
      hgr her ex ey er hxy hya hsra hsrb z hz hzx hzy
    refine ⟨H.1, ?_, ?_, H.2.2.2⟩
    · simpa only [F.swapCenters_center_one] using H.2.2.1
    · simpa only [F.swapCenters_center_zero] using H.2.1

end TaskH.Seven
#print axioms TaskH.Seven.outside_closed_ne_neighbor
#print axioms TaskH.Seven.split_pool_two_leaf_constraints_at_zero
#print axioms TaskH.Seven.split_pool_two_leaf_constraints
