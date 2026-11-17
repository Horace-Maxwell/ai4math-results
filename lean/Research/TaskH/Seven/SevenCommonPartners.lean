import Research.TaskH.Seven.SevenCommonOneTwo

/-! The common-representative/partner no-edge rule uses an actual neighbor
of a third pair color, supplied by the original center first-step theorem.
That third color need not itself be common or split. -/

set_option autoImplicit false
universe u
namespace TaskH.Seven
open SimpleGraph _root_.TaskH.Challenge
open scoped Classical
variable {V : Type u} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem common_partner_other_rep_extra_edge_false
    (hcrit : IsCriticalPlus 7 G) (hc : modCycleCount 7 G = 2880)
    (hnot : ¬ IsCompleteOfOrder G 8) {v : V}
    {c : (G.induce {x | x ≠ v}).Coloring (Fin 7)} (hv : G.degree v = 12)
    (F : DegreeTwelveFrame G v c) (rho sigma : Fin 5) (hrs : rho ≠ sigma)
    (er es et : Fin 2) (hst : es ≠ et)
    (hra : G.Adj (F.center 0).val (F.leaf rho er).val)
    (hsa : G.Adj (F.center 0).val (F.leaf sigma es).val)
    (hsb : G.Adj (F.center 1).val (F.leaf sigma es).val)
    (htr : G.Adj (F.leaf sigma et).val (F.leaf rho er).val) : False := by
  obtain ⟨gamma, hgr, hgs⟩ : ∃ gamma : Fin 5, gamma ≠ rho ∧ gamma ≠ sigma := by
    by_contra! hh
    have hs : (Finset.univ : Finset (Fin 5)) ⊆ {rho, sigma} := by
      intro gamma _hg
      by_cases hgr : gamma = rho
      · exact Finset.mem_insert.mpr (Or.inl hgr)
      · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr (hh gamma hgr)))
    have hcard := Finset.card_le_card hs
    have hcard' : 5 ≤ ({rho, sigma} : Finset (Fin 5)).card := by
      simpa only [Finset.card_univ, Fintype.card_fin] using hcard
    have hp : ({rho, sigma} : Finset (Fin 5)).card ≤ 2 := Finset.card_le_two
    omega
  obtain ⟨eu, hbu⟩ := F.center_meets_pair hcrit hc hnot hv 1 gamma
  let a := F.center 0
  let b := F.center 1
  let r := F.leaf rho er
  let s := F.leaf sigma es
  let t := F.leaf sigma et
  let u := F.leaf gamma eu
  have hab : a ≠ b := by intro he; exact F.center_center_ne (by decide : (0 : Fin 2) ≠ 1) (congrArg Subtype.val he)
  have hcLeaf : ∀ j : Fin 2, ∀ i : Fin 5, ∀ e : Fin 2, F.center j ≠ F.leaf i e := by
    intro j i e he
    exact F.center_leaf_ne j i e (congrArg Subtype.val he)
  have hLeaf : ∀ {i j : Fin 5}, i ≠ j → ∀ e d : Fin 2, F.leaf i e ≠ F.leaf j d := by
    intro i j hij e d he
    exact F.leaf_leaf_ne hij e d (congrArg Subtype.val he)
  have hrsn : r ≠ s := hLeaf hrs er es
  have hrtn : r ≠ t := hLeaf hrs er et
  have hstn : s ≠ t := by
    intro he
    exact hst (F.leaf_same_pair_injective sigma (congrArg Subtype.val he))
  have hur : u ≠ r := hLeaf hgr eu er
  have hus : u ≠ s := hLeaf hgs eu es
  have hut : u ≠ t := hLeaf hgs eu et
  have har := hcLeaf 0 rho er
  have has := hcLeaf 0 sigma es
  have hat := hcLeaf 0 sigma et
  have hau := hcLeaf 0 gamma eu
  have hbr := hcLeaf 1 rho er
  have hbs := hcLeaf 1 sigma es
  have hbt := hcLeaf 1 sigma et
  have hbu' := hcLeaf 1 gamma eu
  let f : Fin 6 → G.neighborSet v := ![t, r, a, s, b, u]
  have hf : Function.Injective f := by
    change Function.Injective ![t, r, a, s, b, u]
    unfold Matrix.vecCons
    refine Fin.cons_injective_of_injective ?_ ?_
    · simpa only [Fin.range_cons, Matrix.range_empty, Set.mem_insert_iff,
        Set.mem_empty_iff_false, or_false, not_or] using
        (show t ≠ r ∧ t ≠ a ∧ t ≠ s ∧ t ≠ b ∧ t ≠ u from ⟨Ne.symm hrtn, Ne.symm hat, Ne.symm hstn, Ne.symm hbt, Ne.symm hut⟩)
    refine Fin.cons_injective_of_injective ?_ ?_
    · simpa only [Fin.range_cons, Matrix.range_empty, Set.mem_insert_iff,
        Set.mem_empty_iff_false, or_false, not_or] using
        (show r ≠ a ∧ r ≠ s ∧ r ≠ b ∧ r ≠ u from ⟨Ne.symm har, hrsn, Ne.symm hbr, Ne.symm hur⟩)
    refine Fin.cons_injective_of_injective ?_ ?_
    · simpa only [Fin.range_cons, Matrix.range_empty, Set.mem_insert_iff,
        Set.mem_empty_iff_false, or_false, not_or] using
        (show a ≠ s ∧ a ≠ b ∧ a ≠ u from ⟨has, hab, hau⟩)
    refine Fin.cons_injective_of_injective ?_ ?_
    · simpa only [Fin.range_cons, Matrix.range_empty, Set.mem_insert_iff,
        Set.mem_empty_iff_false, or_false, not_or] using
        (show s ≠ b ∧ s ≠ u from ⟨Ne.symm hbs, Ne.symm hus⟩)
    exact injective_pair_iff_ne.mpr (hbu')
  have hcolor : neighborColor v c (f 0) = neighborColor v c (f 3) :=
    (F.leaf_color sigma et).trans (F.leaf_color sigma es).symm
  exact neighbor_five_path_same_color_false (equality_rainbowSevenCycles hcrit hc)
    v c f hf htr hra.symm hsa hsb.symm hbu 0 3 (by decide) hcolor

noncomputable def DegreeTwelveFrame.commonRepSide {v : V}
    {c : (G.induce {x | x ≠ v}).Coloring (Fin 7)}
    (F : DegreeTwelveFrame G v c) (i : ↥F.commonColors) : Fin 2 :=
  Classical.choose (Finset.mem_filter.mp i.property).2

noncomputable def DegreeTwelveFrame.commonMate {v : V}
    {c : (G.induce {x | x ≠ v}).Coloring (Fin 7)}
    (F : DegreeTwelveFrame G v c) (i : ↥F.commonColors) : G.neighborSet v :=
  F.leaf i.val (F.commonRepSide i + 1)

theorem fin_two_add_one_ne (i : Fin 2) : i + 1 ≠ i := by
  fin_cases i <;> decide

theorem DegreeTwelveFrame.commonMate_color {v : V}
    {c : (G.induce {x | x ≠ v}).Coloring (Fin 7)}
    (F : DegreeTwelveFrame G v c) (i : ↥F.commonColors) :
    neighborColor v c (F.commonMate i) = (F.pairIndex i.val).val := F.leaf_color i.val _

theorem DegreeTwelveFrame.commonMate_ne_rep {v : V}
    {c : (G.induce {x | x ≠ v}).Coloring (Fin 7)}
    (F : DegreeTwelveFrame G v c) (i : ↥F.commonColors) :
    (F.commonMate i).val ≠ (F.commonRep i).val :=
  (F.leaf_same_pair_injective i.val).ne (fin_two_add_one_ne (F.commonRepSide i))

theorem commonRep_not_adj_commonMate
    (hcrit : IsCriticalPlus 7 G) (hc : modCycleCount 7 G = 2880)
    (hnot : ¬ IsCompleteOfOrder G 8) {v : V}
    {c : (G.induce {x | x ≠ v}).Coloring (Fin 7)} (hv : G.degree v = 12)
    (F : DegreeTwelveFrame G v c) (i j : ↥F.commonColors) :
    ¬ G.Adj (F.commonRep i).val (F.commonMate j).val := by
  intro he
  by_cases hij : i = j
  · subst j
    have hproper : neighborColor v c (F.commonRep i) ≠ neighborColor v c (F.commonMate i) := c.valid he
    exact hproper ((F.commonRep_color i).trans (F.commonMate_color i).symm)
  · have hvals : i.val ≠ j.val := fun heq => hij (Subtype.ext heq)
    exact common_partner_other_rep_extra_edge_false hcrit hc hnot hv F i.val j.val hvals
      (F.commonRepSide i) (F.commonRepSide j) (F.commonRepSide j + 1)
      (Ne.symm (fin_two_add_one_ne (F.commonRepSide j)))
      (F.commonRep_adj_zero i) (F.commonRep_adj_zero j) (F.commonRep_adj_one j) he.symm


theorem fin_two_eq_or_add_one (i j : Fin 2) : i = j ∨ i = j + 1 := by
  fin_cases i <;> fin_cases j <;> decide

theorem DegreeTwelveFrame.common_pair_cases {v : V}
    {c : (G.induce {x | x ≠ v}).Coloring (Fin 7)}
    (F : DegreeTwelveFrame G v c) (i : ↥F.commonColors) (e : Fin 2) :
    F.leaf i.val e = F.commonRep i ∨ F.leaf i.val e = F.commonMate i := by
  rcases fin_two_eq_or_add_one e (F.commonRepSide i) with h | h
  · left
    exact congrArg (F.leaf i.val) h
  · right
    exact congrArg (F.leaf i.val) h

theorem commonRep_internal_neighbor_cases
    (hcrit : IsCriticalPlus 7 G) (hc : modCycleCount 7 G = 2880)
    (hnot : ¬ IsCompleteOfOrder G 8) {v : V}
    {c : (G.induce {x | x ≠ v}).Coloring (Fin 7)} (hv : G.degree v = 12)
    (F : DegreeTwelveFrame G v c) (i : ↥F.commonColors) (z : G.neighborSet v)
    (hiz : G.Adj (F.commonRep i).val z.val) :
    z = F.center 0 ∨ z = F.center 1 ∨ ∃ j : ↥F.commonColors, z = F.commonRep j := by
  rcases F.neighbor_cases z with ⟨j, hj⟩ | ⟨gamma, e, he⟩
  · fin_cases j
    · exact Or.inl hj.symm
    · exact Or.inr (Or.inl hj.symm)
  · have hileaf : G.Adj (F.commonRep i).val (F.leaf gamma e).val := by rw [he]; exact hiz
    by_cases hg : gamma ∈ F.commonColors
    · let j : ↥F.commonColors := ⟨gamma, hg⟩
      rcases F.common_pair_cases j e with hrep | hmate
      · exact Or.inr (Or.inr ⟨j, he.symm.trans hrep⟩)
      · rw [hmate] at hileaf
        exact (commonRep_not_adj_commonMate hcrit hc hnot hv F i j hileaf).elim
    · exact (split_leaf_not_adj_commonRep hcrit hc hnot hv F gamma hg i e hileaf.symm).elim

end TaskH.Seven
#print axioms TaskH.Seven.common_partner_other_rep_extra_edge_false
#print axioms TaskH.Seven.DegreeTwelveFrame.commonRepSide
#print axioms TaskH.Seven.DegreeTwelveFrame.commonMate
#print axioms TaskH.Seven.fin_two_add_one_ne
#print axioms TaskH.Seven.DegreeTwelveFrame.commonMate_color
#print axioms TaskH.Seven.DegreeTwelveFrame.commonMate_ne_rep
#print axioms TaskH.Seven.commonRep_not_adj_commonMate

#print axioms TaskH.Seven.fin_two_eq_or_add_one
#print axioms TaskH.Seven.DegreeTwelveFrame.common_pair_cases
#print axioms TaskH.Seven.commonRep_internal_neighbor_cases
