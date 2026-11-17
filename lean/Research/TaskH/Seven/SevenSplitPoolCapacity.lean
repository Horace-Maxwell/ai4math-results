import Research.TaskH.Seven.SevenSplitPoolColors

/-! Finite outside split-leaf capacities derived from the actual P7 color
constraints. The strict s-1 bound requires at least two split colors. -/

set_option autoImplicit false
universe u
namespace TaskH.Seven
open SimpleGraph _root_.TaskH.Challenge
open scoped Classical
variable {V : Type u} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem DegreeTwelveFrame.leaf_coordinates_injective {v : V}
    {c : (G.induce {x | x ≠ v}).Coloring (Fin 7)}
    (F : DegreeTwelveFrame G v c) :
    Function.Injective (fun t : Fin 5 × Fin 2 => (F.leaf t.1 t.2).val) := by
  intro a b he
  rcases a with ⟨i, e⟩
  rcases b with ⟨j, d⟩
  have hh := congrArg (neighborColor v c) (Subtype.ext he)
  rw [F.leaf_color, F.leaf_color] at hh
  have hij : i = j := F.pairIndex.injective (Subtype.ext hh)
  subst j
  have hed := F.leaf_same_pair_injective i he
  exact Prod.ext rfl hed

noncomputable def splitPoolHits {v : V}
    {c : (G.induce {x | x ≠ v}).Coloring (Fin 7)}
    (F : DegreeTwelveFrame G v c) (z : V) : Finset (Fin 5 × Fin 2) :=
  Finset.univ.filter (fun t => t.1 ∉ F.commonColors ∧ G.Adj z (F.leaf t.1 t.2).val)

theorem mem_splitPoolHits {v : V}
    {c : (G.induce {x | x ≠ v}).Coloring (Fin 7)}
    (F : DegreeTwelveFrame G v c) (z : V) (t : Fin 5 × Fin 2) :
    t ∈ splitPoolHits F z ↔ t.1 ∉ F.commonColors ∧ G.Adj z (F.leaf t.1 t.2).val := by
  simp only [splitPoolHits, Finset.mem_filter, Finset.mem_univ, true_and]

theorem splitPoolHits_fst_injective
    (hcrit : IsCriticalPlus 7 G) (hc : modCycleCount 7 G = 2880)
    (hnot : ¬ IsCompleteOfOrder G 8) {v : V}
    {c : (G.induce {x | x ≠ v}).Coloring (Fin 7)} (hv : G.degree v = 12)
    (F : DegreeTwelveFrame G v c) (hcommon : F.commonColors.Nonempty)
    (z : {x : V // x ≠ v}) (hz : z.val ∉ insert v (G.neighborFinset v)) :
    Set.InjOn Prod.fst (splitPoolHits F z.val : Set (Fin 5 × Fin 2)) := by
  obtain ⟨rho, hrho⟩ := hcommon
  intro a ha b hb hab
  by_contra hne
  have hxy : (F.leaf a.1 a.2).val ≠ (F.leaf b.1 b.2).val :=
    F.leaf_coordinates_injective.ne hne
  have ha' := (mem_splitPoolHits F z.val a).mp ha
  have hb' := (mem_splitPoolHits F z.val b).mp hb
  have H := split_pool_two_leaf_constraints hcrit hc hnot hv F a.1 b.1 rho
    ha'.1 hb'.1 hrho a.2 b.2 hxy z hz ha'.2 hb'.2
  exact H.1 hab

theorem splitPoolHits_card_le_splitColors
    (hcrit : IsCriticalPlus 7 G) (hc : modCycleCount 7 G = 2880)
    (hnot : ¬ IsCompleteOfOrder G 8) {v : V}
    {c : (G.induce {x | x ≠ v}).Coloring (Fin 7)} (hv : G.degree v = 12)
    (F : DegreeTwelveFrame G v c) (hcommon : F.commonColors.Nonempty)
    (z : {x : V // x ≠ v}) (hz : z.val ∉ insert v (G.neighborFinset v)) :
    (splitPoolHits F z.val).card ≤ (F.commonColorsᶜ).card := by
  have hinj := splitPoolHits_fst_injective hcrit hc hnot hv F hcommon z hz
  have hsub : (splitPoolHits F z.val).image Prod.fst ⊆ F.commonColorsᶜ := by
    intro i hi
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hi
    exact Finset.mem_compl.mpr ((mem_splitPoolHits F z.val t).mp ht).1
  have hh := Finset.card_le_card hsub
  rw [Finset.card_image_iff.mpr hinj] at hh
  exact hh

theorem splitPoolHits_card_lt_splitColors
    (hcrit : IsCriticalPlus 7 G) (hc : modCycleCount 7 G = 2880)
    (hnot : ¬ IsCompleteOfOrder G 8) {v : V}
    {c : (G.induce {x | x ≠ v}).Coloring (Fin 7)} (hv : G.degree v = 12)
    (F : DegreeTwelveFrame G v c) (hcommon : F.commonColors.Nonempty)
    (hsplit : 2 ≤ (F.commonColorsᶜ).card)
    (z : {x : V // x ≠ v}) (hz : z.val ∉ insert v (G.neighborFinset v)) :
    (splitPoolHits F z.val).card < (F.commonColorsᶜ).card := by
  classical
  by_contra! hge
  let T := splitPoolHits F z.val
  have hinj := splitPoolHits_fst_injective hcrit hc hnot hv F hcommon z hz
  have himagecard : (T.image Prod.fst).card = T.card := Finset.card_image_iff.mpr hinj
  have hsub : T.image Prod.fst ⊆ F.commonColorsᶜ := by
    intro i hi
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hi
    exact Finset.mem_compl.mpr ((mem_splitPoolHits F z.val t).mp ht).1
  have hcover : T.image Prod.fst = F.commonColorsᶜ :=
    Finset.eq_of_subset_of_card_le hsub (by rw [himagecard]; exact hge)
  have hT : 1 < T.card := by
    change 1 < (splitPoolHits F z.val).card
    omega
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp hT
  have hxy := F.leaf_coordinates_injective.ne hab
  have ha' := (mem_splitPoolHits F z.val a).mp ha
  have hb' := (mem_splitPoolHits F z.val b).mp hb
  have H : ∀ rho ∈ F.commonColors,
      a.1 ≠ b.1 ∧ c z ≠ neighborColor v c (F.center 0) ∧
      c z ≠ neighborColor v c (F.center 1) ∧ c z ≠ (F.pairIndex rho).val := by
    intro rho hrho
    exact split_pool_two_leaf_constraints hcrit hc hnot hv F a.1 b.1 rho
      ha'.1 hb'.1 hrho a.2 b.2 hxy z hz ha'.2 hb'.2
  obtain ⟨rho, hrho⟩ := hcommon
  have H0 := H rho hrho
  rcases F.color_cases (c z) with ⟨j, hj⟩ | ⟨i, hi⟩
  · fin_cases j
    · apply H0.2.1
      exact hj.symm.trans (F.center_color 0).symm
    · apply H0.2.2.1
      exact hj.symm.trans (F.center_color 1).symm
  · by_cases hic : i ∈ F.commonColors
    · exact (H i hic).2.2.2 hi.symm
    · have him : i ∈ T.image Prod.fst := by rw [hcover]; exact Finset.mem_compl.mpr hic
      obtain ⟨t, ht, hti⟩ := Finset.mem_image.mp him
      have ht' := (mem_splitPoolHits F z.val t).mp ht
      have hproper : c z ≠ neighborColor v c (F.leaf t.1 t.2) := c.valid ht'.2
      apply hproper
      exact hi.symm.trans ((congrArg (fun k : Fin 5 => (F.pairIndex k).val) hti).symm.trans
        (F.leaf_color t.1 t.2).symm)

end TaskH.Seven
#print axioms TaskH.Seven.DegreeTwelveFrame.leaf_coordinates_injective
#print axioms TaskH.Seven.splitPoolHits
#print axioms TaskH.Seven.mem_splitPoolHits
#print axioms TaskH.Seven.splitPoolHits_fst_injective
#print axioms TaskH.Seven.splitPoolHits_card_le_splitColors
#print axioms TaskH.Seven.splitPoolHits_card_lt_splitColors
