import Research.TaskH.Seven.SevenCommonIncidence

/-! In the all-common case, an actual common partner has at most seven
neighbors in N[v]. The actual R-to-partner no-edge rule is used pointwise. -/

set_option autoImplicit false
universe u
namespace TaskH.Seven
open SimpleGraph _root_.TaskH.Challenge
open scoped Classical
variable {V : Type u} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem DegreeTwelveFrame.commonRep_ne_commonMate {v : V}
    {c : (G.induce {x | x ≠ v}).Coloring (Fin 7)}
    (F : DegreeTwelveFrame G v c) (i j : ↥F.commonColors) :
    (F.commonRep i).val ≠ (F.commonMate j).val := by
  by_cases hij : i = j
  · subst j
    exact Ne.symm (F.commonMate_ne_rep i)
  · have hvals : i.val ≠ j.val := fun he => hij (Subtype.ext he)
    exact F.leaf_leaf_ne hvals (F.commonRepSide i) (F.commonRepSide j + 1)

theorem commonMate_outside_card_ge_five
    (hcrit : IsCriticalPlus 7 G) (hc : modCycleCount 7 G = 2880)
    (hnot : ¬ IsCompleteOfOrder G 8) {v : V}
    {c : (G.induce {x | x ≠ v}).Coloring (Fin 7)} (hv : G.degree v = 12)
    (F : DegreeTwelveFrame G v c) (hfive : F.commonColors.card = 5)
    (rho : ↥F.commonColors) :
    5 ≤ ((G.neighborFinset (F.commonMate rho).val).filter
      (fun z => z ∉ insert v (G.neighborFinset v))).card := by
  classical
  have hfull := commonColors_eq_univ_of_card_five F hfive
  let s := F.commonMate rho
  let N := insert v (G.neighborFinset v)
  let A := (Finset.univ : Finset ↥F.commonColors).erase rho
  let f : ↥F.commonColors → V := fun i => (F.commonMate i).val
  let B := insert v (insert (F.center 0).val (insert (F.center 1).val (A.image f)))
  let I := (G.neighborFinset s.val).filter (fun z => z ∈ N)
  have hsub : I ⊆ B := by
    intro z hz
    have hsz := (G.mem_neighborFinset s.val z).mp (Finset.mem_filter.mp hz).1
    rcases Finset.mem_insert.mp (Finset.mem_filter.mp hz).2 with hzv | hzv
    · exact Finset.mem_insert.mpr (Or.inl hzv)
    · let zz : G.neighborSet v := ⟨z, (G.mem_neighborFinset v z).mp hzv⟩
      rcases F.neighbor_cases zz with ⟨j, hj⟩ | ⟨gamma, e, hge⟩
      · have he : (F.center j).val = z := congrArg Subtype.val hj
        rw [← he]
        fin_cases j
        · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_insert.mpr (Or.inl rfl)))
        · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_insert.mpr
            (Or.inr (Finset.mem_insert.mpr (Or.inl rfl)))))
      · have hg : gamma ∈ F.commonColors := by rw [hfull]; exact Finset.mem_univ gamma
        let j : ↥F.commonColors := ⟨gamma, hg⟩
        rcases F.common_pair_cases j e with hrep | hmate
        · have he : (F.commonRep j).val = z := congrArg Subtype.val (hrep.symm.trans hge)
          have ha : G.Adj (F.commonRep j).val s.val := by rw [he]; exact hsz.symm
          exact (commonRep_not_adj_commonMate hcrit hc hnot hv F j rho ha).elim
        · have he : (F.commonMate j).val = z := congrArg Subtype.val (hmate.symm.trans hge)
          by_cases hj : j = rho
          · have hs : (F.commonMate j).val = s.val :=
              congrArg (fun k => (F.commonMate k).val) hj
            exact (hsz.ne (hs.symm.trans he)).elim
          · have hjA : j ∈ A := Finset.mem_erase.mpr ⟨hj, Finset.mem_univ j⟩
            have hm : z ∈ A.image f := Finset.mem_image.mpr ⟨j, hjA, he⟩
            exact Finset.mem_insert.mpr (Or.inr (Finset.mem_insert.mpr
              (Or.inr (Finset.mem_insert.mpr (Or.inr hm)))))
  have hA : A.card = 4 := by
    simp only [A, Finset.card_erase_of_mem (Finset.mem_univ rho), Finset.card_univ,
      Fintype.card_coe, hfive]
  have him : (A.image f).card ≤ A.card := Finset.card_image_le
  have h0 := Finset.card_insert_le v (insert (F.center 0).val (insert (F.center 1).val (A.image f)))
  have h1 := Finset.card_insert_le (F.center 0).val (insert (F.center 1).val (A.image f))
  have h2 := Finset.card_insert_le (F.center 1).val (A.image f)
  have hI : I.card ≤ 7 := by
    have hh := Finset.card_le_card hsub
    change I.card ≤ (insert v (insert (F.center 0).val (insert (F.center 1).val (A.image f)))).card at hh
    omega
  have hd := equality_noncomplete_degree_ge_twelve hcrit hc hnot s.val
  have hp := Finset.card_filter_add_card_filter_not (s := G.neighborFinset s.val) (p := fun z => z ∈ N)
  rw [G.card_neighborFinset_eq_degree] at hp
  change I.card + ((G.neighborFinset s.val).filter (fun z => z ∉ N)).card = G.degree s.val at hp
  change 5 ≤ ((G.neighborFinset s.val).filter (fun z => z ∉ N)).card
  omega

end TaskH.Seven
#print axioms TaskH.Seven.DegreeTwelveFrame.commonRep_ne_commonMate
#print axioms TaskH.Seven.commonMate_outside_card_ge_five
