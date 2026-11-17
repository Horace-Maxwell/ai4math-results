import Research.TaskH.Seven.SevenCommonRepSeparation

/-! A selected common representative has at most 2h+1 internal neighbors.
This deliberately weak bound already suffices for h=1 and h=2 at order46;
no unproved representative-to-partner separation is used. -/

set_option autoImplicit false
universe u
namespace TaskH.Seven
open SimpleGraph _root_.TaskH.Challenge
open scoped Classical
variable {V : Type u} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem commonRep_outside_card_lower
    (hcrit : IsCriticalPlus 7 G) (hc : modCycleCount 7 G = 2880)
    (hnot : ¬ IsCompleteOfOrder G 8) {v : V}
    {c : (G.induce {x | x ≠ v}).Coloring (Fin 7)} (hv : G.degree v = 12)
    (F : DegreeTwelveFrame G v c) (rho : ↥F.commonColors) :
    11 ≤ ((G.neighborFinset (F.commonRep rho).val).filter
      (fun z => z ∉ insert v (G.neighborFinset v))).card + 2 * F.commonColors.card := by
  classical
  let r := F.commonRep rho
  let N := insert v (G.neighborFinset v)
  let C := (F.commonColors.erase rho.val) ×ˢ (Finset.univ : Finset (Fin 2))
  let f : Fin 5 × Fin 2 → V := fun t => (F.leaf t.1 t.2).val
  let B := insert v (insert (F.center 0).val (insert (F.center 1).val (C.image f)))
  let I := (G.neighborFinset r.val).filter (fun z => z ∈ N)
  have hsub : I ⊆ B := by
    intro z hz
    have hrz : G.Adj r.val z := (G.mem_neighborFinset r.val z).mp (Finset.mem_filter.mp hz).1
    rcases Finset.mem_insert.mp (Finset.mem_filter.mp hz).2 with hzv | hzv
    · exact Finset.mem_insert.mpr (Or.inl hzv)
    · let zz : G.neighborSet v := ⟨z, (G.mem_neighborFinset v z).mp hzv⟩
      rcases F.neighbor_cases zz with ⟨j, hj⟩ | ⟨i, e, hie⟩
      · have he : (F.center j).val = z := congrArg Subtype.val hj
        rw [← he]
        fin_cases j
        · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_insert.mpr (Or.inl rfl)))
        · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_insert.mpr
            (Or.inr (Finset.mem_insert.mpr (Or.inl rfl)))))
      · have he : (F.leaf i e).val = z := congrArg Subtype.val hie
        have hrleaf : G.Adj r.val (F.leaf i e).val := by rw [he]; exact hrz
        by_cases hir : i = rho.val
        · have hproper : neighborColor v c r ≠ neighborColor v c (F.leaf i e) :=
            c.valid (show (G.induce {x | x ≠ v}).Adj
              ⟨r.val, r.property.ne.symm⟩
              ⟨(F.leaf i e).val, (F.leaf i e).property.ne.symm⟩ from hrleaf)
          apply (hproper ?_).elim
          change neighborColor v c (F.commonRep rho) = neighborColor v c (F.leaf i e)
          rw [F.commonRep_color, F.leaf_color, hir]
        · by_cases hic : i ∈ F.commonColors
          · have hm : (i, e) ∈ C := Finset.mem_product.mpr
              ⟨Finset.mem_erase.mpr ⟨hir, hic⟩, Finset.mem_univ e⟩
            have him : z ∈ C.image f := Finset.mem_image.mpr ⟨(i, e), hm, he⟩
            exact Finset.mem_insert.mpr (Or.inr (Finset.mem_insert.mpr
              (Or.inr (Finset.mem_insert.mpr (Or.inr him)))))
          · exact (split_leaf_not_adj_commonRep hcrit hc hnot hv F i hic rho e hrleaf.symm).elim
  have hC : C.card = 2 * (F.commonColors.card - 1) := by
    simp only [C, Finset.card_product, Finset.card_univ, Fintype.card_fin,
      Finset.card_erase_of_mem rho.property]
    exact Nat.mul_comm _ _
  have himg : (C.image f).card ≤ C.card := Finset.card_image_le
  have hb0 := Finset.card_insert_le v (insert (F.center 0).val (insert (F.center 1).val (C.image f)))
  have hb1 := Finset.card_insert_le (F.center 0).val (insert (F.center 1).val (C.image f))
  have hb2 := Finset.card_insert_le (F.center 1).val (C.image f)
  have hI : I.card ≤ 3 + 2 * (F.commonColors.card - 1) := by
    have hh := Finset.card_le_card hsub
    change I.card ≤ (insert v (insert (F.center 0).val (insert (F.center 1).val (C.image f)))).card at hh
    omega
  have hdeg := equality_noncomplete_degree_ge_twelve hcrit hc hnot r.val
  have hp := Finset.card_filter_add_card_filter_not (s := G.neighborFinset r.val)
    (p := fun z => z ∈ N)
  rw [G.card_neighborFinset_eq_degree] at hp
  change I.card + ((G.neighborFinset r.val).filter (fun z => z ∉ N)).card = G.degree r.val at hp
  have hpos : 1 ≤ F.commonColors.card := Finset.one_le_card.mpr ⟨rho.val, rho.property⟩
  change 11 ≤ ((G.neighborFinset r.val).filter (fun z => z ∉ N)).card + 2 * F.commonColors.card
  omega

end TaskH.Seven
#print axioms TaskH.Seven.commonRep_outside_card_lower
