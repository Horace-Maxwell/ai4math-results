import Research.TaskH.Seven.SevenSplitPoolCapacity

/-! Actual finite coordinate/outside incidence. Coordinate injectivity was
proved from real neighbor fibers; no leaf multiplicity is silently counted. -/

set_option autoImplicit false
universe u
namespace TaskH.Seven
open SimpleGraph _root_.TaskH.Challenge
open scoped Classical
variable {V : Type u} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem split_leaf_outside_card_ge_ten
    (hcrit : IsCriticalPlus 7 G) (hc : modCycleCount 7 G = 2880)
    (hnot : ¬ IsCompleteOfOrder G 8) {v : V}
    {c : (G.induce {x | x ≠ v}).Coloring (Fin 7)} (hv : G.degree v = 12)
    (F : DegreeTwelveFrame G v c) (hcommon : F.commonColors.Nonempty)
    (gamma : Fin 5) (hg : gamma ∉ F.commonColors) (e : Fin 2) :
    10 ≤ ((G.neighborFinset (F.leaf gamma e).val).filter
      (fun z => z ∉ insert v (G.neighborFinset v))).card := by
  obtain ⟨rho, hrho⟩ := hcommon
  have hgr : gamma ≠ rho := by intro he; exact hg (he.symm ▸ hrho)
  obtain ⟨er, hra, hrb⟩ := (Finset.mem_filter.mp hrho).2
  have hs := F.splitPair_of_not_common hcrit hc hnot hv gamma hg
  rcases hs with h | h
  · fin_cases e
    · exact degreeTwelve_common_split_leaf_outside_card_ge_ten hcrit hc hnot hv F
        gamma rho hgr 0 1 er (by decide) h.1 h.2.1 h.2.2.1 hra hrb
    · exact degreeTwelve_common_split_other_leaf_outside_card_ge_ten hcrit hc hnot hv F
        gamma rho hgr 0 1 er (by decide) h.1 h.2.2.1 h.2.2.2 hra hrb
  · fin_cases e
    · exact degreeTwelve_common_split_other_leaf_outside_card_ge_ten hcrit hc hnot hv F
        gamma rho hgr 1 0 er (by decide) h.1 h.2.2.1 h.2.2.2 hra hrb
    · exact degreeTwelve_common_split_leaf_outside_card_ge_ten hcrit hc hnot hv F
        gamma rho hgr 1 0 er (by decide) h.1 h.2.1 h.2.2.1 hra hrb

noncomputable def splitLeafCoordinates {v : V}
    {c : (G.induce {x | x ≠ v}).Coloring (Fin 7)}
    (F : DegreeTwelveFrame G v c) : Finset (Fin 5 × Fin 2) :=
  F.commonColorsᶜ ×ˢ Finset.univ

theorem splitLeafCoordinates_card {v : V}
    {c : (G.induce {x | x ≠ v}).Coloring (Fin 7)}
    (F : DegreeTwelveFrame G v c) :
    (splitLeafCoordinates F).card = 2 * (F.commonColorsᶜ).card := by
  simp only [splitLeafCoordinates, Finset.card_product, Finset.card_univ, Fintype.card_fin]
  exact Nat.mul_comm _ _

theorem split_leaf_outside_incidence_lower
    (hcrit : IsCriticalPlus 7 G) (hc : modCycleCount 7 G = 2880)
    (hnot : ¬ IsCompleteOfOrder G 8) {v : V}
    {c : (G.induce {x | x ≠ v}).Coloring (Fin 7)} (hv : G.degree v = 12)
    (F : DegreeTwelveFrame G v c) (hcommon : F.commonColors.Nonempty) :
    20 * (F.commonColorsᶜ).card ≤
      ∑ z ∈ ((insert v (G.neighborFinset v))ᶜ : Finset V), (splitPoolHits F z).card := by
  have hdec :
      (inferInstance : DecidableRel G.Adj) =
        (fun a b => Classical.propDecidable (G.Adj a b)) := by
    funext a b
    exact Subsingleton.elim _ _
  cases hdec
  classical
  let L := splitLeafCoordinates F
  let O := (insert v (G.neighborFinset v))ᶜ
  let R : (Fin 5 × Fin 2) → V → Prop := fun t z => G.Adj (F.leaf t.1 t.2).val z
  have hrow : ∀ t ∈ L, 10 ≤ (O.filter (R t)).card := by
    intro t ht
    have hts := (Finset.mem_product.mp ht).1
    have he : O.filter (R t) = (G.neighborFinset (F.leaf t.1 t.2).val).filter
        (fun z => z ∉ insert v (G.neighborFinset v)) := by
      ext z
      simp only [O, R, Finset.mem_filter, Finset.mem_compl, G.mem_neighborFinset]
      exact and_comm
    rw [he]
    exact split_leaf_outside_card_ge_ten hcrit hc hnot hv F hcommon t.1
      (Finset.mem_compl.mp hts) t.2
  have hcol : ∀ z, L.filter (fun t => R t z) = splitPoolHits F z := by
    intro z
    ext t
    simp only [L, splitLeafCoordinates, R, splitPoolHits, Finset.mem_filter,
      Finset.mem_product, Finset.mem_compl, Finset.mem_univ, and_true, true_and]
    exact and_congr_right (fun _ => G.adj_comm (F.leaf t.1 t.2).val z)
  have hd := FiniteBudget.relation_double_count L O R
  have hlo : L.card * 10 ≤ ∑ t ∈ L, (O.filter (R t)).card := by
    calc
      _ = ∑ _t ∈ L, 10 := by simp
      _ ≤ _ := Finset.sum_le_sum hrow
  have he : (∑ t ∈ L, (O.filter (R t)).card) =
      ∑ z ∈ O, (splitPoolHits F z).card := by
    calc
      _ = ∑ z ∈ O, (L.filter (fun t => R t z)).card := hd
      _ = _ := Finset.sum_congr rfl (fun z _ => congrArg Finset.card (hcol z))
  rw [he, splitLeafCoordinates_card] at hlo
  change 20 * (F.commonColorsᶜ).card ≤ ∑ z ∈ O, (splitPoolHits F z).card
  omega

theorem equality_degreeTwelve_commonColors_card_ne_three
    (hcrit : IsCriticalPlus 7 G) (hc : modCycleCount 7 G = 2880)
    (hnot : ¬ IsCompleteOfOrder G 8) (v : V)
    (c : (G.induce {x | x ≠ v}).Coloring (Fin 7)) (hv : G.degree v = 12)
    (F : DegreeTwelveFrame G v c) : F.commonColors.card ≠ 3 := by
  classical
  intro hthree
  have hcommon : F.commonColors.Nonempty := Finset.card_pos.mp (by omega)
  have hcomp : (F.commonColorsᶜ).card = 2 := by
    have hh := Finset.card_add_card_compl F.commonColors
    rw [hthree] at hh
    norm_num at hh
    omega
  have hlo := split_leaf_outside_incidence_lower hcrit hc hnot hv F hcommon
  rw [hcomp] at hlo
  let O := ((insert v (G.neighborFinset v))ᶜ : Finset V)
  have hrow : ∀ z ∈ O, (splitPoolHits F z).card ≤ 1 := by
    intro z hz
    have hzout := Finset.mem_compl.mp hz
    have hzv : z ≠ v := by intro he; exact hzout (Finset.mem_insert.mpr (Or.inl he))
    have hh := splitPoolHits_card_lt_splitColors hcrit hc hnot hv F hcommon
      (by omega) ⟨z, hzv⟩ hzout
    rw [hcomp] at hh
    change (splitPoolHits F z).card < 2 at hh
    omega
  have hhi : (∑ z ∈ O, (splitPoolHits F z).card) ≤ O.card := by
    calc
      _ ≤ ∑ _z ∈ O, 1 := Finset.sum_le_sum hrow
      _ = _ := by simp
  have hn := equality_degree_twelve_outside_closed_card_le_thirty_three hcrit hc hnot v hv
  change O.card ≤ 33 at hn
  change 20 * 2 ≤ ∑ z ∈ O, (splitPoolHits F z).card at hlo
  omega

end TaskH.Seven
#print axioms TaskH.Seven.split_leaf_outside_card_ge_ten
#print axioms TaskH.Seven.splitLeafCoordinates
#print axioms TaskH.Seven.splitLeafCoordinates_card
#print axioms TaskH.Seven.split_leaf_outside_incidence_lower
#print axioms TaskH.Seven.equality_degreeTwelve_commonColors_card_ne_three
