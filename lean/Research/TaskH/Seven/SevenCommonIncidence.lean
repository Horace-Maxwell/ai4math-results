import Research.TaskH.Seven.SevenCommonRepGraph

/-! Actual representative/outside finite incidence, and h5 capacity one.
The full five-representative API is invoked ONLY after h=5 is proved. -/

set_option autoImplicit false
universe u
namespace TaskH.Seven
open SimpleGraph _root_.TaskH.Challenge
open scoped Classical
variable {V : Type u} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable def commonPoolHits {v : V}
    {c : (G.induce {x | x ≠ v}).Coloring (Fin 7)}
    (F : DegreeTwelveFrame G v c) (z : V) : Finset ↥F.commonColors :=
  Finset.univ.filter (fun i => G.Adj z (F.commonRep i).val)

theorem mem_commonPoolHits {v : V}
    {c : (G.induce {x | x ≠ v}).Coloring (Fin 7)}
    (F : DegreeTwelveFrame G v c) (z : V) (i : ↥F.commonColors) :
    i ∈ commonPoolHits F z ↔ G.Adj z (F.commonRep i).val := by
  simp only [commonPoolHits, Finset.mem_filter, Finset.mem_univ, true_and]

theorem common_outside_incidence_double_count {v : V}
    {c : (G.induce {x | x ≠ v}).Coloring (Fin 7)}
    (F : DegreeTwelveFrame G v c) :
    (∑ i : ↥F.commonColors, commonRepOutsideDegree F i) =
      ∑ z ∈ ((insert v (G.neighborFinset v))ᶜ : Finset V), (commonPoolHits F z).card := by
  have hdec :
      (inferInstance : DecidableRel G.Adj) =
        (fun a b => Classical.propDecidable (G.Adj a b)) := by
    funext a b
    exact Subsingleton.elim _ _
  cases hdec
  classical
  let O := ((insert v (G.neighborFinset v))ᶜ : Finset V)
  let A : Finset ↥F.commonColors := Finset.univ
  let R : ↥F.commonColors → V → Prop := fun i z => G.Adj z (F.commonRep i).val
  have hrow : ∀ i, commonRepOutsideDegree F i = (O.filter (R i)).card := by
    intro i
    have he : (G.neighborFinset (F.commonRep i).val).filter
        (fun z => z ∉ insert v (G.neighborFinset v)) = O.filter (R i) := by
      ext z
      simp only [O, R, Finset.mem_filter, G.mem_neighborFinset, Finset.mem_compl]
      exact ⟨fun h => ⟨h.2, h.1.symm⟩, fun h => ⟨h.2.symm, h.1⟩⟩
    exact congrArg Finset.card he
  calc
    _ = ∑ i ∈ A, (O.filter (R i)).card := Finset.sum_congr rfl (fun i _ => hrow i)
    _ = ∑ z ∈ O, (A.filter (fun i => R i z)).card := FiniteBudget.relation_double_count A O R
    _ = _ := rfl

theorem commonColors_eq_univ_of_card_five {v : V}
    {c : (G.induce {x | x ≠ v}).Coloring (Fin 7)}
    (F : DegreeTwelveFrame G v c) (hfive : F.commonColors.card = 5) :
    F.commonColors = Finset.univ := by
  apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
  simpa only [Finset.card_univ, Fintype.card_fin, hfive] using
    (le_rfl : (5 : ℕ) ≤ 5)

theorem commonPoolHits_card_le_one_of_card_five
    (hr : RainbowSevenCycles G) {v : V}
    {c : (G.induce {x | x ≠ v}).Coloring (Fin 7)}
    (F : DegreeTwelveFrame G v c) (hfive : F.commonColors.card = 5)
    (z : {x : V // x ≠ v}) (hz : z.val ∉ insert v (G.neighborFinset v)) :
    (commonPoolHits F z.val).card ≤ 1 := by
  classical
  have hfull := commonColors_eq_univ_of_card_five F hfive
  let e : Fin 5 → ↥F.commonColors := fun i => ⟨i, by rw [hfull]; exact Finset.mem_univ i⟩
  let r : Fin 5 → G.neighborSet v := fun i => F.commonRep (e i)
  have hrcolor : ∀ i, neighborColor v c (r i) = (F.pairIndex i).val := fun i => F.commonRep_color (e i)
  have hra : ∀ i, G.Adj (F.center 0).val (r i).val := fun i => F.commonRep_adj_zero (e i)
  have hrb : ∀ i, G.Adj (F.center 1).val (r i).val := fun i => F.commonRep_adj_one (e i)
  have hcap := all_common_representatives_outside_at_most_one hr F r hrcolor hra hrb z hz
  have hle : (commonPoolHits F z.val).card ≤
      ((Finset.univ : Finset (Fin 5)).filter (fun i => G.Adj z.val (r i).val)).card := by
    apply Finset.card_le_card_of_injOn (fun i : ↥F.commonColors => i.val)
    · intro i hi
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ i.val, (mem_commonPoolHits F z.val i).mp hi⟩
    · intro i _hi j _hj he
      exact Subtype.ext he
  exact hle.trans hcap

end TaskH.Seven
#print axioms TaskH.Seven.commonPoolHits
#print axioms TaskH.Seven.mem_commonPoolHits
#print axioms TaskH.Seven.common_outside_incidence_double_count
#print axioms TaskH.Seven.commonColors_eq_univ_of_card_five
#print axioms TaskH.Seven.commonPoolHits_card_le_one_of_card_five
