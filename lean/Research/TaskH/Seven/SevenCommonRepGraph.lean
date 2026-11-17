import Research.TaskH.Seven.SevenCommonCrossingCycles
import Mathlib.Combinatorics.SimpleGraph.Extremal.Turan

/-! The actual common-representative graph is pulled back to the REAL common
color subtype. K5-free proves it triangle-free; symbolic Mantel is Mathlib's
Turán bound at r=2, without graph enumeration. -/

set_option autoImplicit false
universe u
namespace TaskH.Seven
open SimpleGraph _root_.TaskH.Challenge
open scoped Classical
variable {V : Type u} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable def commonRepGraph {v : V}
    {c : (G.induce {x | x ≠ v}).Coloring (Fin 7)}
    (F : DegreeTwelveFrame G v c) : SimpleGraph ↥F.commonColors :=
  G.comap (fun i => (F.commonRep i).val)

theorem DegreeTwelveFrame.commonRep_val_injective {v : V}
    {c : (G.induce {x | x ≠ v}).Coloring (Fin 7)}
    (F : DegreeTwelveFrame G v c) : Function.Injective (fun i : ↥F.commonColors => (F.commonRep i).val) := by
  intro i j he
  have hh := congrArg (neighborColor v c) (Subtype.ext he)
  rw [F.commonRep_color, F.commonRep_color] at hh
  exact Subtype.ext (F.pairIndex.injective (Subtype.ext hh))

theorem commonRepGraph_cliqueFree_three
    (hfree : G.CliqueFree 5) {v : V}
    {c : (G.induce {x | x ≠ v}).Coloring (Fin 7)}
    (F : DegreeTwelveFrame G v c) : (commonRepGraph F).CliqueFree 3 := by
  classical
  intro S hS
  let e : Fin 3 ≃ ↥S := (Finset.equivFinOfCardEq hS.2).symm
  let q : Fin 3 → V := fun i => (F.commonRep (e i).val).val
  have hq : Function.Injective q := by
    intro i j he
    apply e.injective
    exact Subtype.ext (F.commonRep_val_injective he)
  have hvq : ∀ i, G.Adj v (q i) := fun i => (F.commonRep (e i).val).property
  have hqq : ∀ i j, i ≠ j → G.Adj (q i) (q j) := by
    intro i j hij
    exact hS.1 (e i).property (e j).property
      (fun he => hij (e.injective (Subtype.ext he)))
  have hxq : ∀ i, (F.center 0).val ≠ q i := by
    intro i
    exact F.center_leaf_ne 0 (e i).val.val (F.commonRepSide (e i).val)
  have hfull : centerLabels G q (F.center 0).val = Finset.univ := by
    ext i
    simp only [centerLabels, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun _ => trivial, fun _ => F.commonRep_adj_zero (e i).val⟩
  exact cliqueFree_five_center_label_proper hfree v (F.center 0).val q hq
    (F.center 0).property hvq hxq hqq hfull

theorem commonRepGraph_sum_degrees_le
    (hfree : G.CliqueFree 5) {v : V}
    {c : (G.induce {x | x ≠ v}).Coloring (Fin 7)}
    (F : DegreeTwelveFrame G v c) :
    (∑ i : ↥F.commonColors, (commonRepGraph F).degree i) ≤
      2 * (F.commonColors.card ^ 2 / 4) := by
  classical
  have hh : (commonRepGraph F).edgeFinset.card ≤
      SimpleGraph.turanNumber (Fintype.card ↥F.commonColors) 2 :=
    (commonRepGraph_cliqueFree_three hfree F).card_edgeFinset_le
  rw [SimpleGraph.turanNumber_two, Fintype.card_coe] at hh
  rw [(commonRepGraph F).sum_degrees_eq_twice_card_edges]
  exact Nat.mul_le_mul_left 2 hh

noncomputable def commonRepOutsideDegree {v : V}
    {c : (G.induce {x | x ≠ v}).Coloring (Fin 7)}
    (F : DegreeTwelveFrame G v c) (i : ↥F.commonColors) : ℕ :=
  ((G.neighborFinset (F.commonRep i).val).filter
    (fun z => z ∉ insert v (G.neighborFinset v))).card

theorem commonRep_outside_add_internal_degree_ge_nine
    (hcrit : IsCriticalPlus 7 G) (hc : modCycleCount 7 G = 2880)
    (hnot : ¬ IsCompleteOfOrder G 8) {v : V}
    {c : (G.induce {x | x ≠ v}).Coloring (Fin 7)} (hv : G.degree v = 12)
    (F : DegreeTwelveFrame G v c) (i : ↥F.commonColors) :
    9 ≤ commonRepOutsideDegree F i + (commonRepGraph F).degree i := by
  classical
  let r := F.commonRep i
  let N := insert v (G.neighborFinset v)
  let A := (commonRepGraph F).neighborFinset i
  let f : ↥F.commonColors → V := fun j => (F.commonRep j).val
  let B := insert v (insert (F.center 0).val (insert (F.center 1).val (A.image f)))
  let I := (G.neighborFinset r.val).filter (fun z => z ∈ N)
  have hsub : I ⊆ B := by
    intro z hz
    have hrz := (G.mem_neighborFinset r.val z).mp (Finset.mem_filter.mp hz).1
    rcases Finset.mem_insert.mp (Finset.mem_filter.mp hz).2 with hzv | hzv
    · exact Finset.mem_insert.mpr (Or.inl hzv)
    · let zz : G.neighborSet v := ⟨z, (G.mem_neighborFinset v z).mp hzv⟩
      rcases commonRep_internal_neighbor_cases hcrit hc hnot hv F i zz hrz with h0 | h1 | ⟨j, hj⟩
      · have he : z = (F.center 0).val := congrArg Subtype.val h0
        exact Finset.mem_insert.mpr (Or.inr (Finset.mem_insert.mpr (Or.inl he)))
      · have he : z = (F.center 1).val := congrArg Subtype.val h1
        exact Finset.mem_insert.mpr (Or.inr (Finset.mem_insert.mpr
          (Or.inr (Finset.mem_insert.mpr (Or.inl he)))))
      · have he : z = (F.commonRep j).val := congrArg Subtype.val hj
        have ha : j ∈ A := by
          apply ((commonRepGraph F).mem_neighborFinset i j).mpr
          change G.Adj r.val (F.commonRep j).val
          rw [← he]
          exact hrz
        have hm : z ∈ A.image f := Finset.mem_image.mpr ⟨j, ha, he.symm⟩
        exact Finset.mem_insert.mpr (Or.inr (Finset.mem_insert.mpr
          (Or.inr (Finset.mem_insert.mpr (Or.inr hm)))))
  have hI : I.card ≤ 3 + (commonRepGraph F).degree i := by
    have hh := Finset.card_le_card hsub
    have him : (A.image f).card ≤ A.card := Finset.card_image_le
    have h0 := Finset.card_insert_le v (insert (F.center 0).val (insert (F.center 1).val (A.image f)))
    have h1 := Finset.card_insert_le (F.center 0).val (insert (F.center 1).val (A.image f))
    have h2 := Finset.card_insert_le (F.center 1).val (A.image f)
    have hA : A.card = (commonRepGraph F).degree i := (commonRepGraph F).card_neighborFinset_eq_degree i
    change I.card ≤ (insert v (insert (F.center 0).val (insert (F.center 1).val (A.image f)))).card at hh
    omega
  have hd := equality_noncomplete_degree_ge_twelve hcrit hc hnot r.val
  have hp := Finset.card_filter_add_card_filter_not (s := G.neighborFinset r.val) (p := fun z => z ∈ N)
  rw [G.card_neighborFinset_eq_degree] at hp
  change I.card + commonRepOutsideDegree F i = G.degree r.val at hp
  omega

theorem commonRep_total_outside_mantel_budget
    (hcrit : IsCriticalPlus 7 G) (hc : modCycleCount 7 G = 2880)
    (hnot : ¬ IsCompleteOfOrder G 8) {v : V}
    {c : (G.induce {x | x ≠ v}).Coloring (Fin 7)} (hv : G.degree v = 12)
    (F : DegreeTwelveFrame G v c) :
    9 * F.commonColors.card ≤ (∑ i : ↥F.commonColors, commonRepOutsideDegree F i) +
      2 * (F.commonColors.card ^ 2 / 4) := by
  classical
  have hlow : 9 * F.commonColors.card ≤
      (∑ i : ↥F.commonColors, commonRepOutsideDegree F i) +
        ∑ i : ↥F.commonColors, (commonRepGraph F).degree i := by
    calc
      _ = ∑ _i : ↥F.commonColors, 9 := by simp [Nat.mul_comm]
      _ ≤ ∑ i : ↥F.commonColors, (commonRepOutsideDegree F i + (commonRepGraph F).degree i) :=
        Finset.sum_le_sum (fun i _ => commonRep_outside_add_internal_degree_ge_nine hcrit hc hnot hv F i)
      _ = _ := Finset.sum_add_distrib
  have hhigh := commonRepGraph_sum_degrees_le (equality_cliqueFree_five hcrit hc hnot) F
  omega

end TaskH.Seven
#print axioms TaskH.Seven.commonRepGraph
#print axioms TaskH.Seven.DegreeTwelveFrame.commonRep_val_injective
#print axioms TaskH.Seven.commonRepGraph_cliqueFree_three
#print axioms TaskH.Seven.commonRepGraph_sum_degrees_le
#print axioms TaskH.Seven.commonRepOutsideDegree
#print axioms TaskH.Seven.commonRep_outside_add_internal_degree_ge_nine
#print axioms TaskH.Seven.commonRep_total_outside_mantel_budget
