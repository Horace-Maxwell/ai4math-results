import Research.TaskH.Seven.SevenSplitAdjacentCenters
import Research.TaskH.FiniteBudget

/-! Actual degree partition and incidence count exclude an edge between the
two centers. The outside set is the full complement of the root neighborhood.
No row budget or outside cover is assumed in the original-graph wrapper. -/

set_option autoImplicit false
universe u
namespace TaskH.Seven
open SimpleGraph _root_.TaskH.Challenge
open scoped Classical BigOperators
variable {V : Type u} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem DegreeTwelveFrame.adjacent_centers_A_outside_at_least_nine
    (hcrit : IsCriticalPlus 7 G) (hc : modCycleCount 7 G = 2880)
    (hnot : ¬ IsCompleteOfOrder G 8) {v : V}
    {c : (G.induce {x | x ≠ v}).Coloring (Fin 7)}
    (F : DegreeTwelveFrame G v c) (hF : F.IsPureSplit)
    (hab : G.Adj (F.center 0).val (F.center 1).val) (i : Fin 5) :
    9 ≤ ((rootOutside G v).filter (fun z => G.Adj (F.splitA i).val z)).card := by
  have hdec :
      (inferInstance : DecidableRel G.Adj) =
        (fun a b => Classical.propDecidable (G.Adj a b)) := by
    funext a b
    exact Subsingleton.elim _ _
  cases hdec
  classical
  have hr : RainbowSevenCycles G := equality_rainbowSevenCycles hcrit hc
  let a := (F.center 0).val
  let p := (F.splitA i).val
  let N := insert v (G.neighborFinset v)
  let L := (Finset.univ : Finset (Fin 5)).filter
    (fun j => G.Adj p (F.splitA j).val)
  let I := (G.neighborFinset p).filter (fun z => z ∈ N)
  let T := insert v (insert a (L.image (fun j => (F.splitA j).val)))
  have hL : L.card ≤ 1 := F.adjacent_centers_A_internal_capacity hr hF hab i
  have hi := F.splitAB_adjacencies i (hF i)
  have hsub : I ⊆ T := by
    intro z hz
    obtain ⟨hzp, hzN⟩ := Finset.mem_filter.mp hz
    have hzp' : G.Adj p z := (G.mem_neighborFinset p z).mp hzp
    rcases Finset.mem_insert.mp hzN with he | hzv
    · exact Finset.mem_insert.mpr (Or.inl he)
    · let zz : G.neighborSet v := ⟨z, (G.mem_neighborFinset v z).mp hzv⟩
      rcases F.split_neighbor_cases zz with ⟨j, hj⟩ | ⟨j, hj | hj⟩
      · change z = (F.center j).val at hj
        fin_cases j
        · exact Finset.mem_insert.mpr (Or.inr
            (Finset.mem_insert.mpr (Or.inl hj)))
        · exact False.elim (hi.2.1 (by rw [hj] at hzp'; exact hzp'.symm))
      · change z = (F.splitA j).val at hj
        have hjL : j ∈ L := Finset.mem_filter.mpr
          ⟨Finset.mem_univ j, by rw [hj] at hzp'; exact hzp'⟩
        exact Finset.mem_insert.mpr (Or.inr (Finset.mem_insert.mpr
          (Or.inr (Finset.mem_image.mpr ⟨j, hjL, hj.symm⟩))))
      · change z = (F.splitB j).val at hj
        exact False.elim (F.pureSplit_cross_not_adj hr hF i j
          (by rw [hj] at hzp'; exact hzp'))
  have himage : (L.image (fun j => (F.splitA j).val)).card ≤ L.card :=
    Finset.card_image_le
  have hinner := Finset.card_insert_le a (L.image (fun j => (F.splitA j).val))
  have houter := Finset.card_insert_le v (insert a (L.image (fun j => (F.splitA j).val)))
  have hI : I.card ≤ 3 := by
    have hh := Finset.card_le_card hsub
    change I.card ≤ (insert v (insert a (L.image (fun j => (F.splitA j).val)))).card at hh
    omega
  have hpartition := Finset.card_filter_add_card_filter_not (s := G.neighborFinset p)
    (p := fun z => z ∈ N)
  have hout : ((G.neighborFinset p).filter (fun z => z ∉ N)) =
      (rootOutside G v).filter (fun z => G.Adj p z) := by
    ext z
    simp only [rootOutside, Finset.mem_filter, Finset.mem_compl, G.mem_neighborFinset]
    change (G.Adj p z ∧ z ∉ N) ↔ (z ∉ N ∧ G.Adj p z)
    exact and_comm
  rw [hout, G.card_neighborFinset_eq_degree] at hpartition
  have hd := equality_noncomplete_degree_ge_twelve hcrit hc hnot p
  change I.card + ((rootOutside G v).filter (fun z => G.Adj p z)).card = G.degree p
    at hpartition
  change 9 ≤ ((rootOutside G v).filter (fun z => G.Adj p z)).card
  omega

theorem equality_degreeTwelve_centers_not_adj
    (hcrit : IsCriticalPlus 7 G) (hc : modCycleCount 7 G = 2880)
    (hnot : ¬ IsCompleteOfOrder G 8) {v : V}
    {c : (G.induce {x | x ≠ v}).Coloring (Fin 7)} (hv : G.degree v = 12)
    (F : DegreeTwelveFrame G v c) (hF : F.IsPureSplit) :
    ¬ G.Adj (F.center 0).val (F.center 1).val := by
  have hdec :
      (inferInstance : DecidableRel G.Adj) =
        (fun a b => Classical.propDecidable (G.Adj a b)) := by
    funext a b
    exact Subsingleton.elim _ _
  cases hdec
  classical
  intro hab
  have hr : RainbowSevenCycles G := equality_rainbowSevenCycles hcrit hc
  let O := rootOutside G v
  let R : Fin 5 → V → Prop := fun i z => G.Adj (F.splitA i).val z
  have hrow : ∀ i ∈ (Finset.univ : Finset (Fin 5)), 9 ≤ (O.filter (R i)).card := by
    intro i _hi
    exact F.adjacent_centers_A_outside_at_least_nine hcrit hc hnot hF hab i
  have hcol : ∀ z ∈ O, ((Finset.univ : Finset (Fin 5)).filter
      (fun i => R i z)).card ≤ 1 := by
    intro z hz
    have hfilter : ((Finset.univ : Finset (Fin 5)).filter (fun i => R i z)) =
        ((Finset.univ : Finset (Fin 5)).filter
          (fun i => G.Adj z (F.splitA i).val)) := by
      ext i
      simp only [Finset.mem_filter, R, G.adj_comm]
    rw [hfilter]
    exact F.adjacent_centers_outside_A_capacity hr hF hab z hz
  have hdouble := FiniteBudget.relation_double_count (Finset.univ : Finset (Fin 5)) O R
  have hlo : 45 ≤ ∑ i : Fin 5, (O.filter (R i)).card := by
    calc
      45 = ∑ _i : Fin 5, 9 := by norm_num
      _ ≤ _ := Finset.sum_le_sum hrow
  have hhi : (∑ z ∈ O, ((Finset.univ : Finset (Fin 5)).filter
      (fun i => R i z)).card) ≤ O.card := by
    calc
      _ ≤ ∑ _z ∈ O, 1 := Finset.sum_le_sum hcol
      _ = _ := by simp
  have hO : O.card ≤ 33 :=
    equality_degree_twelve_outside_closed_card_le_thirty_three hcrit hc hnot v hv
  rw [hdouble] at hlo
  omega

end TaskH.Seven

#print axioms TaskH.Seven.DegreeTwelveFrame.adjacent_centers_A_outside_at_least_nine
#print axioms TaskH.Seven.equality_degreeTwelve_centers_not_adj
