import Research.TaskH.Seven.SevenSingletonOrderFamilies
import Research.TaskH.Seven.SevenEqualityBasics
import Research.TaskH.Seven.SevenNoncompleteDegree
import Mathlib.Algebra.BigOperators.Ring.Finset

/-! Actual deleted-color-class incidence budgets. A class is a finite set of
actual deleted vertices, and every counted circle is an original edge set. -/

set_option autoImplicit false
universe u
namespace TaskH.Seven
open SimpleGraph _root_.TaskH.Challenge
open scoped Classical
variable {V : Type u} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable def deletedColorClass (v : V)
    (c : (G.induce {x | x ≠ v}).Coloring (Fin 7)) (i : Fin 7) :
    Finset {x : V // x ≠ v} := by
  classical
  exact Finset.univ.filter (fun z => c z = i)

theorem mem_deletedColorClass (v : V)
    (c : (G.induce {x | x ≠ v}).Coloring (Fin 7)) (i : Fin 7)
    (z : {x : V // x ≠ v}) : z ∈ deletedColorClass v c i ↔ c z = i := by
  cases (inferInstance : DecidableRel G.Adj) v v with
  | isTrue hvv => exact (G.loopless.irrefl v hvv).elim
  | isFalse _ =>
    classical
    simp only [deletedColorClass, Finset.mem_filter, Finset.mem_univ, true_and]

theorem deletedColorClass_circle_hit_card_le_one
    (hs : ShortSevenCycles G) (hr : RainbowSevenCycles G)
    (v : V) (c : (G.induce {x | x ≠ v}).Coloring (Fin 7)) (i : Fin 7)
    {s : Finset (Sym2 V)} (hmem : s ∈ cycleFinset G) :
    ((deletedColorClass v c i).filter (fun z => CycleContains s z.val)).card ≤ 1 := by
  classical
  obtain ⟨x, p, hp, he, hk⟩ := Basics.mem_modCycleEdgeSets_iff.mp
    ((mem_cycleFinset s).mp hmem)
  have hlen := hs p hp hk
  apply Finset.card_le_one.mpr
  intro a ha b hb
  have hac := (mem_deletedColorClass v c i a).mp (Finset.mem_filter.mp ha).1
  have hbc := (mem_deletedColorClass v c i b).mp (Finset.mem_filter.mp hb).1
  have hap : a.val ∈ p.support := by
    apply (TaskH.cycleContains_edges_toFinset_iff p hp.not_nil a.val).mp
    simpa only [he] using (Finset.mem_filter.mp ha).2
  have hbp : b.val ∈ p.support := by
    apply (TaskH.cycleContains_edges_toFinset_iff p hp.not_nil b.val).mp
    simpa only [he] using (Finset.mem_filter.mp hb).2
  exact hr v c p hp hlen a b hap hbp (hac.trans hbc.symm)

theorem deletedColorClass_incidence_double_count (v : V)
    (c : (G.induce {x | x ≠ v}).Coloring (Fin 7)) (i : Fin 7) :
    (∑ z ∈ deletedColorClass v c i, cycleDegree G z.val) =
      ∑ s ∈ cycleFinset G,
        ((deletedColorClass v c i).filter (fun z => CycleContains s z.val)).card := by
  cases (inferInstance : DecidableRel G.Adj) v v with
  | isTrue hvv => exact (G.loopless.irrefl v hvv).elim
  | isFalse _ =>
    classical
    exact FiniteBudget.relation_double_count (deletedColorClass v c i)
      (cycleFinset G) (fun z s => CycleContains s z.val)

theorem deletedColorClass_incidence_le
    (hs : ShortSevenCycles G) (hr : RainbowSevenCycles G)
    (v : V) (c : (G.induce {x | x ≠ v}).Coloring (Fin 7)) (i : Fin 7) :
    (∑ z ∈ deletedColorClass v c i, cycleDegree G z.val) ≤ modCycleCount 7 G := by
  classical
  rw [deletedColorClass_incidence_double_count]
  calc
    _ ≤ ∑ _s ∈ cycleFinset G, 1 :=
      Finset.sum_le_sum (fun _ hs' => deletedColorClass_circle_hit_card_le_one hs hr v c i hs')
    _ = _ := by simp [cycleFinset_card]

theorem singletonColorClass_incidence_le
    (hcrit : IsCriticalPlus 7 G) (hs : ShortSevenCycles G) (hr : RainbowSevenCycles G)
    (v : V) (c : (G.induce {x | x ≠ v}).Coloring (Fin 7))
    (i : ↥(singletonNeighborColors v c)) :
    (∑ z ∈ deletedColorClass v c i.val, cycleDegree G z.val) + 360 ≤
      modCycleCount 7 G := by
  classical
  let F := singletonOrderCycleFinset v c i
  have hsub : F ⊆ cycleFinset G := by
    intro s hsF
    exact ((mem_singletonOrderCycleFinset v c i s).mp hsF).1
  have hrow : ∀ s ∈ cycleFinset G,
      ((deletedColorClass v c i.val).filter (fun z => CycleContains s z.val)).card ≤
        if s ∈ F then 0 else 1 := by
    intro s hs'
    by_cases hF : s ∈ F
    · rw [ite_eq_left hF]
      have he : (deletedColorClass v c i.val).filter (fun z => CycleContains s z.val) = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro z hz
        have hc := (mem_deletedColorClass v c i.val z).mp (Finset.mem_filter.mp hz).1
        exact singletonOrderCycle_missing_entire_class v c i hF z hc (Finset.mem_filter.mp hz).2
      rw [he]
      exact le_rfl
    · rw [ite_eq_right hF]
      exact deletedColorClass_circle_hit_card_le_one hs hr v c i.val hs'
  have hh : (∑ z ∈ deletedColorClass v c i.val, cycleDegree G z.val) ≤
      ((cycleFinset G).filter (fun s => s ∉ F)).card := by
    rw [deletedColorClass_incidence_double_count]
    calc
      _ ≤ ∑ s ∈ cycleFinset G, if s ∈ F then 0 else 1 := Finset.sum_le_sum hrow
      _ = _ := by
        rw [Finset.card_eq_sum_ones, Finset.sum_filter]
        simp only [ite_not]
  have he : (cycleFinset G).filter (fun s => s ∈ F) = F := by
    ext s
    simp only [Finset.mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨hsub h, h⟩⟩
  have hpartition := Finset.card_filter_add_card_filter_not (s := cycleFinset G)
    (p := fun s => s ∈ F)
  rw [he, cycleFinset_card] at hpartition
  have hF : 360 ≤ F.card := singletonOrderCycleFinset_card_ge hcrit hs v c i
  omega

theorem equality_deletedColorClass_card_le_seven
    (hcrit : IsCriticalPlus 7 G) (hc : modCycleCount 7 G = 2880)
    (hnot : ¬ IsCompleteOfOrder G 8) (v : V)
    (c : (G.induce {x | x ≠ v}).Coloring (Fin 7)) (i : Fin 7) :
    (deletedColorClass v c i).card ≤ 7 := by
  classical
  have hs : ShortSevenCycles G := equality_shortSevenCycles hcrit hc
  have hr : RainbowSevenCycles G := equality_rainbowSevenCycles hcrit hc
  have hn := noncomplete_card_ge_nine hcrit hs hr hnot
  have hlow : (deletedColorClass v c i).card * 389 ≤
      ∑ z ∈ deletedColorClass v c i, cycleDegree G z.val := by
    calc
      _ = ∑ _z ∈ deletedColorClass v c i, 389 := by simp
      _ ≤ _ := Finset.sum_le_sum (fun z _ =>
        equality_three_hundred_eighty_nine_le_cycleDegree hcrit hc hn z.val)
  have hhigh := deletedColorClass_incidence_le hs hr v c i
  rw [hc] at hhigh
  omega

theorem equality_singletonColorClass_card_le_five
    (hcrit : IsCriticalPlus 7 G) (hc : modCycleCount 7 G = 2880)
    (hnot : ¬ IsCompleteOfOrder G 8) (v : V)
    (c : (G.induce {x | x ≠ v}).Coloring (Fin 7))
    (i j : ↥(singletonNeighborColors v c)) (hij : i ≠ j) :
    (deletedColorClass v c j.val).card ≤ 5 := by
  classical
  have hs : ShortSevenCycles G := equality_shortSevenCycles hcrit hc
  have hr : RainbowSevenCycles G := equality_rainbowSevenCycles hcrit hc
  have hn := noncomplete_card_ge_nine hcrit hs hr hnot
  let T := deletedColorClass v c j.val
  let z : {x : V // x ≠ v} :=
    ⟨(singletonNeighbor v c j).val, (singletonNeighbor v c j).property.ne.symm⟩
  have hz : z ∈ T := by
    apply (mem_deletedColorClass v c j.val z).mpr
    exact singletonNeighbor_color v c j
  have hspecial : 720 ≤ cycleDegree G z.val :=
    singleton_neighbor_cycleDegree_ge_seven_hundred_twenty hcrit hs hr v c i j hij
  have hrest : (T.erase z).card * 389 ≤ ∑ w ∈ T.erase z, cycleDegree G w.val := by
    calc
      _ = ∑ _w ∈ T.erase z, 389 := by simp
      _ ≤ _ := Finset.sum_le_sum (fun w _ =>
        equality_three_hundred_eighty_nine_le_cycleDegree hcrit hc hn w.val)
  have hsum := Finset.sum_erase_add T (fun w => cycleDegree G w.val) hz
  have hcard := Finset.card_erase_add_one hz
  have hhigh := singletonColorClass_incidence_le hcrit hs hr v c j
  rw [hc] at hhigh
  change (∑ w ∈ T, cycleDegree G w.val) + 360 ≤ 2880 at hhigh
  change T.card ≤ 5
  omega

end TaskH.Seven
#print axioms TaskH.Seven.deletedColorClass
#print axioms TaskH.Seven.mem_deletedColorClass
#print axioms TaskH.Seven.deletedColorClass_circle_hit_card_le_one
#print axioms TaskH.Seven.deletedColorClass_incidence_double_count
#print axioms TaskH.Seven.deletedColorClass_incidence_le
#print axioms TaskH.Seven.singletonColorClass_incidence_le
#print axioms TaskH.Seven.equality_deletedColorClass_card_le_seven
#print axioms TaskH.Seven.equality_singletonColorClass_card_le_five
