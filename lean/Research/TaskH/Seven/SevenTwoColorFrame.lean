import Research.TaskH.Seven.SevenSplitPairCoordinates
import Research.TaskH.Seven.SevenTwoColorSeven
import Research.TaskH.Seven.SevenK5Free

/-! Actual pure-split Frame coordinates and the original-graph detours.
Pure split is explicitly an INTERNAL condition here, not a new original
CaseSeven hypothesis and not a proved all-colorings conclusion. -/

set_option autoImplicit false
universe u
namespace TaskH.Seven
open SimpleGraph Challenge
open scoped Classical
variable {V : Type u} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]

def twoColorNeighborDeleted (v : V) (z : G.neighborSet v) : {x : V // x ≠ v} :=
  ⟨z.val, z.property.ne.symm⟩

noncomputable def DegreeTwelveFrame.centerD {v : V}
    {c : (G.induce {x | x ≠ v}).Coloring (Fin 7)}
    (F : DegreeTwelveFrame G v c) (j : Fin 2) : {x : V // x ≠ v} :=
  twoColorNeighborDeleted v (F.center j)

noncomputable def DegreeTwelveFrame.splitAD {v : V}
    {c : (G.induce {x | x ≠ v}).Coloring (Fin 7)}
    (F : DegreeTwelveFrame G v c) (i : Fin 5) : {x : V // x ≠ v} :=
  twoColorNeighborDeleted v (F.splitA i)

noncomputable def DegreeTwelveFrame.splitBD {v : V}
    {c : (G.induce {x | x ≠ v}).Coloring (Fin 7)}
    (F : DegreeTwelveFrame G v c) (i : Fin 5) : {x : V // x ≠ v} :=
  twoColorNeighborDeleted v (F.splitB i)

theorem DegreeTwelveFrame.pairColor_ne_singleton {v : V}
    {c : (G.induce {x | x ≠ v}).Coloring (Fin 7)}
    (F : DegreeTwelveFrame G v c) (i : Fin 5) (j : Fin 2) :
    (F.pairIndex i).val ≠ (F.singletonIndex j).val := by
  have hdec :
      (inferInstance : DecidableRel G.Adj) =
        (fun a b => Classical.propDecidable (G.Adj a b)) := by
    funext a b
    exact Subsingleton.elim _ _
  have hset : singletonNeighborColors v c =
      @singletonNeighborColors V (inferInstance : Fintype V) G
        (fun a b => Classical.propDecidable (G.Adj a b)) v c := by
    cases hdec
    rfl
  have hp : (F.pairIndex i).val ∉ singletonNeighborColors v c := by
    rw [hset]
    exact Finset.mem_compl.mp (F.pairIndex i).property
  have hs : (F.singletonIndex j).val ∈ singletonNeighborColors v c := by
    rw [hset]
    exact (F.singletonIndex j).property
  intro he
  exact hp (he.symm ▸ hs)

theorem DegreeTwelveFrame.pairColor_injective {v : V}
    {c : (G.induce {x | x ≠ v}).Coloring (Fin 7)}
    (F : DegreeTwelveFrame G v c) : Function.Injective (fun i => (F.pairIndex i).val) :=
by
  have hdec :
      (inferInstance : DecidableRel G.Adj) =
        (fun a b => Classical.propDecidable (G.Adj a b)) := by
    funext a b
    exact Subsingleton.elim _ _
  let E : Fin 5 ≃ ↥((singletonNeighborColors v c)ᶜ) := by
    cases hdec
    exact F.pairIndex
  have hE : ∀ i : Fin 5, (E i).val = (F.pairIndex i).val := by
    cases hdec
    intro i
    rfl
  intro i j he
  apply E.injective
  apply Subtype.ext
  exact ((hE i).trans he).trans (hE j).symm

theorem DegreeTwelveFrame.singletonColor_injective {v : V}
    {c : (G.induce {x | x ≠ v}).Coloring (Fin 7)}
    (F : DegreeTwelveFrame G v c) : Function.Injective (fun j => (F.singletonIndex j).val) :=
by
  have hdec :
      (inferInstance : DecidableRel G.Adj) =
        (fun a b => Classical.propDecidable (G.Adj a b)) := by
    funext a b
    exact Subsingleton.elim _ _
  let E : Fin 2 ≃ ↥(singletonNeighborColors v c) := by
    cases hdec
    exact F.singletonIndex
  have hE : ∀ j : Fin 2, (E j).val = (F.singletonIndex j).val := by
    cases hdec
    intro j
    rfl
  intro i j he
  apply E.injective
  apply Subtype.ext
  exact ((hE i).trans he).trans (hE j).symm

theorem DegreeTwelveFrame.splitA_injective {v : V}
    {c : (G.induce {x | x ≠ v}).Coloring (Fin 7)}
    (F : DegreeTwelveFrame G v c) : Function.Injective (fun i => (F.splitA i).val) := by
  intro i j he
  apply F.pairColor_injective
  have hh := congrArg (neighborColor v c) (Subtype.ext he)
  simpa only [F.splitA_color] using hh

theorem DegreeTwelveFrame.splitB_injective {v : V}
    {c : (G.induce {x | x ≠ v}).Coloring (Fin 7)}
    (F : DegreeTwelveFrame G v c) : Function.Injective (fun i => (F.splitB i).val) := by
  intro i j he
  apply F.pairColor_injective
  have hh := congrArg (neighborColor v c) (Subtype.ext he)
  simpa only [F.splitB_color] using hh

theorem DegreeTwelveFrame.center_splitA_ne {v : V}
    {c : (G.induce {x | x ≠ v}).Coloring (Fin 7)}
    (F : DegreeTwelveFrame G v c) (j : Fin 2) (i : Fin 5) :
    (F.center j).val ≠ (F.splitA i).val := by
  intro he
  apply F.pairColor_ne_singleton i j
  have hh := congrArg (neighborColor v c) (Subtype.ext he)
  simpa only [F.center_color, F.splitA_color] using hh.symm

theorem DegreeTwelveFrame.center_splitB_ne {v : V}
    {c : (G.induce {x | x ≠ v}).Coloring (Fin 7)}
    (F : DegreeTwelveFrame G v c) (j : Fin 2) (i : Fin 5) :
    (F.center j).val ≠ (F.splitB i).val := by
  intro he
  apply F.pairColor_ne_singleton i j
  have hh := congrArg (neighborColor v c) (Subtype.ext he)
  simpa only [F.center_color, F.splitB_color] using hh.symm

theorem DegreeTwelveFrame.splitA_splitB_ne {v : V}
    {c : (G.induce {x | x ≠ v}).Coloring (Fin 7)}
    (F : DegreeTwelveFrame G v c) (i j : Fin 5) :
    (F.splitA i).val ≠ (F.splitB j).val := by
  by_cases hij : i = j
  · subst j
    exact F.splitAB_ne i
  · intro he
    apply hij
    apply F.pairColor_injective
    have hh := congrArg (neighborColor v c) (Subtype.ext he)
    simpa only [F.splitA_color, F.splitB_color] using hh

theorem DegreeTwelveFrame.pureSplit_cross_not_adj
    (hr : RainbowSevenCycles G) {v : V}
    {c : (G.induce {x | x ≠ v}).Coloring (Fin 7)}
    (F : DegreeTwelveFrame G v c) (hF : F.IsPureSplit) (i j : Fin 5) :
    ¬ G.Adj (F.splitA i).val (F.splitB j).val := by
  intro he
  by_cases hij : i = j
  · subst j
    have he' : (G.induce {x | x ≠ v}).Adj
        (F.splitAD i) (F.splitBD i) := he
    have hc' : c (F.splitAD i) = c (F.splitBD i) :=
      (F.splitA_color i).trans (F.splitB_color i).symm
    exact (c.valid he') hc'
  · have hi := F.splitAB_adjacencies i (hF i)
    have hj := F.splitAB_adjacencies j (hF j)
    have hab := F.center_center_ne (by decide : (0 : Fin 2) ≠ 1)
    have hA := F.splitA_injective.ne hij
    have hB := F.splitB_injective.ne hij
    have hca := F.center_splitA_ne
    have hcb := F.center_splitB_ne
    have hcross := F.splitA_splitB_ne
    let t : Fin 6 → G.neighborSet v :=
      ![F.splitB i, F.center 1, F.splitB j, F.splitA i, F.center 0, F.splitA j]
    have ht : Function.Injective t := by
      change Function.Injective ![F.splitB i, F.center 1, F.splitB j, F.splitA i, F.center 0, F.splitA j]
      unfold Matrix.vecCons
      refine Fin.cons_injective_of_injective ?_ ?_
      · simpa only [Fin.range_cons, Matrix.range_empty, Set.mem_insert_iff,
          Set.mem_empty_iff_false, or_false, not_or] using
          (show F.splitB i ≠ F.center 1 ∧ F.splitB i ≠ F.splitB j ∧ F.splitB i ≠ F.splitA i ∧ F.splitB i ≠ F.center 0 ∧ F.splitB i ≠ F.splitA j from
            ⟨(fun he => (Ne.symm (hcb 1 i)) (congrArg Subtype.val he)), (fun he => (hB) (congrArg Subtype.val he)), (fun he => (Ne.symm (hcross i i)) (congrArg Subtype.val he)), (fun he => (Ne.symm (hcb 0 i)) (congrArg Subtype.val he)), (fun he => (Ne.symm (hcross j i)) (congrArg Subtype.val he))⟩)
      refine Fin.cons_injective_of_injective ?_ ?_
      · simpa only [Fin.range_cons, Matrix.range_empty, Set.mem_insert_iff,
          Set.mem_empty_iff_false, or_false, not_or] using
          (show F.center 1 ≠ F.splitB j ∧ F.center 1 ≠ F.splitA i ∧ F.center 1 ≠ F.center 0 ∧ F.center 1 ≠ F.splitA j from
            ⟨(fun he => (hcb 1 j) (congrArg Subtype.val he)), (fun he => (hca 1 i) (congrArg Subtype.val he)), (fun he => (Ne.symm hab) (congrArg Subtype.val he)), (fun he => (hca 1 j) (congrArg Subtype.val he))⟩)
      refine Fin.cons_injective_of_injective ?_ ?_
      · simpa only [Fin.range_cons, Matrix.range_empty, Set.mem_insert_iff,
          Set.mem_empty_iff_false, or_false, not_or] using
          (show F.splitB j ≠ F.splitA i ∧ F.splitB j ≠ F.center 0 ∧ F.splitB j ≠ F.splitA j from
            ⟨(fun he => (Ne.symm (hcross i j)) (congrArg Subtype.val he)), (fun he => (Ne.symm (hcb 0 j)) (congrArg Subtype.val he)), (fun he => (Ne.symm (hcross j j)) (congrArg Subtype.val he))⟩)
      refine Fin.cons_injective_of_injective ?_ ?_
      · simpa only [Fin.range_cons, Matrix.range_empty, Set.mem_insert_iff,
          Set.mem_empty_iff_false, or_false, not_or] using
          (show F.splitA i ≠ F.center 0 ∧ F.splitA i ≠ F.splitA j from
            ⟨(fun he => (Ne.symm (hca 0 i)) (congrArg Subtype.val he)), (fun he => (hA) (congrArg Subtype.val he))⟩)
      exact injective_pair_iff_ne.mpr ((fun he => (hca 0 j) (congrArg Subtype.val he)))
    have hcol : neighborColor v c (t 0) = neighborColor v c (t 3) :=
      (F.splitB_color i).trans (F.splitA_color i).symm
    exact neighbor_five_path_same_color_false hr v c t ht hi.2.2.1.symm hj.2.2.1
      he.symm hi.1.symm hj.1 0 3 (by decide) hcol

theorem DegreeTwelveFrame.pureSplit_no_triangle_A
    (hfree : G.CliqueFree 5) {v : V}
    {c : (G.induce {x | x ≠ v}).Coloring (Fin 7)}
    (F : DegreeTwelveFrame G v c) (hF : F.IsPureSplit)
    (i j k : Fin 5) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hijE : G.Adj (F.splitA i).val (F.splitA j).val)
    (hikE : G.Adj (F.splitA i).val (F.splitA k).val)
    (hjkE : G.Adj (F.splitA j).val (F.splitA k).val) : False := by
  classical
  have hi := (F.splitAB_adjacencies i (hF i)).1
  have hj := (F.splitAB_adjacencies j (hF j)).1
  have hk := (F.splitAB_adjacencies k (hF k)).1
  have hAi := F.center_splitA_ne 0 i
  have hAj := F.center_splitA_ne 0 j
  have hAk := F.center_splitA_ne 0 k
  have hAij := F.splitA_injective.ne hij
  have hAik := F.splitA_injective.ne hik
  have hAjk := F.splitA_injective.ne hjk
  let f : Fin 5 → V := ![v, (F.center 0).val, (F.splitA i).val,
    (F.splitA j).val, (F.splitA k).val]
  have hf : Function.Injective f := by
    change Function.Injective ![v, (F.center 0).val, (F.splitA i).val, (F.splitA j).val, (F.splitA k).val]
    unfold Matrix.vecCons
    refine Fin.cons_injective_of_injective ?_ ?_
    · simpa only [Fin.range_cons, Matrix.range_empty, Set.mem_insert_iff,
        Set.mem_empty_iff_false, or_false, not_or] using
        (show v ≠ (F.center 0).val ∧ v ≠ (F.splitA i).val ∧ v ≠ (F.splitA j).val ∧ v ≠ (F.splitA k).val from
          ⟨(F.center 0).property.ne, (F.splitA i).property.ne, (F.splitA j).property.ne, (F.splitA k).property.ne⟩)
    refine Fin.cons_injective_of_injective ?_ ?_
    · simpa only [Fin.range_cons, Matrix.range_empty, Set.mem_insert_iff,
        Set.mem_empty_iff_false, or_false, not_or] using
        (show (F.center 0).val ≠ (F.splitA i).val ∧ (F.center 0).val ≠ (F.splitA j).val ∧ (F.center 0).val ≠ (F.splitA k).val from
          ⟨hAi, hAj, hAk⟩)
    refine Fin.cons_injective_of_injective ?_ ?_
    · simpa only [Fin.range_cons, Matrix.range_empty, Set.mem_insert_iff,
        Set.mem_empty_iff_false, or_false, not_or] using
        (show (F.splitA i).val ≠ (F.splitA j).val ∧ (F.splitA i).val ≠ (F.splitA k).val from
          ⟨hAij, hAik⟩)
    exact injective_pair_iff_ne.mpr (hAjk)
  have hadj : ∀ l m : Fin 5, l ≠ m → G.Adj (f l) (f m) := by
    intro l m hlm
    fin_cases l <;> fin_cases m
    · exact False.elim (hlm rfl)
    · change G.Adj v (F.center 0).val
      exact (F.center 0).property
    · change G.Adj v (F.splitA i).val
      exact (F.splitA i).property
    · change G.Adj v (F.splitA j).val
      exact (F.splitA j).property
    · change G.Adj v (F.splitA k).val
      exact (F.splitA k).property
    · change G.Adj (F.center 0).val v
      exact ((F.center 0).property).symm
    · exact False.elim (hlm rfl)
    · change G.Adj (F.center 0).val (F.splitA i).val
      exact hi
    · change G.Adj (F.center 0).val (F.splitA j).val
      exact hj
    · change G.Adj (F.center 0).val (F.splitA k).val
      exact hk
    · change G.Adj (F.splitA i).val v
      exact ((F.splitA i).property).symm
    · change G.Adj (F.splitA i).val (F.center 0).val
      exact (hi).symm
    · exact False.elim (hlm rfl)
    · change G.Adj (F.splitA i).val (F.splitA j).val
      exact hijE
    · change G.Adj (F.splitA i).val (F.splitA k).val
      exact hikE
    · change G.Adj (F.splitA j).val v
      exact ((F.splitA j).property).symm
    · change G.Adj (F.splitA j).val (F.center 0).val
      exact (hj).symm
    · change G.Adj (F.splitA j).val (F.splitA i).val
      exact (hijE).symm
    · exact False.elim (hlm rfl)
    · change G.Adj (F.splitA j).val (F.splitA k).val
      exact hjkE
    · change G.Adj (F.splitA k).val v
      exact ((F.splitA k).property).symm
    · change G.Adj (F.splitA k).val (F.center 0).val
      exact (hk).symm
    · change G.Adj (F.splitA k).val (F.splitA i).val
      exact (hikE).symm
    · change G.Adj (F.splitA k).val (F.splitA j).val
      exact (hjkE).symm
    · exact False.elim (hlm rfl)
  let Q := Finset.univ.image f
  apply hfree Q
  refine ⟨?_, ?_⟩
  · intro x hx y hy hxy
    obtain ⟨l, _, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨m, _, rfl⟩ := Finset.mem_image.mp hy
    exact hadj l m (fun he => hxy (congrArg f he))
  · simpa [Q] using Finset.card_image_of_injective (s := Finset.univ) hf

theorem DegreeTwelveFrame.connected_splitB_seven_path
    (hcrit : IsCriticalPlus 7 G) (hc : modCycleCount 7 G = 2880)
    (hnot : ¬ IsCompleteOfOrder G 8) {v : V}
    {c : (G.induce {x | x ≠ v}).Coloring (Fin 7)}
    (F : DegreeTwelveFrame G v c) (hF : F.IsPureSplit) (i : Fin 5)
    (hreach : F.splitBD i ∈ twoColorComponent c (c (F.centerD 0))
      (F.pairIndex i).val (F.centerD 0)) :
    ∃ p : (G.induce {x | x ≠ v}).Walk (F.centerD 0) (F.splitBD i),
      p.IsPath ∧ Follows p c (Equiv.swap (c (F.centerD 0)) (F.pairIndex i).val) ∧
      (∀ q : (G.induce {x | x ≠ v}).Walk (F.centerD 0) (F.splitBD i),
        Follows q c (Equiv.swap (c (F.centerD 0)) (F.pairIndex i).val) →
        p.length ≤ q.length) ∧ p.length = 7 := by
  have hdec :
      (inferInstance : DecidableRel G.Adj) =
        (fun a b => Classical.propDecidable (G.Adj a b)) := by
    funext a b
    exact Subsingleton.elim _ _
  cases hdec
  classical
  obtain ⟨j, hji⟩ : ∃ j : Fin 5, j ≠ i := exists_ne i
  have hi := F.splitAB_adjacencies i (hF i)
  have hj := F.splitAB_adjacencies j (hF j)
  have hac : c (F.centerD 0) = (F.singletonIndex 0).val := F.center_color 0
  have hsc : c (F.centerD 1) = (F.singletonIndex 1).val := F.center_color 1
  have hbc : c (F.splitBD i) = (F.pairIndex i).val := F.splitB_color i
  have htc : c (F.splitBD j) = (F.pairIndex j).val := F.splitB_color j
  have huc : c (F.splitAD j) = (F.pairIndex j).val := F.splitA_color j
  have hsingle : F.singletonIndex 1 ≠ F.singletonIndex 0 :=
    F.singletonIndex.injective.ne (by decide : (1 : Fin 2) ≠ 0)
  have htu : F.splitBD j ≠ F.splitAD j := by
    intro he
    exact F.splitAB_ne j (congrArg Subtype.val he).symm
  have hbs : G.Adj (F.splitBD i).val (F.centerD 1).val := by
    change G.Adj (F.splitB i).val (F.center 1).val
    exact hi.2.2.1.symm
  have hsv : G.Adj (F.centerD 1).val v := by
    change G.Adj (F.center 1).val v
    exact (F.center 1).property.symm
  have hst : G.Adj (F.centerD 1).val (F.splitBD j).val := by
    change G.Adj (F.center 1).val (F.splitB j).val
    exact hj.2.2.1
  have htv : G.Adj (F.splitBD j).val v := by
    change G.Adj (F.splitB j).val v
    exact (F.splitB j).property.symm
  have hvu : G.Adj v (F.splitAD j).val := by
    change G.Adj v (F.splitA j).val
    exact (F.splitA j).property
  have hua : G.Adj (F.splitAD j).val (F.centerD 0).val := by
    change G.Adj (F.splitA j).val (F.center 0).val
    exact hj.1.symm
  exact equality_singleton_exists_length_seven hcrit hc hnot v c
    (F.singletonIndex 1) (F.singletonIndex 0) hsingle
    (a := F.centerD 0) (b := F.splitBD i) (s := F.centerD 1)
    (t := F.splitBD j) (u := F.splitAD j) hac (F.pairIndex i).val
    (by rw [hac]; exact F.pairColor_ne_singleton i 0) hbc
    (F.center 0).property (F.splitB i).property hi.2.2.2
    (by rw [hsc, hac]; exact F.singletonColor_injective.ne (by decide))
    (by rw [hsc]; exact Ne.symm (F.pairColor_ne_singleton i 1))
    (by rw [htc, hac]; exact F.pairColor_ne_singleton j 0)
    (by rw [htc]; exact F.pairColor_injective.ne hji)
    (huc.trans htc.symm) htu
    (by rw [hsc, htc]; exact Ne.symm (F.pairColor_ne_singleton j 1))
    hbs hsv hst htv hvu hua hreach

end TaskH.Seven
#print axioms TaskH.Seven.twoColorNeighborDeleted
#print axioms TaskH.Seven.DegreeTwelveFrame.centerD
#print axioms TaskH.Seven.DegreeTwelveFrame.splitAD
#print axioms TaskH.Seven.DegreeTwelveFrame.splitBD
#print axioms TaskH.Seven.DegreeTwelveFrame.pairColor_ne_singleton
#print axioms TaskH.Seven.DegreeTwelveFrame.pairColor_injective
#print axioms TaskH.Seven.DegreeTwelveFrame.singletonColor_injective
#print axioms TaskH.Seven.DegreeTwelveFrame.splitA_injective
#print axioms TaskH.Seven.DegreeTwelveFrame.splitB_injective
#print axioms TaskH.Seven.DegreeTwelveFrame.center_splitA_ne
#print axioms TaskH.Seven.DegreeTwelveFrame.center_splitB_ne
#print axioms TaskH.Seven.DegreeTwelveFrame.splitA_splitB_ne
#print axioms TaskH.Seven.DegreeTwelveFrame.pureSplit_cross_not_adj
#print axioms TaskH.Seven.DegreeTwelveFrame.pureSplit_no_triangle_A
#print axioms TaskH.Seven.DegreeTwelveFrame.connected_splitB_seven_path
