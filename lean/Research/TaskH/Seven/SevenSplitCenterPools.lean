import Research.TaskH.Seven.SevenTwoColorFrame

/-! Actual outside center/leaf pool separations in a fixed pure-split frame.
Pure split is an explicit internal branch, still to be derived universally.
The path arguments include the outside vertices; no cover of the complement
or extra neighbor incidence is assumed. -/

set_option autoImplicit false
universe u
namespace TaskH.Seven
open SimpleGraph
open scoped Classical
variable {V : Type u} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable def rootOutside (G : SimpleGraph V) (v : V) : Finset V :=
  (insert v (G.neighborFinset v))ᶜ

theorem rootOutside_ne_root {v z : V} (hz : z ∈ rootOutside G v) : z ≠ v := by
  cases (inferInstance : DecidableRel G.Adj) v v with
  | isTrue hvv => exact (G.loopless.irrefl v hvv).elim
  | isFalse _ =>
      intro he
      subst z
      exact (Finset.mem_compl.mp hz) (Finset.mem_insert_self _ _)

theorem rootOutside_ne_neighbor {v z : V} (hz : z ∈ rootOutside G v)
    (w : G.neighborSet v) : z ≠ w.val := by
  have hdec :
      (inferInstance : DecidableRel G.Adj) =
        (fun a b => Classical.propDecidable (G.Adj a b)) := by
    funext a b
    exact Subsingleton.elim _ _
  cases hdec
  classical
  intro he
  apply Finset.mem_compl.mp hz
  exact Finset.mem_insert.mpr (Or.inr ((G.mem_neighborFinset v z).mpr
    (by rw [he]; exact w.property)))

noncomputable def DegreeTwelveFrame.centerPool {v : V}
    {c : (G.induce {x | x ≠ v}).Coloring (Fin 7)}
    (F : DegreeTwelveFrame G v c) (j : Fin 2) : Finset V :=
  (rootOutside G v).filter (fun z => G.Adj (F.center j).val z)

noncomputable def DegreeTwelveFrame.splitPoolA {v : V}
    {c : (G.induce {x | x ≠ v}).Coloring (Fin 7)}
    (F : DegreeTwelveFrame G v c) : Finset V :=
  (rootOutside G v).filter (fun z => ∃ i : Fin 5, G.Adj z (F.splitA i).val)

noncomputable def DegreeTwelveFrame.splitPoolB {v : V}
    {c : (G.induce {x | x ≠ v}).Coloring (Fin 7)}
    (F : DegreeTwelveFrame G v c) : Finset V :=
  (rootOutside G v).filter (fun z => ∃ i : Fin 5, G.Adj z (F.splitB i).val)

theorem DegreeTwelveFrame.pureSplit_center_zero_no_B_hook
    (hr : RainbowSevenCycles G) {v : V}
    {c : (G.induce {x | x ≠ v}).Coloring (Fin 7)}
    (F : DegreeTwelveFrame G v c) (hF : F.IsPureSplit)
    (z : V) (hz : z ∈ rootOutside G v)
    (haz : G.Adj (F.center 0).val z) (i : Fin 5) :
    ¬ G.Adj z (F.splitB i).val := by
  intro hzq
  obtain ⟨j, hji⟩ : ∃ j : Fin 5, j ≠ i := exists_ne i
  have hi := F.splitAB_adjacencies i (hF i)
  have hj := F.splitAB_adjacencies j (hF j)
  have hab := F.center_center_ne (by decide : (0 : Fin 2) ≠ 1)
  have hB := F.splitB_injective.ne hji
  have hca := F.center_splitA_ne
  have hcb := F.center_splitB_ne
  have hcross := F.splitA_splitB_ne
  have hzn := rootOutside_ne_neighbor hz
  let t : Fin 6 → V := ![(F.splitA i).val, (F.center 0).val, z,
    (F.splitB i).val, (F.center 1).val, (F.splitB j).val]
  have ht : Function.Injective t := by
    change Function.Injective ![(F.splitA i).val, (F.center 0).val, z, (F.splitB i).val, (F.center 1).val, (F.splitB j).val]
    unfold Matrix.vecCons
    refine Fin.cons_injective_of_injective ?_ ?_
    · simpa only [Fin.range_cons, Matrix.range_empty, Set.mem_insert_iff,
        Set.mem_empty_iff_false, or_false, not_or] using
        (show (F.splitA i).val ≠ (F.center 0).val ∧ (F.splitA i).val ≠ z ∧ (F.splitA i).val ≠ (F.splitB i).val ∧ (F.splitA i).val ≠ (F.center 1).val ∧ (F.splitA i).val ≠ (F.splitB j).val from
          ⟨(Ne.symm (hca 0 i)), (Ne.symm (hzn (F.splitA i))), (hcross i i), (Ne.symm (hca 1 i)), (hcross i j)⟩)
    refine Fin.cons_injective_of_injective ?_ ?_
    · simpa only [Fin.range_cons, Matrix.range_empty, Set.mem_insert_iff,
        Set.mem_empty_iff_false, or_false, not_or] using
        (show (F.center 0).val ≠ z ∧ (F.center 0).val ≠ (F.splitB i).val ∧ (F.center 0).val ≠ (F.center 1).val ∧ (F.center 0).val ≠ (F.splitB j).val from
          ⟨(Ne.symm (hzn (F.center 0))), (hcb 0 i), (hab), (hcb 0 j)⟩)
    refine Fin.cons_injective_of_injective ?_ ?_
    · simpa only [Fin.range_cons, Matrix.range_empty, Set.mem_insert_iff,
        Set.mem_empty_iff_false, or_false, not_or] using
        (show z ≠ (F.splitB i).val ∧ z ≠ (F.center 1).val ∧ z ≠ (F.splitB j).val from
          ⟨(hzn (F.splitB i)), (hzn (F.center 1)), (hzn (F.splitB j))⟩)
    refine Fin.cons_injective_of_injective ?_ ?_
    · simpa only [Fin.range_cons, Matrix.range_empty, Set.mem_insert_iff,
        Set.mem_empty_iff_false, or_false, not_or] using
        (show (F.splitB i).val ≠ (F.center 1).val ∧ (F.splitB i).val ≠ (F.splitB j).val from
          ⟨(Ne.symm (hcb 1 i)), (Ne.symm (hB))⟩)
    exact injective_pair_iff_ne.mpr (hcb 1 j)
  have htv : ∀ l : Fin 6, t l ≠ v := by
    intro l
    fin_cases l
    · exact (F.splitA i).property.ne.symm
    · exact (F.center 0).property.ne.symm
    · exact rootOutside_ne_root hz
    · exact (F.splitB i).property.ne.symm
    · exact (F.center 1).property.ne.symm
    · exact (F.splitB j).property.ne.symm
  exact rooted_five_path_same_color_false hr v c t ht htv
    (F.splitA i).property (F.splitB j).property
    hi.1.symm haz hzq hi.2.2.1.symm hj.2.2.1
    0 3 (by decide) ((F.splitA_color i).trans (F.splitB_color i).symm)

theorem DegreeTwelveFrame.pureSplit_centerPool_zero_disjoint_B
    (hr : RainbowSevenCycles G) {v : V}
    {c : (G.induce {x | x ≠ v}).Coloring (Fin 7)}
    (F : DegreeTwelveFrame G v c) (hF : F.IsPureSplit) :
    Disjoint (F.centerPool 0) F.splitPoolB := by
  apply Finset.disjoint_left.mpr
  intro z hz hzb
  obtain ⟨hzO, haz⟩ := Finset.mem_filter.mp hz
  obtain ⟨i, hzi⟩ := (Finset.mem_filter.mp hzb).2
  exact F.pureSplit_center_zero_no_B_hook hr hF z hzO haz i hzi

theorem DegreeTwelveFrame.pureSplit_no_centerPool_edge
    (hr : RainbowSevenCycles G) {v : V}
    {c : (G.induce {x | x ≠ v}).Coloring (Fin 7)}
    (F : DegreeTwelveFrame G v c) (hF : F.IsPureSplit)
    (z w : V) (hz : z ∈ F.centerPool 0) (hw : w ∈ F.centerPool 1) :
    ¬ G.Adj z w := by
  intro hzw
  obtain ⟨hzO, haz⟩ := Finset.mem_filter.mp hz
  obtain ⟨hwO, hbw⟩ := Finset.mem_filter.mp hw
  let i : Fin 5 := 0
  have hi := F.splitAB_adjacencies i (hF i)
  have hab := F.center_center_ne (by decide : (0 : Fin 2) ≠ 1)
  have hca := F.center_splitA_ne
  have hcb := F.center_splitB_ne
  have hcross := F.splitA_splitB_ne
  have hzn := rootOutside_ne_neighbor hzO
  have hwn := rootOutside_ne_neighbor hwO
  have hne := hzw.ne
  let t : Fin 6 → V := ![(F.splitA i).val, (F.center 0).val, z, w,
    (F.center 1).val, (F.splitB i).val]
  have ht : Function.Injective t := by
    change Function.Injective ![(F.splitA i).val, (F.center 0).val, z, w, (F.center 1).val, (F.splitB i).val]
    unfold Matrix.vecCons
    refine Fin.cons_injective_of_injective ?_ ?_
    · simpa only [Fin.range_cons, Matrix.range_empty, Set.mem_insert_iff,
        Set.mem_empty_iff_false, or_false, not_or] using
        (show (F.splitA i).val ≠ (F.center 0).val ∧ (F.splitA i).val ≠ z ∧ (F.splitA i).val ≠ w ∧ (F.splitA i).val ≠ (F.center 1).val ∧ (F.splitA i).val ≠ (F.splitB i).val from
          ⟨(Ne.symm (hca 0 i)), (Ne.symm (hzn (F.splitA i))), (Ne.symm (hwn (F.splitA i))), (Ne.symm (hca 1 i)), (hcross i i)⟩)
    refine Fin.cons_injective_of_injective ?_ ?_
    · simpa only [Fin.range_cons, Matrix.range_empty, Set.mem_insert_iff,
        Set.mem_empty_iff_false, or_false, not_or] using
        (show (F.center 0).val ≠ z ∧ (F.center 0).val ≠ w ∧ (F.center 0).val ≠ (F.center 1).val ∧ (F.center 0).val ≠ (F.splitB i).val from
          ⟨(Ne.symm (hzn (F.center 0))), (Ne.symm (hwn (F.center 0))), (hab), (hcb 0 i)⟩)
    refine Fin.cons_injective_of_injective ?_ ?_
    · simpa only [Fin.range_cons, Matrix.range_empty, Set.mem_insert_iff,
        Set.mem_empty_iff_false, or_false, not_or] using
        (show z ≠ w ∧ z ≠ (F.center 1).val ∧ z ≠ (F.splitB i).val from
          ⟨(hne), (hzn (F.center 1)), (hzn (F.splitB i))⟩)
    refine Fin.cons_injective_of_injective ?_ ?_
    · simpa only [Fin.range_cons, Matrix.range_empty, Set.mem_insert_iff,
        Set.mem_empty_iff_false, or_false, not_or] using
        (show w ≠ (F.center 1).val ∧ w ≠ (F.splitB i).val from
          ⟨(hwn (F.center 1)), (hwn (F.splitB i))⟩)
    exact injective_pair_iff_ne.mpr (hcb 1 i)
  have htv : ∀ l : Fin 6, t l ≠ v := by
    intro l
    fin_cases l
    · exact (F.splitA i).property.ne.symm
    · exact (F.center 0).property.ne.symm
    · exact rootOutside_ne_root hzO
    · exact rootOutside_ne_root hwO
    · exact (F.center 1).property.ne.symm
    · exact (F.splitB i).property.ne.symm
  exact rooted_five_path_same_color_false hr v c t ht htv
    (F.splitA i).property (F.splitB i).property
    hi.1.symm haz hzw hbw.symm hi.2.2.1
    0 5 (by decide) ((F.splitA_color i).trans (F.splitB_color i).symm)

theorem DegreeTwelveFrame.pureSplit_centerPool_zero_no_B_pool_edge
    (hr : RainbowSevenCycles G) {v : V}
    {c : (G.induce {x | x ≠ v}).Coloring (Fin 7)}
    (F : DegreeTwelveFrame G v c) (hF : F.IsPureSplit)
    (z w : V) (hz : z ∈ F.centerPool 0) (hw : w ∈ F.splitPoolB) :
    ¬ G.Adj z w := by
  intro hzw
  obtain ⟨hzO, haz⟩ := Finset.mem_filter.mp hz
  obtain ⟨hwO, i, hwi⟩ := Finset.mem_filter.mp hw
  have hi := F.splitAB_adjacencies i (hF i)
  have hab := F.center_center_ne (by decide : (0 : Fin 2) ≠ 1)
  have hcb := F.center_splitB_ne
  have hzn := rootOutside_ne_neighbor hzO
  have hwn := rootOutside_ne_neighbor hwO
  have hne := hzw.ne
  have pathColors (j : Fin 5) (hji : j ≠ i) :
      c ⟨z, rootOutside_ne_root hzO⟩ ≠ (F.singletonIndex 0).val ∧
      c ⟨z, rootOutside_ne_root hzO⟩ ≠ (F.singletonIndex 1).val ∧
      c ⟨z, rootOutside_ne_root hzO⟩ ≠ (F.pairIndex i).val ∧
      c ⟨z, rootOutside_ne_root hzO⟩ ≠ (F.pairIndex j).val := by
    have hj := F.splitAB_adjacencies j (hF j)
    have hB := F.splitB_injective.ne hji
    let t : Fin 6 → V := ![(F.center 0).val, z, w,
      (F.splitB i).val, (F.center 1).val, (F.splitB j).val]
    have ht : Function.Injective t := by
      change Function.Injective ![(F.center 0).val, z, w, (F.splitB i).val, (F.center 1).val, (F.splitB j).val]
      unfold Matrix.vecCons
      refine Fin.cons_injective_of_injective ?_ ?_
      · simpa only [Fin.range_cons, Matrix.range_empty, Set.mem_insert_iff,
          Set.mem_empty_iff_false, or_false, not_or] using
          (show (F.center 0).val ≠ z ∧ (F.center 0).val ≠ w ∧ (F.center 0).val ≠ (F.splitB i).val ∧ (F.center 0).val ≠ (F.center 1).val ∧ (F.center 0).val ≠ (F.splitB j).val from
            ⟨(Ne.symm (hzn (F.center 0))), (Ne.symm (hwn (F.center 0))), (hcb 0 i), (hab), (hcb 0 j)⟩)
      refine Fin.cons_injective_of_injective ?_ ?_
      · simpa only [Fin.range_cons, Matrix.range_empty, Set.mem_insert_iff,
          Set.mem_empty_iff_false, or_false, not_or] using
          (show z ≠ w ∧ z ≠ (F.splitB i).val ∧ z ≠ (F.center 1).val ∧ z ≠ (F.splitB j).val from
            ⟨(hne), (hzn (F.splitB i)), (hzn (F.center 1)), (hzn (F.splitB j))⟩)
      refine Fin.cons_injective_of_injective ?_ ?_
      · simpa only [Fin.range_cons, Matrix.range_empty, Set.mem_insert_iff,
          Set.mem_empty_iff_false, or_false, not_or] using
          (show w ≠ (F.splitB i).val ∧ w ≠ (F.center 1).val ∧ w ≠ (F.splitB j).val from
            ⟨(hwn (F.splitB i)), (hwn (F.center 1)), (hwn (F.splitB j))⟩)
      refine Fin.cons_injective_of_injective ?_ ?_
      · simpa only [Fin.range_cons, Matrix.range_empty, Set.mem_insert_iff,
          Set.mem_empty_iff_false, or_false, not_or] using
          (show (F.splitB i).val ≠ (F.center 1).val ∧ (F.splitB i).val ≠ (F.splitB j).val from
            ⟨(Ne.symm (hcb 1 i)), (Ne.symm (hB))⟩)
      exact injective_pair_iff_ne.mpr (hcb 1 j)
    have htv : ∀ l : Fin 6, t l ≠ v := by
      intro l
      fin_cases l
      · exact (F.center 0).property.ne.symm
      · exact rootOutside_ne_root hzO
      · exact rootOutside_ne_root hwO
      · exact (F.splitB i).property.ne.symm
      · exact (F.center 1).property.ne.symm
      · exact (F.splitB j).property.ne.symm
    have hinj := rooted_five_path_colors_injective hr v c t ht htv
      (F.center 0).property (F.splitB j).property
      haz hzw hwi hi.2.2.1.symm hj.2.2.1
    have hn : ∀ l : Fin 6, l ≠ 1 → c ⟨z, rootOutside_ne_root hzO⟩ ≠ c ⟨t l, htv l⟩ := by
      intro l hl he
      have he' : c ⟨t 1, htv 1⟩ = c ⟨t l, htv l⟩ := he
      have hindex : (1 : Fin 6) = l := @hinj 1 l he'
      exact hl hindex.symm
    have h0 : c ⟨t 0, htv 0⟩ = (F.singletonIndex 0).val := F.center_color 0
    have h4 : c ⟨t 4, htv 4⟩ = (F.singletonIndex 1).val := F.center_color 1
    have h3 : c ⟨t 3, htv 3⟩ = (F.pairIndex i).val := F.splitB_color i
    have h5 : c ⟨t 5, htv 5⟩ = (F.pairIndex j).val := F.splitB_color j
    exact ⟨by simpa only [h0] using hn 0 (by decide),
      by simpa only [h4] using hn 4 (by decide),
      by simpa only [h3] using hn 3 (by decide),
      by simpa only [h5] using hn 5 (by decide)⟩
  obtain ⟨j, hji⟩ : ∃ j : Fin 5, j ≠ i := exists_ne i
  have hc := pathColors j hji
  rcases F.color_cases (c ⟨z, rootOutside_ne_root hzO⟩) with ⟨a, ha⟩ | ⟨l, hl⟩
  · fin_cases a
    · exact hc.1 ha.symm
    · exact hc.2.1 ha.symm
  · by_cases hli : l = i
    · subst l
      exact hc.2.2.1 hl.symm
    · exact (pathColors l hli).2.2.2 hl.symm

end TaskH.Seven

#print axioms TaskH.Seven.rootOutside
#print axioms TaskH.Seven.rootOutside_ne_root
#print axioms TaskH.Seven.rootOutside_ne_neighbor
#print axioms TaskH.Seven.DegreeTwelveFrame.centerPool
#print axioms TaskH.Seven.DegreeTwelveFrame.splitPoolA
#print axioms TaskH.Seven.DegreeTwelveFrame.splitPoolB
#print axioms TaskH.Seven.DegreeTwelveFrame.pureSplit_center_zero_no_B_hook
#print axioms TaskH.Seven.DegreeTwelveFrame.pureSplit_centerPool_zero_disjoint_B
#print axioms TaskH.Seven.DegreeTwelveFrame.pureSplit_no_centerPool_edge
#print axioms TaskH.Seven.DegreeTwelveFrame.pureSplit_centerPool_zero_no_B_pool_edge
