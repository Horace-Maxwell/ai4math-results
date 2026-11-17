import Research.TaskH.Seven.SevenTwoColorSixPathNeighbors

/-! Actual seven-path residual positions. Absence of the own P_i leaf is an
explicit INTERNAL path condition, still to be obtained from shortestness and
the six-path contradiction. This file does not claim that transport done. -/

set_option autoImplicit false
universe u
namespace TaskH.Seven
open SimpleGraph
open scoped Classical
variable {V : Type u} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem DegreeTwelveFrame.seven_path_internal_outside_of_own_leaf_absent {v : V}
    {c : (G.induce {x | x ≠ v}).Coloring (Fin 7)}
    (F : DegreeTwelveFrame G v c) (i : Fin 5)
    (p : (G.induce {x | x ≠ v}).Walk (F.centerD 0) (F.splitBD i))
    (hp : p.IsPath)
    (hf : Follows p c (Equiv.swap (c (F.centerD 0)) (F.pairIndex i).val))
    (hl : p.length = 7)
    (havoidP : ∀ n ≤ p.length, p.getVert n ≠ F.splitAD i)
    (n : ℕ) (hn0 : 0 < n) (hn7 : n < 7) :
    (p.getVert n).val ∈ rootOutside G v := by
  have hdec :
      (inferInstance : DecidableRel G.Adj) =
        (fun a b => Classical.propDecidable (G.Adj a b)) := by
    funext a b
    exact Subsingleton.elim _ _
  cases hdec
  classical
  apply Finset.mem_compl.mpr
  intro hm
  rcases Finset.mem_insert.mp hm with he | he
  · exact (p.getVert n).property he
  · have hadj := (G.mem_neighborFinset v (p.getVert n).val).mp he
    have hc := twoColor_color_at p c (F.pairIndex i).val hf n (by omega)
    have hstart : c (F.centerD 0) = (F.singletonIndex 0).val := F.center_color 0
    by_cases heven : n % 2 = 0
    · rw [ite_eq_left heven, hstart] at hc
      have hpoint := (F.singleton_fiber_as_deleted 0 (p.getVert n) hadj).mp hc
      have hh := (hp.getVert_eq_start_iff (by omega : n ≤ p.length)).mp hpoint
      omega
    · rw [ite_eq_right heven] at hc
      rcases (F.pair_fiber_as_deleted i (p.getVert n) hadj).mp hc with hpi | hqi
      · exact havoidP n (by omega) hpi
      · have hh := (hp.getVert_eq_end_iff (by omega : n ≤ p.length)).mp hqi
        omega

theorem DegreeTwelveFrame.seven_path_middle_residual_of_own_leaf_absent
    (hr : RainbowSevenCycles G) {v : V}
    {c : (G.induce {x | x ≠ v}).Coloring (Fin 7)}
    (F : DegreeTwelveFrame G v c) (hF : F.IsPureSplit) (i : Fin 5)
    (p : (G.induce {x | x ≠ v}).Walk (F.centerD 0) (F.splitBD i))
    (hp : p.IsPath)
    (hf : Follows p c (Equiv.swap (c (F.centerD 0)) (F.pairIndex i).val))
    (hl : p.length = 7)
    (havoidP : ∀ n ≤ p.length, p.getVert n ≠ F.splitAD i) :
    (p.getVert 3).val ∈ F.residualPool ∧ (p.getVert 4).val ∈ F.residualPool := by
  have hdec :
      (inferInstance : DecidableRel G.Adj) =
        (fun a b => Classical.propDecidable (G.Adj a b)) := by
    funext a b
    exact Subsingleton.elim _ _
  cases hdec
  classical
  have h1O := F.seven_path_internal_outside_of_own_leaf_absent i p hp hf hl havoidP 1 (by decide) (by decide)
  have h1N := rootOutside_ne_neighbor h1O
  have h2O := F.seven_path_internal_outside_of_own_leaf_absent i p hp hf hl havoidP 2 (by decide) (by decide)
  have h2N := rootOutside_ne_neighbor h2O
  have h3O := F.seven_path_internal_outside_of_own_leaf_absent i p hp hf hl havoidP 3 (by decide) (by decide)
  have h3N := rootOutside_ne_neighbor h3O
  have h4O := F.seven_path_internal_outside_of_own_leaf_absent i p hp hf hl havoidP 4 (by decide) (by decide)
  have h4N := rootOutside_ne_neighbor h4O
  have h5O := F.seven_path_internal_outside_of_own_leaf_absent i p hp hf hl havoidP 5 (by decide) (by decide)
  have h5N := rootOutside_ne_neighbor h5O
  have h6O := F.seven_path_internal_outside_of_own_leaf_absent i p hp hf hl havoidP 6 (by decide) (by decide)
  have h6N := rootOutside_ne_neighbor h6O
  have hposne (n m : ℕ) (hn : n ≤ p.length) (hm : m ≤ p.length) (hne : n ≠ m) :
      (p.getVert n).val ≠ (p.getVert m).val := by
    intro he
    exact hne (hp.getVert_injOn hn hm (Subtype.ext he))
  have h12n := hposne 1 2 (by omega) (by omega) (by decide)
  have h13n := hposne 1 3 (by omega) (by omega) (by decide)
  have h14n := hposne 1 4 (by omega) (by omega) (by decide)
  have h15n := hposne 1 5 (by omega) (by omega) (by decide)
  have h16n := hposne 1 6 (by omega) (by omega) (by decide)
  have h23n := hposne 2 3 (by omega) (by omega) (by decide)
  have h24n := hposne 2 4 (by omega) (by omega) (by decide)
  have h25n := hposne 2 5 (by omega) (by omega) (by decide)
  have h26n := hposne 2 6 (by omega) (by omega) (by decide)
  have h34n := hposne 3 4 (by omega) (by omega) (by decide)
  have h35n := hposne 3 5 (by omega) (by omega) (by decide)
  have h36n := hposne 3 6 (by omega) (by omega) (by decide)
  have h45n := hposne 4 5 (by omega) (by omega) (by decide)
  have h46n := hposne 4 6 (by omega) (by omega) (by decide)
  have h56n := hposne 5 6 (by omega) (by omega) (by decide)
  have hca := F.center_splitA_ne
  have hcb := F.center_splitB_ne
  have hcross := F.splitA_splitB_ne
  have hab := F.center_center_ne (by decide : (0 : Fin 2) ≠ 1)
  have hi := F.splitAB_adjacencies i (hF i)
  have hlast : p.getVert 7 = F.splitBD i := by simpa only [hl] using p.getVert_length
  have h01 : G.Adj (F.center 0).val (p.getVert 1).val := by
    have he := p.adj_getVert_succ (i := 0) (by omega)
    rw [Walk.getVert_zero] at he
    change G.Adj (F.center 0).val (p.getVert 1).val at he
    exact he
  have h12 : G.Adj (p.getVert 1).val (p.getVert 2).val := p.adj_getVert_succ (i := 1) (by omega)
  have h23 : G.Adj (p.getVert 2).val (p.getVert 3).val := p.adj_getVert_succ (i := 2) (by omega)
  have h34 : G.Adj (p.getVert 3).val (p.getVert 4).val := p.adj_getVert_succ (i := 3) (by omega)
  have h45 : G.Adj (p.getVert 4).val (p.getVert 5).val := p.adj_getVert_succ (i := 4) (by omega)
  have h56 : G.Adj (p.getVert 5).val (p.getVert 6).val := p.adj_getVert_succ (i := 5) (by omega)
  have h67 : G.Adj (p.getVert 6).val (F.splitB i).val := by
    have he := p.adj_getVert_succ (i := 6) (by omega)
    rw [hlast] at he
    change G.Adj (p.getVert 6).val (F.splitB i).val at he
    exact he
  have hc2 : c (p.getVert 2) = (F.singletonIndex 0).val := by
    simpa using (twoColor_color_at p c (F.pairIndex i).val hf 2 (by omega)).trans (F.center_color 0)
  have hc4 : c (p.getVert 4) = (F.singletonIndex 0).val := by
    simpa using (twoColor_color_at p c (F.pairIndex i).val hf 4 (by omega)).trans (F.center_color 0)
  have hc6 : c (p.getVert 6) = (F.singletonIndex 0).val := by
    simpa using (twoColor_color_at p c (F.pairIndex i).val hf 6 (by omega)).trans (F.center_color 0)
  have tA : (p.getVert 3).val ∉ F.centerPool 0 := by
    intro hm
    have hj := (Finset.mem_filter.mp hm).2
    let t : Fin 6 → V := ![(F.center 0).val, (p.getVert 3).val, (p.getVert 4).val, (p.getVert 5).val, (p.getVert 6).val, (F.splitB i).val]
    have ht : Function.Injective t := by
      change Function.Injective ![(F.center 0).val, (p.getVert 3).val, (p.getVert 4).val, (p.getVert 5).val, (p.getVert 6).val, (F.splitB i).val]
      unfold Matrix.vecCons
      refine Fin.cons_injective_of_injective ?_ ?_
      · simpa only [Fin.range_cons, Matrix.range_empty, Set.mem_insert_iff,
          Set.mem_empty_iff_false, or_false, not_or] using
          (show (F.center 0).val ≠ (p.getVert 3).val ∧ (F.center 0).val ≠ (p.getVert 4).val ∧ (F.center 0).val ≠ (p.getVert 5).val ∧ (F.center 0).val ≠ (p.getVert 6).val ∧ (F.center 0).val ≠ (F.splitB i).val from
            ⟨(Ne.symm (h3N (F.center 0))), (Ne.symm (h4N (F.center 0))), (Ne.symm (h5N (F.center 0))), (Ne.symm (h6N (F.center 0))), (hcb 0 i)⟩)
      refine Fin.cons_injective_of_injective ?_ ?_
      · simpa only [Fin.range_cons, Matrix.range_empty, Set.mem_insert_iff,
          Set.mem_empty_iff_false, or_false, not_or] using
          (show (p.getVert 3).val ≠ (p.getVert 4).val ∧ (p.getVert 3).val ≠ (p.getVert 5).val ∧ (p.getVert 3).val ≠ (p.getVert 6).val ∧ (p.getVert 3).val ≠ (F.splitB i).val from
            ⟨(h34n), (h35n), (h36n), (h3N (F.splitB i))⟩)
      refine Fin.cons_injective_of_injective ?_ ?_
      · simpa only [Fin.range_cons, Matrix.range_empty, Set.mem_insert_iff,
          Set.mem_empty_iff_false, or_false, not_or] using
          (show (p.getVert 4).val ≠ (p.getVert 5).val ∧ (p.getVert 4).val ≠ (p.getVert 6).val ∧ (p.getVert 4).val ≠ (F.splitB i).val from
            ⟨(h45n), (h46n), (h4N (F.splitB i))⟩)
      refine Fin.cons_injective_of_injective ?_ ?_
      · simpa only [Fin.range_cons, Matrix.range_empty, Set.mem_insert_iff,
          Set.mem_empty_iff_false, or_false, not_or] using
          (show (p.getVert 5).val ≠ (p.getVert 6).val ∧ (p.getVert 5).val ≠ (F.splitB i).val from
            ⟨(h56n), (h5N (F.splitB i))⟩)
      exact injective_pair_iff_ne.mpr (h6N (F.splitB i))
    have htv : ∀ a : Fin 6, t a ≠ v := by
      intro a
      fin_cases a
      all_goals first | exact (p.getVert _).property | exact (F.center 0).property.ne.symm | exact (F.splitB i).property.ne.symm
    exact rooted_five_path_same_color_false hr v c t ht htv (F.center 0).property
      (F.splitB i).property hj h34 h45 h56 h67 2 4 (by decide) (hc4.trans hc6.symm)
  have tB : (p.getVert 3).val ∉ F.centerPool 1 := by
    intro hm
    have hj := (Finset.mem_filter.mp hm).2
    let j : Fin 5 := 0
    have hjE := F.splitAB_adjacencies j (hF j)
    let t : Fin 6 → V := ![(F.center 0).val, (p.getVert 1).val, (p.getVert 2).val, (p.getVert 3).val, (F.center 1).val, (F.splitB j).val]
    have ht : Function.Injective t := by
      change Function.Injective ![(F.center 0).val, (p.getVert 1).val, (p.getVert 2).val, (p.getVert 3).val, (F.center 1).val, (F.splitB j).val]
      unfold Matrix.vecCons
      refine Fin.cons_injective_of_injective ?_ ?_
      · simpa only [Fin.range_cons, Matrix.range_empty, Set.mem_insert_iff,
          Set.mem_empty_iff_false, or_false, not_or] using
          (show (F.center 0).val ≠ (p.getVert 1).val ∧ (F.center 0).val ≠ (p.getVert 2).val ∧ (F.center 0).val ≠ (p.getVert 3).val ∧ (F.center 0).val ≠ (F.center 1).val ∧ (F.center 0).val ≠ (F.splitB j).val from
            ⟨(Ne.symm (h1N (F.center 0))), (Ne.symm (h2N (F.center 0))), (Ne.symm (h3N (F.center 0))), (hab), (hcb 0 j)⟩)
      refine Fin.cons_injective_of_injective ?_ ?_
      · simpa only [Fin.range_cons, Matrix.range_empty, Set.mem_insert_iff,
          Set.mem_empty_iff_false, or_false, not_or] using
          (show (p.getVert 1).val ≠ (p.getVert 2).val ∧ (p.getVert 1).val ≠ (p.getVert 3).val ∧ (p.getVert 1).val ≠ (F.center 1).val ∧ (p.getVert 1).val ≠ (F.splitB j).val from
            ⟨(h12n), (h13n), (h1N (F.center 1)), (h1N (F.splitB j))⟩)
      refine Fin.cons_injective_of_injective ?_ ?_
      · simpa only [Fin.range_cons, Matrix.range_empty, Set.mem_insert_iff,
          Set.mem_empty_iff_false, or_false, not_or] using
          (show (p.getVert 2).val ≠ (p.getVert 3).val ∧ (p.getVert 2).val ≠ (F.center 1).val ∧ (p.getVert 2).val ≠ (F.splitB j).val from
            ⟨(h23n), (h2N (F.center 1)), (h2N (F.splitB j))⟩)
      refine Fin.cons_injective_of_injective ?_ ?_
      · simpa only [Fin.range_cons, Matrix.range_empty, Set.mem_insert_iff,
          Set.mem_empty_iff_false, or_false, not_or] using
          (show (p.getVert 3).val ≠ (F.center 1).val ∧ (p.getVert 3).val ≠ (F.splitB j).val from
            ⟨(h3N (F.center 1)), (h3N (F.splitB j))⟩)
      exact injective_pair_iff_ne.mpr (hcb 1 j)
    have htv : ∀ a : Fin 6, t a ≠ v := by
      intro a
      fin_cases a
      all_goals first | exact (p.getVert _).property | exact (F.center 0).property.ne.symm | exact (F.center 1).property.ne.symm | exact (F.splitB j).property.ne.symm
    exact rooted_five_path_same_color_false hr v c t ht htv (F.center 0).property
      (F.splitB j).property h01 h12 h23 hj.symm hjE.2.2.1 0 2 (by decide) ((F.center_color 0).trans hc2.symm)
  have tX : (p.getVert 3).val ∉ F.splitPoolA := by
    intro hm
    obtain ⟨j, hj⟩ := (Finset.mem_filter.mp hm).2
    let t : Fin 6 → V := ![(F.splitA j).val, (p.getVert 3).val, (p.getVert 4).val, (p.getVert 5).val, (p.getVert 6).val, (F.splitB i).val]
    have ht : Function.Injective t := by
      change Function.Injective ![(F.splitA j).val, (p.getVert 3).val, (p.getVert 4).val, (p.getVert 5).val, (p.getVert 6).val, (F.splitB i).val]
      unfold Matrix.vecCons
      refine Fin.cons_injective_of_injective ?_ ?_
      · simpa only [Fin.range_cons, Matrix.range_empty, Set.mem_insert_iff,
          Set.mem_empty_iff_false, or_false, not_or] using
          (show (F.splitA j).val ≠ (p.getVert 3).val ∧ (F.splitA j).val ≠ (p.getVert 4).val ∧ (F.splitA j).val ≠ (p.getVert 5).val ∧ (F.splitA j).val ≠ (p.getVert 6).val ∧ (F.splitA j).val ≠ (F.splitB i).val from
            ⟨(Ne.symm (h3N (F.splitA j))), (Ne.symm (h4N (F.splitA j))), (Ne.symm (h5N (F.splitA j))), (Ne.symm (h6N (F.splitA j))), (hcross j i)⟩)
      refine Fin.cons_injective_of_injective ?_ ?_
      · simpa only [Fin.range_cons, Matrix.range_empty, Set.mem_insert_iff,
          Set.mem_empty_iff_false, or_false, not_or] using
          (show (p.getVert 3).val ≠ (p.getVert 4).val ∧ (p.getVert 3).val ≠ (p.getVert 5).val ∧ (p.getVert 3).val ≠ (p.getVert 6).val ∧ (p.getVert 3).val ≠ (F.splitB i).val from
            ⟨(h34n), (h35n), (h36n), (h3N (F.splitB i))⟩)
      refine Fin.cons_injective_of_injective ?_ ?_
      · simpa only [Fin.range_cons, Matrix.range_empty, Set.mem_insert_iff,
          Set.mem_empty_iff_false, or_false, not_or] using
          (show (p.getVert 4).val ≠ (p.getVert 5).val ∧ (p.getVert 4).val ≠ (p.getVert 6).val ∧ (p.getVert 4).val ≠ (F.splitB i).val from
            ⟨(h45n), (h46n), (h4N (F.splitB i))⟩)
      refine Fin.cons_injective_of_injective ?_ ?_
      · simpa only [Fin.range_cons, Matrix.range_empty, Set.mem_insert_iff,
          Set.mem_empty_iff_false, or_false, not_or] using
          (show (p.getVert 5).val ≠ (p.getVert 6).val ∧ (p.getVert 5).val ≠ (F.splitB i).val from
            ⟨(h56n), (h5N (F.splitB i))⟩)
      exact injective_pair_iff_ne.mpr (h6N (F.splitB i))
    have htv : ∀ a : Fin 6, t a ≠ v := by
      intro a
      fin_cases a
      all_goals first | exact (p.getVert _).property | exact (F.splitA j).property.ne.symm | exact (F.splitB i).property.ne.symm
    exact rooted_five_path_same_color_false hr v c t ht htv (F.splitA j).property
      (F.splitB i).property hj.symm h34 h45 h56 h67 2 4 (by decide) (hc4.trans hc6.symm)
  have tY : (p.getVert 3).val ∉ F.splitPoolB := by
    intro hm
    obtain ⟨j, hj⟩ := (Finset.mem_filter.mp hm).2
    have hjE := F.splitAB_adjacencies j (hF j)
    let t : Fin 6 → V := ![(F.center 0).val, (p.getVert 1).val, (p.getVert 2).val, (p.getVert 3).val, (F.splitB j).val, (F.center 1).val]
    have ht : Function.Injective t := by
      change Function.Injective ![(F.center 0).val, (p.getVert 1).val, (p.getVert 2).val, (p.getVert 3).val, (F.splitB j).val, (F.center 1).val]
      unfold Matrix.vecCons
      refine Fin.cons_injective_of_injective ?_ ?_
      · simpa only [Fin.range_cons, Matrix.range_empty, Set.mem_insert_iff,
          Set.mem_empty_iff_false, or_false, not_or] using
          (show (F.center 0).val ≠ (p.getVert 1).val ∧ (F.center 0).val ≠ (p.getVert 2).val ∧ (F.center 0).val ≠ (p.getVert 3).val ∧ (F.center 0).val ≠ (F.splitB j).val ∧ (F.center 0).val ≠ (F.center 1).val from
            ⟨(Ne.symm (h1N (F.center 0))), (Ne.symm (h2N (F.center 0))), (Ne.symm (h3N (F.center 0))), (hcb 0 j), (hab)⟩)
      refine Fin.cons_injective_of_injective ?_ ?_
      · simpa only [Fin.range_cons, Matrix.range_empty, Set.mem_insert_iff,
          Set.mem_empty_iff_false, or_false, not_or] using
          (show (p.getVert 1).val ≠ (p.getVert 2).val ∧ (p.getVert 1).val ≠ (p.getVert 3).val ∧ (p.getVert 1).val ≠ (F.splitB j).val ∧ (p.getVert 1).val ≠ (F.center 1).val from
            ⟨(h12n), (h13n), (h1N (F.splitB j)), (h1N (F.center 1))⟩)
      refine Fin.cons_injective_of_injective ?_ ?_
      · simpa only [Fin.range_cons, Matrix.range_empty, Set.mem_insert_iff,
          Set.mem_empty_iff_false, or_false, not_or] using
          (show (p.getVert 2).val ≠ (p.getVert 3).val ∧ (p.getVert 2).val ≠ (F.splitB j).val ∧ (p.getVert 2).val ≠ (F.center 1).val from
            ⟨(h23n), (h2N (F.splitB j)), (h2N (F.center 1))⟩)
      refine Fin.cons_injective_of_injective ?_ ?_
      · simpa only [Fin.range_cons, Matrix.range_empty, Set.mem_insert_iff,
          Set.mem_empty_iff_false, or_false, not_or] using
          (show (p.getVert 3).val ≠ (F.splitB j).val ∧ (p.getVert 3).val ≠ (F.center 1).val from
            ⟨(h3N (F.splitB j)), (h3N (F.center 1))⟩)
      exact injective_pair_iff_ne.mpr (Ne.symm (hcb 1 j))
    have htv : ∀ a : Fin 6, t a ≠ v := by
      intro a
      fin_cases a
      all_goals first | exact (p.getVert _).property | exact (F.center 0).property.ne.symm | exact (F.center 1).property.ne.symm | exact (F.splitB j).property.ne.symm
    exact rooted_five_path_same_color_false hr v c t ht htv (F.center 0).property
      (F.center 1).property h01 h12 h23 hj hjE.2.2.1.symm 0 2 (by decide) ((F.center_color 0).trans hc2.symm)
  have mB : (p.getVert 4).val ∉ F.centerPool 1 := by
    intro hm
    have hj := (Finset.mem_filter.mp hm).2
    let t : Fin 6 → V := ![(F.center 0).val, (p.getVert 1).val, (p.getVert 2).val, (p.getVert 3).val, (p.getVert 4).val, (F.center 1).val]
    have ht : Function.Injective t := by
      change Function.Injective ![(F.center 0).val, (p.getVert 1).val, (p.getVert 2).val, (p.getVert 3).val, (p.getVert 4).val, (F.center 1).val]
      unfold Matrix.vecCons
      refine Fin.cons_injective_of_injective ?_ ?_
      · simpa only [Fin.range_cons, Matrix.range_empty, Set.mem_insert_iff,
          Set.mem_empty_iff_false, or_false, not_or] using
          (show (F.center 0).val ≠ (p.getVert 1).val ∧ (F.center 0).val ≠ (p.getVert 2).val ∧ (F.center 0).val ≠ (p.getVert 3).val ∧ (F.center 0).val ≠ (p.getVert 4).val ∧ (F.center 0).val ≠ (F.center 1).val from
            ⟨(Ne.symm (h1N (F.center 0))), (Ne.symm (h2N (F.center 0))), (Ne.symm (h3N (F.center 0))), (Ne.symm (h4N (F.center 0))), (hab)⟩)
      refine Fin.cons_injective_of_injective ?_ ?_
      · simpa only [Fin.range_cons, Matrix.range_empty, Set.mem_insert_iff,
          Set.mem_empty_iff_false, or_false, not_or] using
          (show (p.getVert 1).val ≠ (p.getVert 2).val ∧ (p.getVert 1).val ≠ (p.getVert 3).val ∧ (p.getVert 1).val ≠ (p.getVert 4).val ∧ (p.getVert 1).val ≠ (F.center 1).val from
            ⟨(h12n), (h13n), (h14n), (h1N (F.center 1))⟩)
      refine Fin.cons_injective_of_injective ?_ ?_
      · simpa only [Fin.range_cons, Matrix.range_empty, Set.mem_insert_iff,
          Set.mem_empty_iff_false, or_false, not_or] using
          (show (p.getVert 2).val ≠ (p.getVert 3).val ∧ (p.getVert 2).val ≠ (p.getVert 4).val ∧ (p.getVert 2).val ≠ (F.center 1).val from
            ⟨(h23n), (h24n), (h2N (F.center 1))⟩)
      refine Fin.cons_injective_of_injective ?_ ?_
      · simpa only [Fin.range_cons, Matrix.range_empty, Set.mem_insert_iff,
          Set.mem_empty_iff_false, or_false, not_or] using
          (show (p.getVert 3).val ≠ (p.getVert 4).val ∧ (p.getVert 3).val ≠ (F.center 1).val from
            ⟨(h34n), (h3N (F.center 1))⟩)
      exact injective_pair_iff_ne.mpr (h4N (F.center 1))
    have htv : ∀ a : Fin 6, t a ≠ v := by
      intro a
      fin_cases a
      all_goals first | exact (p.getVert _).property | exact (F.center 0).property.ne.symm | exact (F.center 1).property.ne.symm
    exact rooted_five_path_same_color_false hr v c t ht htv (F.center 0).property
      (F.center 1).property h01 h12 h23 h34 hj.symm 0 2 (by decide) ((F.center_color 0).trans hc2.symm)
  have mX : (p.getVert 4).val ∉ F.splitPoolA := by
    intro hm
    obtain ⟨j, hj⟩ := (Finset.mem_filter.mp hm).2
    let t : Fin 6 → V := ![(F.splitA j).val, (p.getVert 4).val, (p.getVert 5).val, (p.getVert 6).val, (F.splitB i).val, (F.center 1).val]
    have ht : Function.Injective t := by
      change Function.Injective ![(F.splitA j).val, (p.getVert 4).val, (p.getVert 5).val, (p.getVert 6).val, (F.splitB i).val, (F.center 1).val]
      unfold Matrix.vecCons
      refine Fin.cons_injective_of_injective ?_ ?_
      · simpa only [Fin.range_cons, Matrix.range_empty, Set.mem_insert_iff,
          Set.mem_empty_iff_false, or_false, not_or] using
          (show (F.splitA j).val ≠ (p.getVert 4).val ∧ (F.splitA j).val ≠ (p.getVert 5).val ∧ (F.splitA j).val ≠ (p.getVert 6).val ∧ (F.splitA j).val ≠ (F.splitB i).val ∧ (F.splitA j).val ≠ (F.center 1).val from
            ⟨(Ne.symm (h4N (F.splitA j))), (Ne.symm (h5N (F.splitA j))), (Ne.symm (h6N (F.splitA j))), (hcross j i), (Ne.symm (hca 1 j))⟩)
      refine Fin.cons_injective_of_injective ?_ ?_
      · simpa only [Fin.range_cons, Matrix.range_empty, Set.mem_insert_iff,
          Set.mem_empty_iff_false, or_false, not_or] using
          (show (p.getVert 4).val ≠ (p.getVert 5).val ∧ (p.getVert 4).val ≠ (p.getVert 6).val ∧ (p.getVert 4).val ≠ (F.splitB i).val ∧ (p.getVert 4).val ≠ (F.center 1).val from
            ⟨(h45n), (h46n), (h4N (F.splitB i)), (h4N (F.center 1))⟩)
      refine Fin.cons_injective_of_injective ?_ ?_
      · simpa only [Fin.range_cons, Matrix.range_empty, Set.mem_insert_iff,
          Set.mem_empty_iff_false, or_false, not_or] using
          (show (p.getVert 5).val ≠ (p.getVert 6).val ∧ (p.getVert 5).val ≠ (F.splitB i).val ∧ (p.getVert 5).val ≠ (F.center 1).val from
            ⟨(h56n), (h5N (F.splitB i)), (h5N (F.center 1))⟩)
      refine Fin.cons_injective_of_injective ?_ ?_
      · simpa only [Fin.range_cons, Matrix.range_empty, Set.mem_insert_iff,
          Set.mem_empty_iff_false, or_false, not_or] using
          (show (p.getVert 6).val ≠ (F.splitB i).val ∧ (p.getVert 6).val ≠ (F.center 1).val from
            ⟨(h6N (F.splitB i)), (h6N (F.center 1))⟩)
      exact injective_pair_iff_ne.mpr (Ne.symm (hcb 1 i))
    have htv : ∀ a : Fin 6, t a ≠ v := by
      intro a
      fin_cases a
      all_goals first | exact (p.getVert _).property | exact (F.splitA j).property.ne.symm | exact (F.splitB i).property.ne.symm | exact (F.center 1).property.ne.symm
    exact rooted_five_path_same_color_false hr v c t ht htv (F.splitA j).property
      (F.center 1).property hj.symm h45 h56 h67 hi.2.2.1.symm 1 3 (by decide) (hc4.trans hc6.symm)
  have mY : (p.getVert 4).val ∉ F.splitPoolB := by
    intro hm
    obtain ⟨j, hj⟩ := (Finset.mem_filter.mp hm).2
    let t : Fin 6 → V := ![(F.center 0).val, (p.getVert 1).val, (p.getVert 2).val, (p.getVert 3).val, (p.getVert 4).val, (F.splitB j).val]
    have ht : Function.Injective t := by
      change Function.Injective ![(F.center 0).val, (p.getVert 1).val, (p.getVert 2).val, (p.getVert 3).val, (p.getVert 4).val, (F.splitB j).val]
      unfold Matrix.vecCons
      refine Fin.cons_injective_of_injective ?_ ?_
      · simpa only [Fin.range_cons, Matrix.range_empty, Set.mem_insert_iff,
          Set.mem_empty_iff_false, or_false, not_or] using
          (show (F.center 0).val ≠ (p.getVert 1).val ∧ (F.center 0).val ≠ (p.getVert 2).val ∧ (F.center 0).val ≠ (p.getVert 3).val ∧ (F.center 0).val ≠ (p.getVert 4).val ∧ (F.center 0).val ≠ (F.splitB j).val from
            ⟨(Ne.symm (h1N (F.center 0))), (Ne.symm (h2N (F.center 0))), (Ne.symm (h3N (F.center 0))), (Ne.symm (h4N (F.center 0))), (hcb 0 j)⟩)
      refine Fin.cons_injective_of_injective ?_ ?_
      · simpa only [Fin.range_cons, Matrix.range_empty, Set.mem_insert_iff,
          Set.mem_empty_iff_false, or_false, not_or] using
          (show (p.getVert 1).val ≠ (p.getVert 2).val ∧ (p.getVert 1).val ≠ (p.getVert 3).val ∧ (p.getVert 1).val ≠ (p.getVert 4).val ∧ (p.getVert 1).val ≠ (F.splitB j).val from
            ⟨(h12n), (h13n), (h14n), (h1N (F.splitB j))⟩)
      refine Fin.cons_injective_of_injective ?_ ?_
      · simpa only [Fin.range_cons, Matrix.range_empty, Set.mem_insert_iff,
          Set.mem_empty_iff_false, or_false, not_or] using
          (show (p.getVert 2).val ≠ (p.getVert 3).val ∧ (p.getVert 2).val ≠ (p.getVert 4).val ∧ (p.getVert 2).val ≠ (F.splitB j).val from
            ⟨(h23n), (h24n), (h2N (F.splitB j))⟩)
      refine Fin.cons_injective_of_injective ?_ ?_
      · simpa only [Fin.range_cons, Matrix.range_empty, Set.mem_insert_iff,
          Set.mem_empty_iff_false, or_false, not_or] using
          (show (p.getVert 3).val ≠ (p.getVert 4).val ∧ (p.getVert 3).val ≠ (F.splitB j).val from
            ⟨(h34n), (h3N (F.splitB j))⟩)
      exact injective_pair_iff_ne.mpr (h4N (F.splitB j))
    have htv : ∀ a : Fin 6, t a ≠ v := by
      intro a
      fin_cases a
      all_goals first | exact (p.getVert _).property | exact (F.center 0).property.ne.symm | exact (F.splitB j).property.ne.symm
    exact rooted_five_path_same_color_false hr v c t ht htv (F.center 0).property
      (F.splitB j).property h01 h12 h23 h34 hj 0 2 (by decide) ((F.center_color 0).trans hc2.symm)
  have mA : (p.getVert 4).val ∉ F.centerPool 0 := by
    intro hm
    have hadj := (Finset.mem_filter.mp hm).2
    have hadjD : (G.induce {x | x ≠ v}).Adj (F.centerD 0) (p.getVert 4) := hadj
    exact (c.valid hadjD) ((F.center_color 0).trans hc4.symm)
  exact ⟨F.mem_residualPool_iff.mpr ⟨h3O, tA, tB, tX, tY⟩,
    F.mem_residualPool_iff.mpr ⟨h4O, mA, mB, mX, mY⟩⟩

end TaskH.Seven
#print axioms TaskH.Seven.DegreeTwelveFrame.seven_path_internal_outside_of_own_leaf_absent
#print axioms TaskH.Seven.DegreeTwelveFrame.seven_path_middle_residual_of_own_leaf_absent
