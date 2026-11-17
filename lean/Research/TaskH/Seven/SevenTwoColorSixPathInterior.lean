import Research.TaskH.Seven.SevenTwoColorResidual

/-! Actual six-edge center-avoiding paths. The boundary-exclusion proof
displays all ten five-edge paths and the distinct seven-cycle required for
the remaining r-in-B case. No residual-size or degree premise is used here. -/

set_option autoImplicit false
universe u
namespace TaskH.Seven
open SimpleGraph
open scoped Classical
variable {V : Type u} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem DegreeTwelveFrame.six_path_internal_outside {v : V}
    {c : (G.induce {x | x ≠ v}).Coloring (Fin 7)}
    (F : DegreeTwelveFrame G v c) (i : Fin 5)
    (p : (G.induce {x | x ≠ v}).Walk (F.splitAD i) (F.splitBD i))
    (hp : p.IsPath)
    (hf : Follows p c (Equiv.swap (c (F.splitAD i)) (F.singletonIndex 0).val))
    (hl : p.length = 6)
    (havoid : ∀ n ≤ p.length, p.getVert n ≠ F.centerD 0)
    (n : ℕ) (hn0 : 0 < n) (hn6 : n < 6) :
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
    have hc := twoColor_color_at p c (F.singletonIndex 0).val hf n (by omega)
    have hstart : c (F.splitAD i) = (F.pairIndex i).val := F.splitA_color i
    by_cases heven : n % 2 = 0
    · rw [ite_eq_left heven, hstart] at hc
      rcases (F.pair_fiber_as_deleted i (p.getVert n) hadj).mp hc with hpi | hqi
      · have hh := (hp.getVert_eq_start_iff (by omega : n ≤ p.length)).mp hpi
        omega
      · have hh := (hp.getVert_eq_end_iff (by omega : n ≤ p.length)).mp hqi
        omega
    · rw [ite_eq_right heven] at hc
      exact havoid n (by omega) ((F.singleton_fiber_as_deleted 0 (p.getVert n) hadj).mp hc)

theorem DegreeTwelveFrame.six_path_three_middle_residual
    (hr : RainbowSevenCycles G) {v : V}
    {c : (G.induce {x | x ≠ v}).Coloring (Fin 7)}
    (F : DegreeTwelveFrame G v c) (hF : F.IsPureSplit) (i : Fin 5)
    (p : (G.induce {x | x ≠ v}).Walk (F.splitAD i) (F.splitBD i))
    (hp : p.IsPath)
    (hf : Follows p c (Equiv.swap (c (F.splitAD i)) (F.singletonIndex 0).val))
    (hl : p.length = 6)
    (havoid : ∀ n ≤ p.length, p.getVert n ≠ F.centerD 0) :
    (p.getVert 2).val ∈ F.residualPool ∧ (p.getVert 3).val ∈ F.residualPool ∧
      (p.getVert 4).val ∈ F.residualPool := by
  have hdec :
      (inferInstance : DecidableRel G.Adj) =
        (fun a b => Classical.propDecidable (G.Adj a b)) := by
    funext a b
    exact Subsingleton.elim _ _
  cases hdec
  classical
  have h1O := F.six_path_internal_outside i p hp hf hl havoid 1 (by decide) (by decide)
  have h2O := F.six_path_internal_outside i p hp hf hl havoid 2 (by decide) (by decide)
  have h3O := F.six_path_internal_outside i p hp hf hl havoid 3 (by decide) (by decide)
  have h4O := F.six_path_internal_outside i p hp hf hl havoid 4 (by decide) (by decide)
  have h5O := F.six_path_internal_outside i p hp hf hl havoid 5 (by decide) (by decide)
  have h1N := rootOutside_ne_neighbor h1O
  have h2N := rootOutside_ne_neighbor h2O
  have h3N := rootOutside_ne_neighbor h3O
  have h4N := rootOutside_ne_neighbor h4O
  have h5N := rootOutside_ne_neighbor h5O
  have hposne (n m : ℕ) (hn : n ≤ p.length) (hm : m ≤ p.length) (hne : n ≠ m) :
      (p.getVert n).val ≠ (p.getVert m).val := by
    intro he
    exact hne (hp.getVert_injOn hn hm (Subtype.ext he))
  have h12n := hposne 1 2 (by omega) (by omega) (by decide)
  have h13n := hposne 1 3 (by omega) (by omega) (by decide)
  have h14n := hposne 1 4 (by omega) (by omega) (by decide)
  have h15n := hposne 1 5 (by omega) (by omega) (by decide)
  have h23n := hposne 2 3 (by omega) (by omega) (by decide)
  have h24n := hposne 2 4 (by omega) (by omega) (by decide)
  have h25n := hposne 2 5 (by omega) (by omega) (by decide)
  have h34n := hposne 3 4 (by omega) (by omega) (by decide)
  have h35n := hposne 3 5 (by omega) (by omega) (by decide)
  have h45n := hposne 4 5 (by omega) (by omega) (by decide)
  have hi := F.splitAB_adjacencies i (hF i)
  have hab := F.center_center_ne (by decide : (0 : Fin 2) ≠ 1)
  have hca := F.center_splitA_ne
  have hcb := F.center_splitB_ne
  have hcross := F.splitA_splitB_ne
  have hlast : p.getVert 6 = F.splitBD i := by simpa only [hl] using p.getVert_length
  have h01 : G.Adj (F.splitA i).val (p.getVert 1).val := by
    have he := p.adj_getVert_succ (i := 0) (by omega)
    rw [Walk.getVert_zero] at he
    change G.Adj (F.splitA i).val (p.getVert 1).val at he
    exact he
  have h12 : G.Adj (p.getVert 1).val (p.getVert 2).val := p.adj_getVert_succ (i := 1) (by omega)
  have h23 : G.Adj (p.getVert 2).val (p.getVert 3).val := p.adj_getVert_succ (i := 2) (by omega)
  have h34 : G.Adj (p.getVert 3).val (p.getVert 4).val := p.adj_getVert_succ (i := 3) (by omega)
  have h45 : G.Adj (p.getVert 4).val (p.getVert 5).val := p.adj_getVert_succ (i := 4) (by omega)
  have h56 : G.Adj (p.getVert 5).val (F.splitB i).val := by
    have he := p.adj_getVert_succ (i := 5) (by omega)
    rw [hlast] at he
    change G.Adj (p.getVert 5).val (F.splitB i).val at he
    exact he
  have hc1 : c (p.getVert 1) = (F.singletonIndex 0).val := by
    simpa using twoColor_color_at p c (F.singletonIndex 0).val hf 1 (by omega)
  have hc2 : c (p.getVert 2) = (F.pairIndex i).val := by
    simpa using (twoColor_color_at p c (F.singletonIndex 0).val hf 2 (by omega)).trans (F.splitA_color i)
  have hc3 : c (p.getVert 3) = (F.singletonIndex 0).val := by
    simpa using twoColor_color_at p c (F.singletonIndex 0).val hf 3 (by omega)
  have hc4 : c (p.getVert 4) = (F.pairIndex i).val := by
    simpa using (twoColor_color_at p c (F.singletonIndex 0).val hf 4 (by omega)).trans (F.splitA_color i)
  have hc5 : c (p.getVert 5) = (F.singletonIndex 0).val := by
    simpa using twoColor_color_at p c (F.singletonIndex 0).val hf 5 (by omega)
  have rA : (p.getVert 2).val ∉ F.centerPool 0 := by
    intro hm
    have har := (Finset.mem_filter.mp hm).2
    let t : Fin 6 → V := ![(F.center 0).val, (p.getVert 2).val, (p.getVert 3).val,
      (p.getVert 4).val, (p.getVert 5).val, (F.splitB i).val]
    have ht : Function.Injective t := by
      change Function.Injective ![(F.center 0).val, (p.getVert 2).val, (p.getVert 3).val, (p.getVert 4).val, (p.getVert 5).val, (F.splitB i).val]
      unfold Matrix.vecCons
      refine Fin.cons_injective_of_injective ?_ ?_
      · simpa only [Fin.range_cons, Matrix.range_empty, Set.mem_insert_iff,
          Set.mem_empty_iff_false, or_false, not_or] using
          (show (F.center 0).val ≠ (p.getVert 2).val ∧ (F.center 0).val ≠ (p.getVert 3).val ∧ (F.center 0).val ≠ (p.getVert 4).val ∧ (F.center 0).val ≠ (p.getVert 5).val ∧ (F.center 0).val ≠ (F.splitB i).val from
            ⟨(Ne.symm (h2N (F.center 0))), (Ne.symm (h3N (F.center 0))), (Ne.symm (h4N (F.center 0))), (Ne.symm (h5N (F.center 0))), (hcb 0 i)⟩)
      refine Fin.cons_injective_of_injective ?_ ?_
      · simpa only [Fin.range_cons, Matrix.range_empty, Set.mem_insert_iff,
          Set.mem_empty_iff_false, or_false, not_or] using
          (show (p.getVert 2).val ≠ (p.getVert 3).val ∧ (p.getVert 2).val ≠ (p.getVert 4).val ∧ (p.getVert 2).val ≠ (p.getVert 5).val ∧ (p.getVert 2).val ≠ (F.splitB i).val from
            ⟨(h23n), (h24n), (h25n), (h2N (F.splitB i))⟩)
      refine Fin.cons_injective_of_injective ?_ ?_
      · simpa only [Fin.range_cons, Matrix.range_empty, Set.mem_insert_iff,
          Set.mem_empty_iff_false, or_false, not_or] using
          (show (p.getVert 3).val ≠ (p.getVert 4).val ∧ (p.getVert 3).val ≠ (p.getVert 5).val ∧ (p.getVert 3).val ≠ (F.splitB i).val from
            ⟨(h34n), (h35n), (h3N (F.splitB i))⟩)
      refine Fin.cons_injective_of_injective ?_ ?_
      · simpa only [Fin.range_cons, Matrix.range_empty, Set.mem_insert_iff,
          Set.mem_empty_iff_false, or_false, not_or] using
          (show (p.getVert 4).val ≠ (p.getVert 5).val ∧ (p.getVert 4).val ≠ (F.splitB i).val from
            ⟨(h45n), (h4N (F.splitB i))⟩)
      exact injective_pair_iff_ne.mpr (h5N (F.splitB i))
    have htv : ∀ a : Fin 6, t a ≠ v := by
      intro a
      fin_cases a
      all_goals first | exact (F.center 0).property.ne.symm | exact (p.getVert _).property | exact (F.splitB i).property.ne.symm
    exact rooted_five_path_same_color_false hr v c t ht htv (F.center 0).property
      (F.splitB i).property har h23 h34 h45 h56 2 4 (by decide) (hc3.trans hc5.symm)
  have rB : (p.getVert 2).val ∉ F.centerPool 1 := by
    intro hm
    have hbr := (Finset.mem_filter.mp hm).2
    let f : Fin 7 → V := ![(F.splitA i).val, (p.getVert 1).val, (p.getVert 2).val,
      (F.center 1).val, (F.splitB i).val, v, (F.center 0).val]
    have hfinj : Function.Injective f := by
      change Function.Injective ![(F.splitA i).val, (p.getVert 1).val, (p.getVert 2).val, (F.center 1).val, (F.splitB i).val, v, (F.center 0).val]
      unfold Matrix.vecCons
      refine Fin.cons_injective_of_injective ?_ ?_
      · simpa only [Fin.range_cons, Matrix.range_empty, Set.mem_insert_iff,
          Set.mem_empty_iff_false, or_false, not_or] using
          (show (F.splitA i).val ≠ (p.getVert 1).val ∧ (F.splitA i).val ≠ (p.getVert 2).val ∧ (F.splitA i).val ≠ (F.center 1).val ∧ (F.splitA i).val ≠ (F.splitB i).val ∧ (F.splitA i).val ≠ v ∧ (F.splitA i).val ≠ (F.center 0).val from
            ⟨(Ne.symm (h1N (F.splitA i))), (Ne.symm (h2N (F.splitA i))), (Ne.symm (hca 1 i)), (hcross i i), ((F.splitA i).property.ne.symm), (Ne.symm (hca 0 i))⟩)
      refine Fin.cons_injective_of_injective ?_ ?_
      · simpa only [Fin.range_cons, Matrix.range_empty, Set.mem_insert_iff,
          Set.mem_empty_iff_false, or_false, not_or] using
          (show (p.getVert 1).val ≠ (p.getVert 2).val ∧ (p.getVert 1).val ≠ (F.center 1).val ∧ (p.getVert 1).val ≠ (F.splitB i).val ∧ (p.getVert 1).val ≠ v ∧ (p.getVert 1).val ≠ (F.center 0).val from
            ⟨(h12n), (h1N (F.center 1)), (h1N (F.splitB i)), ((p.getVert 1).property), (h1N (F.center 0))⟩)
      refine Fin.cons_injective_of_injective ?_ ?_
      · simpa only [Fin.range_cons, Matrix.range_empty, Set.mem_insert_iff,
          Set.mem_empty_iff_false, or_false, not_or] using
          (show (p.getVert 2).val ≠ (F.center 1).val ∧ (p.getVert 2).val ≠ (F.splitB i).val ∧ (p.getVert 2).val ≠ v ∧ (p.getVert 2).val ≠ (F.center 0).val from
            ⟨(h2N (F.center 1)), (h2N (F.splitB i)), ((p.getVert 2).property), (h2N (F.center 0))⟩)
      refine Fin.cons_injective_of_injective ?_ ?_
      · simpa only [Fin.range_cons, Matrix.range_empty, Set.mem_insert_iff,
          Set.mem_empty_iff_false, or_false, not_or] using
          (show (F.center 1).val ≠ (F.splitB i).val ∧ (F.center 1).val ≠ v ∧ (F.center 1).val ≠ (F.center 0).val from
            ⟨(hcb 1 i), ((F.center 1).property.ne.symm), (Ne.symm hab)⟩)
      refine Fin.cons_injective_of_injective ?_ ?_
      · simpa only [Fin.range_cons, Matrix.range_empty, Set.mem_insert_iff,
          Set.mem_empty_iff_false, or_false, not_or] using
          (show (F.splitB i).val ≠ v ∧ (F.splitB i).val ≠ (F.center 0).val from
            ⟨((F.splitB i).property.ne.symm), (Ne.symm (hcb 0 i))⟩)
      exact injective_pair_iff_ne.mpr ((F.center 0).property.ne)
    have hfC : IsHeptagon G f := ⟨hfinj, h01, h12, hbr.symm, hi.2.2.1,
      (F.splitB i).property.symm, (F.center 0).property, hi.1⟩
    exact rainbow_heptagon_same_color_impossible hr v c f hfC (F.splitA i).val
      (p.getVert 2).val (F.splitA i).property.ne.symm (p.getVert 2).property
      (Ne.symm (h2N (F.splitA i))) ⟨0, rfl⟩ ⟨2, rfl⟩
      ((F.splitA_color i).trans hc2.symm)
  have rX : (p.getVert 2).val ∉ F.splitPoolA := by
    intro hm
    obtain ⟨j, hj⟩ := (Finset.mem_filter.mp hm).2
    let t : Fin 6 → V := ![(F.splitA j).val, (p.getVert 2).val, (p.getVert 3).val, (p.getVert 4).val, (p.getVert 5).val, (F.splitB i).val]
    have ht : Function.Injective t := by
      change Function.Injective ![(F.splitA j).val, (p.getVert 2).val, (p.getVert 3).val, (p.getVert 4).val, (p.getVert 5).val, (F.splitB i).val]
      unfold Matrix.vecCons
      refine Fin.cons_injective_of_injective ?_ ?_
      · simpa only [Fin.range_cons, Matrix.range_empty, Set.mem_insert_iff,
          Set.mem_empty_iff_false, or_false, not_or] using
          (show (F.splitA j).val ≠ (p.getVert 2).val ∧ (F.splitA j).val ≠ (p.getVert 3).val ∧ (F.splitA j).val ≠ (p.getVert 4).val ∧ (F.splitA j).val ≠ (p.getVert 5).val ∧ (F.splitA j).val ≠ (F.splitB i).val from
            ⟨(Ne.symm (h2N (F.splitA j))), (Ne.symm (h3N (F.splitA j))), (Ne.symm (h4N (F.splitA j))), (Ne.symm (h5N (F.splitA j))), (hcross j i)⟩)
      refine Fin.cons_injective_of_injective ?_ ?_
      · simpa only [Fin.range_cons, Matrix.range_empty, Set.mem_insert_iff,
          Set.mem_empty_iff_false, or_false, not_or] using
          (show (p.getVert 2).val ≠ (p.getVert 3).val ∧ (p.getVert 2).val ≠ (p.getVert 4).val ∧ (p.getVert 2).val ≠ (p.getVert 5).val ∧ (p.getVert 2).val ≠ (F.splitB i).val from
            ⟨(h23n), (h24n), (h25n), (h2N (F.splitB i))⟩)
      refine Fin.cons_injective_of_injective ?_ ?_
      · simpa only [Fin.range_cons, Matrix.range_empty, Set.mem_insert_iff,
          Set.mem_empty_iff_false, or_false, not_or] using
          (show (p.getVert 3).val ≠ (p.getVert 4).val ∧ (p.getVert 3).val ≠ (p.getVert 5).val ∧ (p.getVert 3).val ≠ (F.splitB i).val from
            ⟨(h34n), (h35n), (h3N (F.splitB i))⟩)
      refine Fin.cons_injective_of_injective ?_ ?_
      · simpa only [Fin.range_cons, Matrix.range_empty, Set.mem_insert_iff,
          Set.mem_empty_iff_false, or_false, not_or] using
          (show (p.getVert 4).val ≠ (p.getVert 5).val ∧ (p.getVert 4).val ≠ (F.splitB i).val from
            ⟨(h45n), (h4N (F.splitB i))⟩)
      exact injective_pair_iff_ne.mpr (h5N (F.splitB i))
    have htv : ∀ a : Fin 6, t a ≠ v := by
      intro a
      fin_cases a
      all_goals first | exact (p.getVert _).property | exact (F.splitA j).property.ne.symm | exact (F.splitB i).property.ne.symm
    exact rooted_five_path_same_color_false hr v c t ht htv (F.splitA j).property
      (F.splitB i).property hj.symm h23 h34 h45 h56 2 4 (by decide) (hc3.trans hc5.symm)
  have rY : (p.getVert 2).val ∉ F.splitPoolB := by
    intro hm
    obtain ⟨j, hj⟩ := (Finset.mem_filter.mp hm).2
    obtain ⟨l, hlj⟩ : ∃ l : Fin 5, l ≠ j := exists_ne j
    have hjE := F.splitAB_adjacencies j (hF j)
    have hlE := F.splitAB_adjacencies l (hF l)
    have hBjl := F.splitB_injective.ne (Ne.symm hlj)
    let t : Fin 6 → V := ![(F.splitA i).val, (p.getVert 1).val, (p.getVert 2).val, (F.splitB j).val, (F.center 1).val, (F.splitB l).val]
    have ht : Function.Injective t := by
      change Function.Injective ![(F.splitA i).val, (p.getVert 1).val, (p.getVert 2).val, (F.splitB j).val, (F.center 1).val, (F.splitB l).val]
      unfold Matrix.vecCons
      refine Fin.cons_injective_of_injective ?_ ?_
      · simpa only [Fin.range_cons, Matrix.range_empty, Set.mem_insert_iff,
          Set.mem_empty_iff_false, or_false, not_or] using
          (show (F.splitA i).val ≠ (p.getVert 1).val ∧ (F.splitA i).val ≠ (p.getVert 2).val ∧ (F.splitA i).val ≠ (F.splitB j).val ∧ (F.splitA i).val ≠ (F.center 1).val ∧ (F.splitA i).val ≠ (F.splitB l).val from
            ⟨(Ne.symm (h1N (F.splitA i))), (Ne.symm (h2N (F.splitA i))), (hcross i j), (Ne.symm (hca 1 i)), (hcross i l)⟩)
      refine Fin.cons_injective_of_injective ?_ ?_
      · simpa only [Fin.range_cons, Matrix.range_empty, Set.mem_insert_iff,
          Set.mem_empty_iff_false, or_false, not_or] using
          (show (p.getVert 1).val ≠ (p.getVert 2).val ∧ (p.getVert 1).val ≠ (F.splitB j).val ∧ (p.getVert 1).val ≠ (F.center 1).val ∧ (p.getVert 1).val ≠ (F.splitB l).val from
            ⟨(h12n), (h1N (F.splitB j)), (h1N (F.center 1)), (h1N (F.splitB l))⟩)
      refine Fin.cons_injective_of_injective ?_ ?_
      · simpa only [Fin.range_cons, Matrix.range_empty, Set.mem_insert_iff,
          Set.mem_empty_iff_false, or_false, not_or] using
          (show (p.getVert 2).val ≠ (F.splitB j).val ∧ (p.getVert 2).val ≠ (F.center 1).val ∧ (p.getVert 2).val ≠ (F.splitB l).val from
            ⟨(h2N (F.splitB j)), (h2N (F.center 1)), (h2N (F.splitB l))⟩)
      refine Fin.cons_injective_of_injective ?_ ?_
      · simpa only [Fin.range_cons, Matrix.range_empty, Set.mem_insert_iff,
          Set.mem_empty_iff_false, or_false, not_or] using
          (show (F.splitB j).val ≠ (F.center 1).val ∧ (F.splitB j).val ≠ (F.splitB l).val from
            ⟨(Ne.symm (hcb 1 j)), (hBjl)⟩)
      exact injective_pair_iff_ne.mpr (hcb 1 l)
    have htv : ∀ a : Fin 6, t a ≠ v := by
      intro a
      fin_cases a
      all_goals first | exact (p.getVert _).property | exact (F.splitA i).property.ne.symm | exact (F.splitB j).property.ne.symm | exact (F.center 1).property.ne.symm | exact (F.splitB l).property.ne.symm
    exact rooted_five_path_same_color_false hr v c t ht htv (F.splitA i).property
      (F.splitB l).property h01 h12 hj hjE.2.2.1.symm hlE.2.2.1 0 2 (by decide) ((F.splitA_color i).trans hc2.symm)
  have sA : (p.getVert 4).val ∉ F.centerPool 0 := by
    intro hm
    have hj := (Finset.mem_filter.mp hm).2
    let t : Fin 6 → V := ![(F.center 0).val, (p.getVert 4).val, (p.getVert 3).val, (p.getVert 2).val, (p.getVert 1).val, (F.splitA i).val]
    have ht : Function.Injective t := by
      change Function.Injective ![(F.center 0).val, (p.getVert 4).val, (p.getVert 3).val, (p.getVert 2).val, (p.getVert 1).val, (F.splitA i).val]
      unfold Matrix.vecCons
      refine Fin.cons_injective_of_injective ?_ ?_
      · simpa only [Fin.range_cons, Matrix.range_empty, Set.mem_insert_iff,
          Set.mem_empty_iff_false, or_false, not_or] using
          (show (F.center 0).val ≠ (p.getVert 4).val ∧ (F.center 0).val ≠ (p.getVert 3).val ∧ (F.center 0).val ≠ (p.getVert 2).val ∧ (F.center 0).val ≠ (p.getVert 1).val ∧ (F.center 0).val ≠ (F.splitA i).val from
            ⟨(Ne.symm (h4N (F.center 0))), (Ne.symm (h3N (F.center 0))), (Ne.symm (h2N (F.center 0))), (Ne.symm (h1N (F.center 0))), (hca 0 i)⟩)
      refine Fin.cons_injective_of_injective ?_ ?_
      · simpa only [Fin.range_cons, Matrix.range_empty, Set.mem_insert_iff,
          Set.mem_empty_iff_false, or_false, not_or] using
          (show (p.getVert 4).val ≠ (p.getVert 3).val ∧ (p.getVert 4).val ≠ (p.getVert 2).val ∧ (p.getVert 4).val ≠ (p.getVert 1).val ∧ (p.getVert 4).val ≠ (F.splitA i).val from
            ⟨(Ne.symm h34n), (Ne.symm h24n), (Ne.symm h14n), (h4N (F.splitA i))⟩)
      refine Fin.cons_injective_of_injective ?_ ?_
      · simpa only [Fin.range_cons, Matrix.range_empty, Set.mem_insert_iff,
          Set.mem_empty_iff_false, or_false, not_or] using
          (show (p.getVert 3).val ≠ (p.getVert 2).val ∧ (p.getVert 3).val ≠ (p.getVert 1).val ∧ (p.getVert 3).val ≠ (F.splitA i).val from
            ⟨(Ne.symm h23n), (Ne.symm h13n), (h3N (F.splitA i))⟩)
      refine Fin.cons_injective_of_injective ?_ ?_
      · simpa only [Fin.range_cons, Matrix.range_empty, Set.mem_insert_iff,
          Set.mem_empty_iff_false, or_false, not_or] using
          (show (p.getVert 2).val ≠ (p.getVert 1).val ∧ (p.getVert 2).val ≠ (F.splitA i).val from
            ⟨(Ne.symm h12n), (h2N (F.splitA i))⟩)
      exact injective_pair_iff_ne.mpr (h1N (F.splitA i))
    have htv : ∀ a : Fin 6, t a ≠ v := by
      intro a
      fin_cases a
      all_goals first | exact (p.getVert _).property | exact (F.center 0).property.ne.symm | exact (F.splitA i).property.ne.symm
    exact rooted_five_path_same_color_false hr v c t ht htv (F.center 0).property
      (F.splitA i).property hj h34.symm h23.symm h12.symm h01.symm 2 4 (by decide) (hc3.trans hc1.symm)
  have sB : (p.getVert 4).val ∉ F.centerPool 1 := by
    intro hm
    have hj := (Finset.mem_filter.mp hm).2
    let t : Fin 6 → V := ![(F.splitA i).val, (p.getVert 1).val, (p.getVert 2).val, (p.getVert 3).val, (p.getVert 4).val, (F.center 1).val]
    have ht : Function.Injective t := by
      change Function.Injective ![(F.splitA i).val, (p.getVert 1).val, (p.getVert 2).val, (p.getVert 3).val, (p.getVert 4).val, (F.center 1).val]
      unfold Matrix.vecCons
      refine Fin.cons_injective_of_injective ?_ ?_
      · simpa only [Fin.range_cons, Matrix.range_empty, Set.mem_insert_iff,
          Set.mem_empty_iff_false, or_false, not_or] using
          (show (F.splitA i).val ≠ (p.getVert 1).val ∧ (F.splitA i).val ≠ (p.getVert 2).val ∧ (F.splitA i).val ≠ (p.getVert 3).val ∧ (F.splitA i).val ≠ (p.getVert 4).val ∧ (F.splitA i).val ≠ (F.center 1).val from
            ⟨(Ne.symm (h1N (F.splitA i))), (Ne.symm (h2N (F.splitA i))), (Ne.symm (h3N (F.splitA i))), (Ne.symm (h4N (F.splitA i))), (Ne.symm (hca 1 i))⟩)
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
      all_goals first | exact (p.getVert _).property | exact (F.splitA i).property.ne.symm | exact (F.center 1).property.ne.symm
    exact rooted_five_path_same_color_false hr v c t ht htv (F.splitA i).property
      (F.center 1).property h01 h12 h23 h34 hj.symm 0 2 (by decide) ((F.splitA_color i).trans hc2.symm)
  have sX : (p.getVert 4).val ∉ F.splitPoolA := by
    intro hm
    obtain ⟨j, hj⟩ := (Finset.mem_filter.mp hm).2
    have hji : j ≠ i := by
      intro he
      subst j
      have hjD : (G.induce {x | x ≠ v}).Adj (p.getVert 4) (F.splitAD i) := hj
      exact (c.valid hjD) (hc4.trans (F.splitA_color i).symm)
    have hAji := F.splitA_injective.ne hji
    let t : Fin 6 → V := ![(F.splitA j).val, (p.getVert 4).val, (p.getVert 3).val, (p.getVert 2).val, (p.getVert 1).val, (F.splitA i).val]
    have ht : Function.Injective t := by
      change Function.Injective ![(F.splitA j).val, (p.getVert 4).val, (p.getVert 3).val, (p.getVert 2).val, (p.getVert 1).val, (F.splitA i).val]
      unfold Matrix.vecCons
      refine Fin.cons_injective_of_injective ?_ ?_
      · simpa only [Fin.range_cons, Matrix.range_empty, Set.mem_insert_iff,
          Set.mem_empty_iff_false, or_false, not_or] using
          (show (F.splitA j).val ≠ (p.getVert 4).val ∧ (F.splitA j).val ≠ (p.getVert 3).val ∧ (F.splitA j).val ≠ (p.getVert 2).val ∧ (F.splitA j).val ≠ (p.getVert 1).val ∧ (F.splitA j).val ≠ (F.splitA i).val from
            ⟨(Ne.symm (h4N (F.splitA j))), (Ne.symm (h3N (F.splitA j))), (Ne.symm (h2N (F.splitA j))), (Ne.symm (h1N (F.splitA j))), (hAji)⟩)
      refine Fin.cons_injective_of_injective ?_ ?_
      · simpa only [Fin.range_cons, Matrix.range_empty, Set.mem_insert_iff,
          Set.mem_empty_iff_false, or_false, not_or] using
          (show (p.getVert 4).val ≠ (p.getVert 3).val ∧ (p.getVert 4).val ≠ (p.getVert 2).val ∧ (p.getVert 4).val ≠ (p.getVert 1).val ∧ (p.getVert 4).val ≠ (F.splitA i).val from
            ⟨(Ne.symm h34n), (Ne.symm h24n), (Ne.symm h14n), (h4N (F.splitA i))⟩)
      refine Fin.cons_injective_of_injective ?_ ?_
      · simpa only [Fin.range_cons, Matrix.range_empty, Set.mem_insert_iff,
          Set.mem_empty_iff_false, or_false, not_or] using
          (show (p.getVert 3).val ≠ (p.getVert 2).val ∧ (p.getVert 3).val ≠ (p.getVert 1).val ∧ (p.getVert 3).val ≠ (F.splitA i).val from
            ⟨(Ne.symm h23n), (Ne.symm h13n), (h3N (F.splitA i))⟩)
      refine Fin.cons_injective_of_injective ?_ ?_
      · simpa only [Fin.range_cons, Matrix.range_empty, Set.mem_insert_iff,
          Set.mem_empty_iff_false, or_false, not_or] using
          (show (p.getVert 2).val ≠ (p.getVert 1).val ∧ (p.getVert 2).val ≠ (F.splitA i).val from
            ⟨(Ne.symm h12n), (h2N (F.splitA i))⟩)
      exact injective_pair_iff_ne.mpr (h1N (F.splitA i))
    have htv : ∀ a : Fin 6, t a ≠ v := by
      intro a
      fin_cases a
      all_goals first | exact (p.getVert _).property | exact (F.splitA j).property.ne.symm | exact (F.splitA i).property.ne.symm
    exact rooted_five_path_same_color_false hr v c t ht htv (F.splitA j).property
      (F.splitA i).property hj.symm h34.symm h23.symm h12.symm h01.symm 2 4 (by decide) (hc3.trans hc1.symm)
  have sY : (p.getVert 4).val ∉ F.splitPoolB := by
    intro hm
    obtain ⟨j, hj⟩ := (Finset.mem_filter.mp hm).2
    let t : Fin 6 → V := ![(F.splitA i).val, (p.getVert 1).val, (p.getVert 2).val, (p.getVert 3).val, (p.getVert 4).val, (F.splitB j).val]
    have ht : Function.Injective t := by
      change Function.Injective ![(F.splitA i).val, (p.getVert 1).val, (p.getVert 2).val, (p.getVert 3).val, (p.getVert 4).val, (F.splitB j).val]
      unfold Matrix.vecCons
      refine Fin.cons_injective_of_injective ?_ ?_
      · simpa only [Fin.range_cons, Matrix.range_empty, Set.mem_insert_iff,
          Set.mem_empty_iff_false, or_false, not_or] using
          (show (F.splitA i).val ≠ (p.getVert 1).val ∧ (F.splitA i).val ≠ (p.getVert 2).val ∧ (F.splitA i).val ≠ (p.getVert 3).val ∧ (F.splitA i).val ≠ (p.getVert 4).val ∧ (F.splitA i).val ≠ (F.splitB j).val from
            ⟨(Ne.symm (h1N (F.splitA i))), (Ne.symm (h2N (F.splitA i))), (Ne.symm (h3N (F.splitA i))), (Ne.symm (h4N (F.splitA i))), (hcross i j)⟩)
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
      all_goals first | exact (p.getVert _).property | exact (F.splitA i).property.ne.symm | exact (F.splitB j).property.ne.symm
    exact rooted_five_path_same_color_false hr v c t ht htv (F.splitA i).property
      (F.splitB j).property h01 h12 h23 h34 hj 1 3 (by decide) (hc1.trans hc3.symm)
  have mA : (p.getVert 3).val ∉ F.centerPool 0 := by
    intro hm
    have ham := (Finset.mem_filter.mp hm).2
    have hamD : (G.induce {x | x ≠ v}).Adj (F.centerD 0) (p.getVert 3) := ham
    exact (c.valid hamD) ((F.center_color 0).trans hc3.symm)
  have mB : (p.getVert 3).val ∉ F.centerPool 1 := by
    intro hm
    have hj := (Finset.mem_filter.mp hm).2
    let j : Fin 5 := 0
    have hjE := F.splitAB_adjacencies j (hF j)
    let t : Fin 6 → V := ![(F.splitA i).val, (p.getVert 1).val, (p.getVert 2).val, (p.getVert 3).val, (F.center 1).val, (F.splitB j).val]
    have ht : Function.Injective t := by
      change Function.Injective ![(F.splitA i).val, (p.getVert 1).val, (p.getVert 2).val, (p.getVert 3).val, (F.center 1).val, (F.splitB j).val]
      unfold Matrix.vecCons
      refine Fin.cons_injective_of_injective ?_ ?_
      · simpa only [Fin.range_cons, Matrix.range_empty, Set.mem_insert_iff,
          Set.mem_empty_iff_false, or_false, not_or] using
          (show (F.splitA i).val ≠ (p.getVert 1).val ∧ (F.splitA i).val ≠ (p.getVert 2).val ∧ (F.splitA i).val ≠ (p.getVert 3).val ∧ (F.splitA i).val ≠ (F.center 1).val ∧ (F.splitA i).val ≠ (F.splitB j).val from
            ⟨(Ne.symm (h1N (F.splitA i))), (Ne.symm (h2N (F.splitA i))), (Ne.symm (h3N (F.splitA i))), (Ne.symm (hca 1 i)), (hcross i j)⟩)
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
      all_goals first | exact (p.getVert _).property | exact (F.splitA i).property.ne.symm | exact (F.center 1).property.ne.symm | exact (F.splitB j).property.ne.symm
    exact rooted_five_path_same_color_false hr v c t ht htv (F.splitA i).property
      (F.splitB j).property h01 h12 h23 hj.symm hjE.2.2.1 0 2 (by decide) ((F.splitA_color i).trans hc2.symm)
  have mX : (p.getVert 3).val ∉ F.splitPoolA := by
    intro hm
    obtain ⟨j, hj⟩ := (Finset.mem_filter.mp hm).2
    have hjE := F.splitAB_adjacencies j (hF j)
    let t : Fin 6 → V := ![(F.center 0).val, (F.splitA j).val, (p.getVert 3).val, (p.getVert 4).val, (p.getVert 5).val, (F.splitB i).val]
    have ht : Function.Injective t := by
      change Function.Injective ![(F.center 0).val, (F.splitA j).val, (p.getVert 3).val, (p.getVert 4).val, (p.getVert 5).val, (F.splitB i).val]
      unfold Matrix.vecCons
      refine Fin.cons_injective_of_injective ?_ ?_
      · simpa only [Fin.range_cons, Matrix.range_empty, Set.mem_insert_iff,
          Set.mem_empty_iff_false, or_false, not_or] using
          (show (F.center 0).val ≠ (F.splitA j).val ∧ (F.center 0).val ≠ (p.getVert 3).val ∧ (F.center 0).val ≠ (p.getVert 4).val ∧ (F.center 0).val ≠ (p.getVert 5).val ∧ (F.center 0).val ≠ (F.splitB i).val from
            ⟨(hca 0 j), (Ne.symm (h3N (F.center 0))), (Ne.symm (h4N (F.center 0))), (Ne.symm (h5N (F.center 0))), (hcb 0 i)⟩)
      refine Fin.cons_injective_of_injective ?_ ?_
      · simpa only [Fin.range_cons, Matrix.range_empty, Set.mem_insert_iff,
          Set.mem_empty_iff_false, or_false, not_or] using
          (show (F.splitA j).val ≠ (p.getVert 3).val ∧ (F.splitA j).val ≠ (p.getVert 4).val ∧ (F.splitA j).val ≠ (p.getVert 5).val ∧ (F.splitA j).val ≠ (F.splitB i).val from
            ⟨(Ne.symm (h3N (F.splitA j))), (Ne.symm (h4N (F.splitA j))), (Ne.symm (h5N (F.splitA j))), (hcross j i)⟩)
      refine Fin.cons_injective_of_injective ?_ ?_
      · simpa only [Fin.range_cons, Matrix.range_empty, Set.mem_insert_iff,
          Set.mem_empty_iff_false, or_false, not_or] using
          (show (p.getVert 3).val ≠ (p.getVert 4).val ∧ (p.getVert 3).val ≠ (p.getVert 5).val ∧ (p.getVert 3).val ≠ (F.splitB i).val from
            ⟨(h34n), (h35n), (h3N (F.splitB i))⟩)
      refine Fin.cons_injective_of_injective ?_ ?_
      · simpa only [Fin.range_cons, Matrix.range_empty, Set.mem_insert_iff,
          Set.mem_empty_iff_false, or_false, not_or] using
          (show (p.getVert 4).val ≠ (p.getVert 5).val ∧ (p.getVert 4).val ≠ (F.splitB i).val from
            ⟨(h45n), (h4N (F.splitB i))⟩)
      exact injective_pair_iff_ne.mpr (h5N (F.splitB i))
    have htv : ∀ a : Fin 6, t a ≠ v := by
      intro a
      fin_cases a
      all_goals first | exact (p.getVert _).property | exact (F.center 0).property.ne.symm | exact (F.splitA j).property.ne.symm | exact (F.splitB i).property.ne.symm
    exact rooted_five_path_same_color_false hr v c t ht htv (F.center 0).property
      (F.splitB i).property hjE.1 hj.symm h34 h45 h56 2 4 (by decide) (hc3.trans hc5.symm)
  have mY : (p.getVert 3).val ∉ F.splitPoolB := by
    intro hm
    obtain ⟨j, hj⟩ := (Finset.mem_filter.mp hm).2
    have hjE := F.splitAB_adjacencies j (hF j)
    let t : Fin 6 → V := ![(F.splitA i).val, (p.getVert 1).val, (p.getVert 2).val, (p.getVert 3).val, (F.splitB j).val, (F.center 1).val]
    have ht : Function.Injective t := by
      change Function.Injective ![(F.splitA i).val, (p.getVert 1).val, (p.getVert 2).val, (p.getVert 3).val, (F.splitB j).val, (F.center 1).val]
      unfold Matrix.vecCons
      refine Fin.cons_injective_of_injective ?_ ?_
      · simpa only [Fin.range_cons, Matrix.range_empty, Set.mem_insert_iff,
          Set.mem_empty_iff_false, or_false, not_or] using
          (show (F.splitA i).val ≠ (p.getVert 1).val ∧ (F.splitA i).val ≠ (p.getVert 2).val ∧ (F.splitA i).val ≠ (p.getVert 3).val ∧ (F.splitA i).val ≠ (F.splitB j).val ∧ (F.splitA i).val ≠ (F.center 1).val from
            ⟨(Ne.symm (h1N (F.splitA i))), (Ne.symm (h2N (F.splitA i))), (Ne.symm (h3N (F.splitA i))), (hcross i j), (Ne.symm (hca 1 i))⟩)
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
      all_goals first | exact (p.getVert _).property | exact (F.splitA i).property.ne.symm | exact (F.splitB j).property.ne.symm | exact (F.center 1).property.ne.symm
    exact rooted_five_path_same_color_false hr v c t ht htv (F.splitA i).property
      (F.center 1).property h01 h12 h23 hj hjE.2.2.1.symm 1 3 (by decide) (hc1.trans hc3.symm)
  exact ⟨F.mem_residualPool_iff.mpr ⟨h2O, rA, rB, rX, rY⟩,
    F.mem_residualPool_iff.mpr ⟨h3O, mA, mB, mX, mY⟩,
    F.mem_residualPool_iff.mpr ⟨h4O, sA, sB, sX, sY⟩⟩

end TaskH.Seven
#print axioms TaskH.Seven.DegreeTwelveFrame.six_path_internal_outside
#print axioms TaskH.Seven.DegreeTwelveFrame.six_path_three_middle_residual
