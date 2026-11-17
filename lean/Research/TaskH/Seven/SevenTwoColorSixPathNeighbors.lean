import Research.TaskH.Seven.SevenTwoColorSixPathInterior

/-! The actual middle vertex of a six-edge path has its entire original
neighborhood in the actual residual set. Four real boundary-neighbor paths
are displayed; collisions are excluded using the already actual pool
separations. The residual card<=7 remains an explicit INTERNAL input. -/

set_option autoImplicit false
universe u
namespace TaskH.Seven
open SimpleGraph Challenge
open scoped Classical
variable {V : Type u} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem DegreeTwelveFrame.six_path_middle_neighbors_residual
    (hr : RainbowSevenCycles G) {v : V}
    {c : (G.induce {x | x ≠ v}).Coloring (Fin 7)}
    (F : DegreeTwelveFrame G v c) (hF : F.IsPureSplit) (i : Fin 5)
    (p : (G.induce {x | x ≠ v}).Walk (F.splitAD i) (F.splitBD i))
    (hp : p.IsPath)
    (hf : Follows p c (Equiv.swap (c (F.splitAD i)) (F.singletonIndex 0).val))
    (hl : p.length = 6)
    (havoid : ∀ n ≤ p.length, p.getVert n ≠ F.centerD 0)
    (z : V) (hmz : G.Adj (p.getVert 3).val z) : z ∈ F.residualPool := by
  have hdec :
      (inferInstance : DecidableRel G.Adj) =
        (fun a b => Classical.propDecidable (G.Adj a b)) := by
    funext a b
    exact Subsingleton.elim _ _
  cases hdec
  classical
  obtain ⟨hrR, hmR, hsR⟩ := F.six_path_three_middle_residual hr hF i p hp hf hl havoid
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
  have hc3 : c (p.getVert 3) = (F.singletonIndex 0).val := by
    simpa using twoColor_color_at p c (F.singletonIndex 0).val hf 3 (by omega)
  have hc5 : c (p.getVert 5) = (F.singletonIndex 0).val := by
    simpa using twoColor_color_at p c (F.singletonIndex 0).val hf 5 (by omega)
  have h1X : (p.getVert 1).val ∈ F.splitPoolA :=
    Finset.mem_filter.mpr ⟨h1O, i, h01.symm⟩
  have h5Y : (p.getVert 5).val ∈ F.splitPoolB :=
    Finset.mem_filter.mpr ⟨h5O, i, h56⟩
  have hzO : z ∈ rootOutside G v := by
    apply Finset.mem_compl.mpr
    intro hzin
    rcases Finset.mem_insert.mp hzin with he | he
    · subst z
      exact (Finset.mem_compl.mp h3O) (Finset.mem_insert.mpr (Or.inr
        ((G.mem_neighborFinset v (p.getVert 3).val).mpr hmz.symm)))
    · have hvz := (G.mem_neighborFinset v z).mp he
      exact F.residualPool_no_root_neighbor hmR ⟨z, hvz⟩ hmz
  have hzN := rootOutside_ne_neighbor hzO
  have hmzne := hmz.ne
  have zA : z ∉ F.centerPool 0 := by
    intro hzA
    have haz := (Finset.mem_filter.mp hzA).2
    have hz4 : z ≠ (p.getVert 4).val := by
      intro he
      rw [he] at hzA
      exact (F.mem_residualPool_iff.mp hsR).2.1 hzA
    have hz5 : z ≠ (p.getVert 5).val := by
      intro he
      rw [he] at hzA
      exact Finset.disjoint_left.mp (F.pureSplit_centerPool_zero_disjoint_B hr hF) hzA h5Y
    let t : Fin 6 → V := ![(F.center 0).val, z, (p.getVert 3).val,
      (p.getVert 4).val, (p.getVert 5).val, (F.splitB i).val]
    have ht : Function.Injective t := by
      change Function.Injective ![(F.center 0).val, z, (p.getVert 3).val, (p.getVert 4).val, (p.getVert 5).val, (F.splitB i).val]
      unfold Matrix.vecCons
      refine Fin.cons_injective_of_injective ?_ ?_
      · simpa only [Fin.range_cons, Matrix.range_empty, Set.mem_insert_iff,
          Set.mem_empty_iff_false, or_false, not_or] using
          (show (F.center 0).val ≠ z ∧ (F.center 0).val ≠ (p.getVert 3).val ∧ (F.center 0).val ≠ (p.getVert 4).val ∧ (F.center 0).val ≠ (p.getVert 5).val ∧ (F.center 0).val ≠ (F.splitB i).val from
            ⟨(Ne.symm (hzN (F.center 0))), (Ne.symm (h3N (F.center 0))), (Ne.symm (h4N (F.center 0))), (Ne.symm (h5N (F.center 0))), (hcb 0 i)⟩)
      refine Fin.cons_injective_of_injective ?_ ?_
      · simpa only [Fin.range_cons, Matrix.range_empty, Set.mem_insert_iff,
          Set.mem_empty_iff_false, or_false, not_or] using
          (show z ≠ (p.getVert 3).val ∧ z ≠ (p.getVert 4).val ∧ z ≠ (p.getVert 5).val ∧ z ≠ (F.splitB i).val from
            ⟨(Ne.symm hmzne), (hz4), (hz5), (hzN (F.splitB i))⟩)
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
      all_goals first | exact rootOutside_ne_root hzO | exact (p.getVert _).property | exact (F.center 0).property.ne.symm | exact (F.splitB i).property.ne.symm
    exact rooted_five_path_same_color_false hr v c t ht htv (F.center 0).property
      (F.splitB i).property haz hmz.symm h34 h45 h56 2 4 (by decide) (hc3.trans hc5.symm)
  have zB : z ∉ F.centerPool 1 := by
    intro hzB
    have hbz := (Finset.mem_filter.mp hzB).2
    have hz1 : z ≠ (p.getVert 1).val := by
      intro he
      rw [he] at hzB
      exact Finset.disjoint_left.mp (F.pureSplit_centerPool_one_disjoint_A hr hF) hzB h1X
    have hz2 : z ≠ (p.getVert 2).val := by
      intro he
      rw [he] at hzB
      exact (F.mem_residualPool_iff.mp hrR).2.2.1 hzB
    let t : Fin 6 → V := ![(F.splitA i).val, (p.getVert 1).val,
      (p.getVert 2).val, (p.getVert 3).val, z, (F.center 1).val]
    have ht : Function.Injective t := by
      change Function.Injective ![(F.splitA i).val, (p.getVert 1).val, (p.getVert 2).val, (p.getVert 3).val, z, (F.center 1).val]
      unfold Matrix.vecCons
      refine Fin.cons_injective_of_injective ?_ ?_
      · simpa only [Fin.range_cons, Matrix.range_empty, Set.mem_insert_iff,
          Set.mem_empty_iff_false, or_false, not_or] using
          (show (F.splitA i).val ≠ (p.getVert 1).val ∧ (F.splitA i).val ≠ (p.getVert 2).val ∧ (F.splitA i).val ≠ (p.getVert 3).val ∧ (F.splitA i).val ≠ z ∧ (F.splitA i).val ≠ (F.center 1).val from
            ⟨(Ne.symm (h1N (F.splitA i))), (Ne.symm (h2N (F.splitA i))), (Ne.symm (h3N (F.splitA i))), (Ne.symm (hzN (F.splitA i))), (Ne.symm (hca 1 i))⟩)
      refine Fin.cons_injective_of_injective ?_ ?_
      · simpa only [Fin.range_cons, Matrix.range_empty, Set.mem_insert_iff,
          Set.mem_empty_iff_false, or_false, not_or] using
          (show (p.getVert 1).val ≠ (p.getVert 2).val ∧ (p.getVert 1).val ≠ (p.getVert 3).val ∧ (p.getVert 1).val ≠ z ∧ (p.getVert 1).val ≠ (F.center 1).val from
            ⟨(h12n), (h13n), (Ne.symm (hz1)), (h1N (F.center 1))⟩)
      refine Fin.cons_injective_of_injective ?_ ?_
      · simpa only [Fin.range_cons, Matrix.range_empty, Set.mem_insert_iff,
          Set.mem_empty_iff_false, or_false, not_or] using
          (show (p.getVert 2).val ≠ (p.getVert 3).val ∧ (p.getVert 2).val ≠ z ∧ (p.getVert 2).val ≠ (F.center 1).val from
            ⟨(h23n), (Ne.symm (hz2)), (h2N (F.center 1))⟩)
      refine Fin.cons_injective_of_injective ?_ ?_
      · simpa only [Fin.range_cons, Matrix.range_empty, Set.mem_insert_iff,
          Set.mem_empty_iff_false, or_false, not_or] using
          (show (p.getVert 3).val ≠ z ∧ (p.getVert 3).val ≠ (F.center 1).val from
            ⟨(hmzne), (h3N (F.center 1))⟩)
      exact injective_pair_iff_ne.mpr (hzN (F.center 1))
    have htv : ∀ a : Fin 6, t a ≠ v := by
      intro a
      fin_cases a
      all_goals first | exact rootOutside_ne_root hzO | exact (p.getVert _).property | exact (F.center 1).property.ne.symm | exact (F.splitA i).property.ne.symm
    exact rooted_five_path_same_color_false hr v c t ht htv (F.splitA i).property
      (F.center 1).property h01 h12 h23 hmz hbz.symm 1 3 (by decide) (hc1.trans hc3.symm)
  have zX : z ∉ F.splitPoolA := by
    intro hzX
    obtain ⟨j, hzj⟩ := (Finset.mem_filter.mp hzX).2
    have hz4 : z ≠ (p.getVert 4).val := by
      intro he
      rw [he] at hzX
      exact (F.mem_residualPool_iff.mp hsR).2.2.2.1 hzX
    have hz5 : z ≠ (p.getVert 5).val := by
      intro he
      rw [he] at hzX
      exact Finset.disjoint_left.mp (F.pureSplit_splitPools_disjoint hr hF) hzX h5Y
    let t : Fin 6 → V := ![(F.splitA j).val, z, (p.getVert 3).val,
      (p.getVert 4).val, (p.getVert 5).val, (F.splitB i).val]
    have ht : Function.Injective t := by
      change Function.Injective ![(F.splitA j).val, z, (p.getVert 3).val, (p.getVert 4).val, (p.getVert 5).val, (F.splitB i).val]
      unfold Matrix.vecCons
      refine Fin.cons_injective_of_injective ?_ ?_
      · simpa only [Fin.range_cons, Matrix.range_empty, Set.mem_insert_iff,
          Set.mem_empty_iff_false, or_false, not_or] using
          (show (F.splitA j).val ≠ z ∧ (F.splitA j).val ≠ (p.getVert 3).val ∧ (F.splitA j).val ≠ (p.getVert 4).val ∧ (F.splitA j).val ≠ (p.getVert 5).val ∧ (F.splitA j).val ≠ (F.splitB i).val from
            ⟨(Ne.symm (hzN (F.splitA j))), (Ne.symm (h3N (F.splitA j))), (Ne.symm (h4N (F.splitA j))), (Ne.symm (h5N (F.splitA j))), (hcross j i)⟩)
      refine Fin.cons_injective_of_injective ?_ ?_
      · simpa only [Fin.range_cons, Matrix.range_empty, Set.mem_insert_iff,
          Set.mem_empty_iff_false, or_false, not_or] using
          (show z ≠ (p.getVert 3).val ∧ z ≠ (p.getVert 4).val ∧ z ≠ (p.getVert 5).val ∧ z ≠ (F.splitB i).val from
            ⟨(Ne.symm hmzne), (hz4), (hz5), (hzN (F.splitB i))⟩)
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
      all_goals first | exact rootOutside_ne_root hzO | exact (p.getVert _).property | exact (F.splitA j).property.ne.symm | exact (F.splitB i).property.ne.symm
    exact rooted_five_path_same_color_false hr v c t ht htv (F.splitA j).property
      (F.splitB i).property hzj.symm hmz.symm h34 h45 h56 2 4 (by decide) (hc3.trans hc5.symm)
  have zY : z ∉ F.splitPoolB := by
    intro hzY
    obtain ⟨j, hzj⟩ := (Finset.mem_filter.mp hzY).2
    have hz1 : z ≠ (p.getVert 1).val := by
      intro he
      rw [he] at hzY
      exact Finset.disjoint_left.mp (F.pureSplit_splitPools_disjoint hr hF) h1X hzY
    have hz2 : z ≠ (p.getVert 2).val := by
      intro he
      rw [he] at hzY
      exact (F.mem_residualPool_iff.mp hrR).2.2.2.2 hzY
    let t : Fin 6 → V := ![(F.splitA i).val, (p.getVert 1).val,
      (p.getVert 2).val, (p.getVert 3).val, z, (F.splitB j).val]
    have ht : Function.Injective t := by
      change Function.Injective ![(F.splitA i).val, (p.getVert 1).val, (p.getVert 2).val, (p.getVert 3).val, z, (F.splitB j).val]
      unfold Matrix.vecCons
      refine Fin.cons_injective_of_injective ?_ ?_
      · simpa only [Fin.range_cons, Matrix.range_empty, Set.mem_insert_iff,
          Set.mem_empty_iff_false, or_false, not_or] using
          (show (F.splitA i).val ≠ (p.getVert 1).val ∧ (F.splitA i).val ≠ (p.getVert 2).val ∧ (F.splitA i).val ≠ (p.getVert 3).val ∧ (F.splitA i).val ≠ z ∧ (F.splitA i).val ≠ (F.splitB j).val from
            ⟨(Ne.symm (h1N (F.splitA i))), (Ne.symm (h2N (F.splitA i))), (Ne.symm (h3N (F.splitA i))), (Ne.symm (hzN (F.splitA i))), (hcross i j)⟩)
      refine Fin.cons_injective_of_injective ?_ ?_
      · simpa only [Fin.range_cons, Matrix.range_empty, Set.mem_insert_iff,
          Set.mem_empty_iff_false, or_false, not_or] using
          (show (p.getVert 1).val ≠ (p.getVert 2).val ∧ (p.getVert 1).val ≠ (p.getVert 3).val ∧ (p.getVert 1).val ≠ z ∧ (p.getVert 1).val ≠ (F.splitB j).val from
            ⟨(h12n), (h13n), (Ne.symm (hz1)), (h1N (F.splitB j))⟩)
      refine Fin.cons_injective_of_injective ?_ ?_
      · simpa only [Fin.range_cons, Matrix.range_empty, Set.mem_insert_iff,
          Set.mem_empty_iff_false, or_false, not_or] using
          (show (p.getVert 2).val ≠ (p.getVert 3).val ∧ (p.getVert 2).val ≠ z ∧ (p.getVert 2).val ≠ (F.splitB j).val from
            ⟨(h23n), (Ne.symm (hz2)), (h2N (F.splitB j))⟩)
      refine Fin.cons_injective_of_injective ?_ ?_
      · simpa only [Fin.range_cons, Matrix.range_empty, Set.mem_insert_iff,
          Set.mem_empty_iff_false, or_false, not_or] using
          (show (p.getVert 3).val ≠ z ∧ (p.getVert 3).val ≠ (F.splitB j).val from
            ⟨(hmzne), (h3N (F.splitB j))⟩)
      exact injective_pair_iff_ne.mpr (hzN (F.splitB j))
    have htv : ∀ a : Fin 6, t a ≠ v := by
      intro a
      fin_cases a
      all_goals first | exact rootOutside_ne_root hzO | exact (p.getVert _).property | exact (F.splitA i).property.ne.symm | exact (F.splitB j).property.ne.symm
    exact rooted_five_path_same_color_false hr v c t ht htv (F.splitA i).property
      (F.splitB j).property h01 h12 h23 hmz hzj 1 3 (by decide) (hc1.trans hc3.symm)
  exact F.mem_residualPool_iff.mpr ⟨hzO, zA, zB, zX, zY⟩

theorem DegreeTwelveFrame.six_path_false_of_residual_card
    (hr : RainbowSevenCycles G) (hmin : ∀ z : V, 12 ≤ G.degree z) {v : V}
    {c : (G.induce {x | x ≠ v}).Coloring (Fin 7)}
    (F : DegreeTwelveFrame G v c) (hF : F.IsPureSplit)
    (hsmall : F.residualPool.card ≤ 7) (i : Fin 5)
    (p : (G.induce {x | x ≠ v}).Walk (F.splitAD i) (F.splitBD i))
    (hp : p.IsPath)
    (hf : Follows p c (Equiv.swap (c (F.splitAD i)) (F.singletonIndex 0).val))
    (hl : p.length = 6)
    (havoid : ∀ n ≤ p.length, p.getVert n ≠ F.centerD 0) : False := by
  have hsub : G.neighborFinset (p.getVert 3).val ⊆ F.residualPool := by
    intro z hz
    exact F.six_path_middle_neighbors_residual hr hF i p hp hf hl havoid z
      ((G.mem_neighborFinset (p.getVert 3).val z).mp hz)
  have hcard := Finset.card_le_card hsub
  rw [G.card_neighborFinset_eq_degree] at hcard
  have hlow := hmin (p.getVert 3).val
  omega

theorem equality_six_path_false_of_residual_card
    (hcrit : IsCriticalPlus 7 G) (hc : modCycleCount 7 G = 2880)
    (hnot : ¬ IsCompleteOfOrder G 8) {v : V}
    {c : (G.induce {x | x ≠ v}).Coloring (Fin 7)}
    (F : DegreeTwelveFrame G v c) (hF : F.IsPureSplit)
    (hsmall : F.residualPool.card ≤ 7) (i : Fin 5)
    (p : (G.induce {x | x ≠ v}).Walk (F.splitAD i) (F.splitBD i))
    (hp : p.IsPath)
    (hf : Follows p c (Equiv.swap (c (F.splitAD i)) (F.singletonIndex 0).val))
    (hl : p.length = 6)
    (havoid : ∀ n ≤ p.length, p.getVert n ≠ F.centerD 0) : False :=
  F.six_path_false_of_residual_card (equality_rainbowSevenCycles hcrit hc)
    (equality_noncomplete_degree_ge_twelve hcrit hc hnot) hF hsmall i p hp hf hl havoid

end TaskH.Seven
#print axioms TaskH.Seven.DegreeTwelveFrame.six_path_middle_neighbors_residual
#print axioms TaskH.Seven.DegreeTwelveFrame.six_path_false_of_residual_card
#print axioms TaskH.Seven.equality_six_path_false_of_residual_card
