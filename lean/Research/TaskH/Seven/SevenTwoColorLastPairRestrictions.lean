import Research.TaskH.Seven.SevenTwoColorPathSystems

/-! The last pair-colored point s_i is outside A,X,Y. A uses actual
shortestness, while X/Y use actual displayed five-edge neighbor paths. -/

set_option autoImplicit false
universe u
namespace TaskH.Seven
open SimpleGraph
open scoped Classical
variable {V : Type u} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem seven_fin_five_avoid_two (i j : Fin 5) : ∃ l : Fin 5, l ≠ i ∧ l ≠ j := by
  classical
  by_contra! hh
  have hs : (Finset.univ : Finset (Fin 5)) ⊆ {i, j} := by
    intro l _
    by_cases hli : l = i
    · exact Finset.mem_insert.mpr (Or.inl hli)
    · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr (hh l hli)))
  have hc := Finset.card_le_card hs
  have hc' := (Finset.card_le_two : ({i, j} : Finset (Fin 5)).card ≤ 2)
  norm_num only [Finset.card_univ, Fintype.card_fin] at hc
  omega

theorem SevenPathSystem.last_pair_restrictions (hr : RainbowSevenCycles G) {v : V}
    {c : (G.induce {x | x ≠ v}).Coloring (Fin 7)}
    {F : DegreeTwelveFrame G v c} (P : SevenPathSystem F) (hF : F.IsPureSplit) (i : ↥P.indices) :
    ((P.paths i).getVert 5).val ∉ F.centerPool 0 ∧
      ((P.paths i).getVert 5).val ∉ F.splitPoolA ∧
      ((P.paths i).getVert 5).val ∉ F.splitPoolB := by
  have hdec :
      (inferInstance : DecidableRel G.Adj) =
        (fun a b => Classical.propDecidable (G.Adj a b)) := by
    funext a b
    exact Subsingleton.elim _ _
  cases hdec
  classical
  let p := P.paths i
  have hl : p.length = 7 := P.path_length i
  have h5O := P.internal_outside i 5 (by decide) (by decide)
  have h6O := P.internal_outside i 6 (by decide) (by decide)
  have h5N := rootOutside_ne_neighbor h5O
  have h6N := rootOutside_ne_neighbor h6O
  have h56ne : (p.getVert 5).val ≠ (p.getVert 6).val := by
    intro he
    have hn := (P.path_isPath i).getVert_injOn (by change 5 ≤ p.length; omega)
      (by change 6 ≤ p.length; omega) (Subtype.ext he)
    omega
  have h56 : G.Adj (p.getVert 5).val (p.getVert 6).val := p.adj_getVert_succ (i := 5) (by omega)
  have hend : p.getVert 7 = F.splitBD i.val := by simpa only [hl] using p.getVert_length
  have h67 : G.Adj (p.getVert 6).val (F.splitB i.val).val := by
    have he := p.adj_getVert_succ (i := 6) (by omega)
    rw [hend] at he
    change G.Adj (p.getVert 6).val (F.splitB i.val).val at he
    exact he
  have hc5 : c (p.getVert 5) = (F.pairIndex i.val).val := P.odd_color i 5 (by decide) (by decide)
  have hi := F.splitAB_adjacencies i.val (hF i.val)
  have hca := F.center_splitA_ne
  have hcb := F.center_splitB_ne
  have hcross := F.splitA_splitB_ne
  have hA : (p.getVert 5).val ∉ F.centerPool 0 := by
    intro hm
    have hedge := (Finset.mem_filter.mp hm).2
    have hb : (F.pairIndex i.val).val ≠ c (F.centerD 0) := by
      change (F.pairIndex i.val).val ≠ neighborColor v c (F.center 0)
      rw [F.center_color]
      exact F.pairColor_ne_singleton i.val 0
    have hn := twoColor_shortest_neighbor_at_start p c (F.pairIndex i.val).val hb
      (P.path_follows i) (P.path_minimal i) 5 (by omega) hc5 hedge
    omega
  have hX : (p.getVert 5).val ∉ F.splitPoolA := by
    intro hm
    obtain ⟨j, hj⟩ := (Finset.mem_filter.mp hm).2
    obtain ⟨l, hli⟩ : ∃ l : Fin 5, l ≠ i.val := exists_ne i.val
    have hlE := F.splitAB_adjacencies l (hF l)
    have hBil := F.splitB_injective.ne (Ne.symm hli)
    let t : Fin 6 → V := ![(F.splitA j).val, (p.getVert 5).val,
      (p.getVert 6).val, (F.splitB i.val).val, (F.center 1).val, (F.splitB l).val]
    have ht : Function.Injective t := by
      change Function.Injective ![(F.splitA j).val, (p.getVert 5).val, (p.getVert 6).val, (F.splitB i.val).val, (F.center 1).val, (F.splitB l).val]
      unfold Matrix.vecCons
      refine Fin.cons_injective_of_injective ?_ ?_
      · simpa only [Fin.range_cons, Matrix.range_empty, Set.mem_insert_iff,
          Set.mem_empty_iff_false, or_false, not_or] using
          (show (F.splitA j).val ≠ (p.getVert 5).val ∧ (F.splitA j).val ≠ (p.getVert 6).val ∧ (F.splitA j).val ≠ (F.splitB i.val).val ∧ (F.splitA j).val ≠ (F.center 1).val ∧ (F.splitA j).val ≠ (F.splitB l).val from
            ⟨(Ne.symm (h5N (F.splitA j))), (Ne.symm (h6N (F.splitA j))), (hcross j i.val), (Ne.symm (hca 1 j)), (hcross j l)⟩)
      refine Fin.cons_injective_of_injective ?_ ?_
      · simpa only [Fin.range_cons, Matrix.range_empty, Set.mem_insert_iff,
          Set.mem_empty_iff_false, or_false, not_or] using
          (show (p.getVert 5).val ≠ (p.getVert 6).val ∧ (p.getVert 5).val ≠ (F.splitB i.val).val ∧ (p.getVert 5).val ≠ (F.center 1).val ∧ (p.getVert 5).val ≠ (F.splitB l).val from
            ⟨(h56ne), (h5N (F.splitB i.val)), (h5N (F.center 1)), (h5N (F.splitB l))⟩)
      refine Fin.cons_injective_of_injective ?_ ?_
      · simpa only [Fin.range_cons, Matrix.range_empty, Set.mem_insert_iff,
          Set.mem_empty_iff_false, or_false, not_or] using
          (show (p.getVert 6).val ≠ (F.splitB i.val).val ∧ (p.getVert 6).val ≠ (F.center 1).val ∧ (p.getVert 6).val ≠ (F.splitB l).val from
            ⟨(h6N (F.splitB i.val)), (h6N (F.center 1)), (h6N (F.splitB l))⟩)
      refine Fin.cons_injective_of_injective ?_ ?_
      · simpa only [Fin.range_cons, Matrix.range_empty, Set.mem_insert_iff,
          Set.mem_empty_iff_false, or_false, not_or] using
          (show (F.splitB i.val).val ≠ (F.center 1).val ∧ (F.splitB i.val).val ≠ (F.splitB l).val from
            ⟨(Ne.symm (hcb 1 i.val)), (hBil)⟩)
      exact injective_pair_iff_ne.mpr (hcb 1 l)
    have htv : ∀ a : Fin 6, t a ≠ v := by
      intro a
      fin_cases a
      all_goals first | exact (p.getVert _).property | exact (F.splitA j).property.ne.symm | exact (F.splitB i.val).property.ne.symm | exact (F.center 1).property.ne.symm | exact (F.splitB l).property.ne.symm
    exact rooted_five_path_same_color_false hr v c t ht htv (F.splitA j).property
      (F.splitB l).property hj.symm h56 h67 hi.2.2.1.symm hlE.2.2.1 1 3 (by decide)
      (hc5.trans (F.splitB_color i.val).symm)
  have hY : (p.getVert 5).val ∉ F.splitPoolB := by
    intro hm
    obtain ⟨j, hj⟩ := (Finset.mem_filter.mp hm).2
    have hji : j ≠ i.val := by
      intro he
      subst j
      change (G.induce {x | x ≠ v}).Adj (p.getVert 5) (F.splitBD i.val) at hj
      exact (c.valid hj) (hc5.trans (F.splitB_color i.val).symm)
    obtain ⟨l, hli, hlj⟩ := seven_fin_five_avoid_two i.val j
    have hlE := F.splitAB_adjacencies l (hF l)
    have hBji := F.splitB_injective.ne hji
    have hBjl := F.splitB_injective.ne (Ne.symm hlj)
    have hBil := F.splitB_injective.ne (Ne.symm hli)
    let t : Fin 6 → V := ![(F.splitB j).val, (p.getVert 5).val,
      (p.getVert 6).val, (F.splitB i.val).val, (F.center 1).val, (F.splitB l).val]
    have ht : Function.Injective t := by
      change Function.Injective ![(F.splitB j).val, (p.getVert 5).val, (p.getVert 6).val, (F.splitB i.val).val, (F.center 1).val, (F.splitB l).val]
      unfold Matrix.vecCons
      refine Fin.cons_injective_of_injective ?_ ?_
      · simpa only [Fin.range_cons, Matrix.range_empty, Set.mem_insert_iff,
          Set.mem_empty_iff_false, or_false, not_or] using
          (show (F.splitB j).val ≠ (p.getVert 5).val ∧ (F.splitB j).val ≠ (p.getVert 6).val ∧ (F.splitB j).val ≠ (F.splitB i.val).val ∧ (F.splitB j).val ≠ (F.center 1).val ∧ (F.splitB j).val ≠ (F.splitB l).val from
            ⟨(Ne.symm (h5N (F.splitB j))), (Ne.symm (h6N (F.splitB j))), (hBji), (Ne.symm (hcb 1 j)), (hBjl)⟩)
      refine Fin.cons_injective_of_injective ?_ ?_
      · simpa only [Fin.range_cons, Matrix.range_empty, Set.mem_insert_iff,
          Set.mem_empty_iff_false, or_false, not_or] using
          (show (p.getVert 5).val ≠ (p.getVert 6).val ∧ (p.getVert 5).val ≠ (F.splitB i.val).val ∧ (p.getVert 5).val ≠ (F.center 1).val ∧ (p.getVert 5).val ≠ (F.splitB l).val from
            ⟨(h56ne), (h5N (F.splitB i.val)), (h5N (F.center 1)), (h5N (F.splitB l))⟩)
      refine Fin.cons_injective_of_injective ?_ ?_
      · simpa only [Fin.range_cons, Matrix.range_empty, Set.mem_insert_iff,
          Set.mem_empty_iff_false, or_false, not_or] using
          (show (p.getVert 6).val ≠ (F.splitB i.val).val ∧ (p.getVert 6).val ≠ (F.center 1).val ∧ (p.getVert 6).val ≠ (F.splitB l).val from
            ⟨(h6N (F.splitB i.val)), (h6N (F.center 1)), (h6N (F.splitB l))⟩)
      refine Fin.cons_injective_of_injective ?_ ?_
      · simpa only [Fin.range_cons, Matrix.range_empty, Set.mem_insert_iff,
          Set.mem_empty_iff_false, or_false, not_or] using
          (show (F.splitB i.val).val ≠ (F.center 1).val ∧ (F.splitB i.val).val ≠ (F.splitB l).val from
            ⟨(Ne.symm (hcb 1 i.val)), (hBil)⟩)
      exact injective_pair_iff_ne.mpr (hcb 1 l)
    have htv : ∀ a : Fin 6, t a ≠ v := by
      intro a
      fin_cases a
      all_goals first | exact (p.getVert _).property | exact (F.splitB j).property.ne.symm | exact (F.splitB i.val).property.ne.symm | exact (F.center 1).property.ne.symm | exact (F.splitB l).property.ne.symm
    exact rooted_five_path_same_color_false hr v c t ht htv (F.splitB j).property
      (F.splitB l).property hj.symm h56 h67 hi.2.2.1.symm hlE.2.2.1 1 3 (by decide)
      (hc5.trans (F.splitB_color i.val).symm)
  exact ⟨hA, hX, hY⟩

end TaskH.Seven
#print axioms TaskH.Seven.seven_fin_five_avoid_two
#print axioms TaskH.Seven.SevenPathSystem.last_pair_restrictions
