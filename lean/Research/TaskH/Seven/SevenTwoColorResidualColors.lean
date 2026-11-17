import Research.TaskH.Seven.SevenTwoColorLastPairRestrictions

/-! Original residual-color incidences. The same-middle argument retains
z=s_i: a B-neighbor is first forced to equal s_i, then a genuinely different
index is selected from the actual >=4-label family to avoid that equality. -/

set_option autoImplicit false
universe u
namespace TaskH.Seven
open SimpleGraph Challenge
open scoped Classical
variable {V : Type u} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable def DegreeTwelveFrame.residualColorClass {v : V}
    {c : (G.induce {x | x ≠ v}).Coloring (Fin 7)}
    (F : DegreeTwelveFrame G v c) (k : Fin 7) : Finset {x : V // x ≠ v} :=
  Finset.univ.filter (fun z => z.val ∈ F.residualPool ∧ c z = k)

theorem DegreeTwelveFrame.residual_neighbor_outside {v m z : V}
    {c : (G.induce {x | x ≠ v}).Coloring (Fin 7)}
    (F : DegreeTwelveFrame G v c) (hm : m ∈ F.residualPool) (hmz : G.Adj m z) :
    z ∈ rootOutside G v := by
  have hdec :
      (inferInstance : DecidableRel G.Adj) =
        (fun a b => Classical.propDecidable (G.Adj a b)) := by
    funext a b
    exact Subsingleton.elim _ _
  cases hdec
  classical
  have hmO := (F.mem_residualPool_iff.mp hm).1
  apply Finset.mem_compl.mpr
  intro hzin
  rcases Finset.mem_insert.mp hzin with he | he
  · subst z
    exact (Finset.mem_compl.mp hmO) (Finset.mem_insert.mpr (Or.inr
      ((G.mem_neighborFinset v m).mpr hmz.symm)))
  · exact F.residualPool_no_root_neighbor hm ⟨z, (G.mem_neighborFinset v z).mp he⟩ hmz

theorem SevenPathSystem.middle_mem_alpha (hr : RainbowSevenCycles G) {v : V}
    {c : (G.induce {x | x ≠ v}).Coloring (Fin 7)}
    {F : DegreeTwelveFrame G v c} (P : SevenPathSystem F) (hF : F.IsPureSplit) (i : ↥P.indices) :
    (P.paths i).getVert 4 ∈ F.residualColorClass (F.singletonIndex 0).val := by
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (P.middle_residual hr hF i).2,
    P.even_color i 4 (by decide) (by decide)⟩

theorem SevenPathSystem.middle_neighbor_constraints (hr : RainbowSevenCycles G) {v : V}
    {c : (G.induce {x | x ≠ v}).Coloring (Fin 7)}
    {F : DegreeTwelveFrame G v c} (P : SevenPathSystem F) (hF : F.IsPureSplit)
    (i : ↥P.indices) (z : V) (hmz : G.Adj ((P.paths i).getVert 4).val z) :
    z ∉ F.centerPool 0 ∧ z ∉ F.splitPoolA ∧
      (∀ j : Fin 5, G.Adj z (F.splitB j).val → i.val = j) ∧
      (z ∈ F.centerPool 1 → z = ((P.paths i).getVert 5).val) := by
  have hdec :
      (inferInstance : DecidableRel G.Adj) =
        (fun a b => Classical.propDecidable (G.Adj a b)) := by
    funext a b
    exact Subsingleton.elim _ _
  cases hdec
  classical
  let p := P.paths i
  have hl : p.length = 7 := P.path_length i
  have hmR := (P.middle_residual hr hF i).2
  have hzO := F.residual_neighbor_outside hmR hmz
  have hzN := rootOutside_ne_neighbor hzO
  have h4O := P.internal_outside i 4 (by decide) (by decide)
  have h5O := P.internal_outside i 5 (by decide) (by decide)
  have h6O := P.internal_outside i 6 (by decide) (by decide)
  have h4N := rootOutside_ne_neighbor h4O
  have h5N := rootOutside_ne_neighbor h5O
  have h6N := rootOutside_ne_neighbor h6O
  have hposne (n m : ℕ) (hn : n ≤ p.length) (hm : m ≤ p.length) (hne : n ≠ m) :
      (p.getVert n).val ≠ (p.getVert m).val := by
    intro he
    exact hne ((P.path_isPath i).getVert_injOn hn hm (Subtype.ext he))
  have h45ne := hposne 4 5 (by omega) (by omega) (by decide)
  have h46ne := hposne 4 6 (by omega) (by omega) (by decide)
  have h56ne := hposne 5 6 (by omega) (by omega) (by decide)
  have hc4 : c (p.getVert 4) = (F.singletonIndex 0).val := P.even_color i 4 (by decide) (by decide)
  have hc6 : c (p.getVert 6) = (F.singletonIndex 0).val := P.even_color i 6 (by decide) (by decide)
  have h45 : G.Adj (p.getVert 4).val (p.getVert 5).val := p.adj_getVert_succ (i := 4) (by omega)
  have h56 : G.Adj (p.getVert 5).val (p.getVert 6).val := p.adj_getVert_succ (i := 5) (by omega)
  have hend : p.getVert 7 = F.splitBD i.val := by simpa only [hl] using p.getVert_length
  have h67 : G.Adj (p.getVert 6).val (F.splitB i.val).val := by
    have he := p.adj_getVert_succ (i := 6) (by omega)
    rw [hend] at he
    change G.Adj (p.getVert 6).val (F.splitB i.val).val at he
    exact he
  obtain ⟨hsA, hsX, hsY⟩ := P.last_pair_restrictions hr hF i
  have hcb := F.center_splitB_ne
  have hcross := F.splitA_splitB_ne
  have hmzne := hmz.ne
  have hz6 : z ≠ (p.getVert 6).val := by
    intro he
    have hedge : (G.induce {x | x ≠ v}).Adj (p.getVert 4) (p.getVert 6) := by
      change G.Adj (p.getVert 4).val (p.getVert 6).val
      simpa only [he] using hmz
    exact (c.valid hedge) (hc4.trans hc6.symm)
  have hA : z ∉ F.centerPool 0 := by
    intro hzA
    have haz := (Finset.mem_filter.mp hzA).2
    have hz5 : z ≠ (p.getVert 5).val := by
      intro he
      rw [he] at hzA
      exact hsA hzA
    let t : Fin 6 → V := ![(F.center 0).val, z, (p.getVert 4).val,
      (p.getVert 5).val, (p.getVert 6).val, (F.splitB i.val).val]
    have ht : Function.Injective t := by
      change Function.Injective ![(F.center 0).val, z, (p.getVert 4).val, (p.getVert 5).val, (p.getVert 6).val, (F.splitB i.val).val]
      unfold Matrix.vecCons
      refine Fin.cons_injective_of_injective ?_ ?_
      · simpa only [Fin.range_cons, Matrix.range_empty, Set.mem_insert_iff,
          Set.mem_empty_iff_false, or_false, not_or] using
          (show (F.center 0).val ≠ z ∧ (F.center 0).val ≠ (p.getVert 4).val ∧ (F.center 0).val ≠ (p.getVert 5).val ∧ (F.center 0).val ≠ (p.getVert 6).val ∧ (F.center 0).val ≠ (F.splitB i.val).val from
            ⟨(Ne.symm (hzN (F.center 0))), (Ne.symm (h4N (F.center 0))), (Ne.symm (h5N (F.center 0))), (Ne.symm (h6N (F.center 0))), (hcb 0 i.val)⟩)
      refine Fin.cons_injective_of_injective ?_ ?_
      · simpa only [Fin.range_cons, Matrix.range_empty, Set.mem_insert_iff,
          Set.mem_empty_iff_false, or_false, not_or] using
          (show z ≠ (p.getVert 4).val ∧ z ≠ (p.getVert 5).val ∧ z ≠ (p.getVert 6).val ∧ z ≠ (F.splitB i.val).val from
            ⟨(Ne.symm hmzne), (hz5), (hz6), (hzN (F.splitB i.val))⟩)
      refine Fin.cons_injective_of_injective ?_ ?_
      · simpa only [Fin.range_cons, Matrix.range_empty, Set.mem_insert_iff,
          Set.mem_empty_iff_false, or_false, not_or] using
          (show (p.getVert 4).val ≠ (p.getVert 5).val ∧ (p.getVert 4).val ≠ (p.getVert 6).val ∧ (p.getVert 4).val ≠ (F.splitB i.val).val from
            ⟨(h45ne), (h46ne), (h4N (F.splitB i.val))⟩)
      refine Fin.cons_injective_of_injective ?_ ?_
      · simpa only [Fin.range_cons, Matrix.range_empty, Set.mem_insert_iff,
          Set.mem_empty_iff_false, or_false, not_or] using
          (show (p.getVert 5).val ≠ (p.getVert 6).val ∧ (p.getVert 5).val ≠ (F.splitB i.val).val from
            ⟨(h56ne), (h5N (F.splitB i.val))⟩)
      exact injective_pair_iff_ne.mpr (h6N (F.splitB i.val))
    have htv : ∀ a : Fin 6, t a ≠ v := by
      intro a
      fin_cases a
      all_goals first | exact rootOutside_ne_root hzO | exact (p.getVert _).property | exact (F.center 0).property.ne.symm | exact (F.splitB i.val).property.ne.symm
    exact rooted_five_path_same_color_false hr v c t ht htv (F.center 0).property
      (F.splitB i.val).property haz hmz.symm h45 h56 h67 2 4 (by decide) (hc4.trans hc6.symm)
  have hX : z ∉ F.splitPoolA := by
    intro hzX
    obtain ⟨j, hzj⟩ := (Finset.mem_filter.mp hzX).2
    have hz5 : z ≠ (p.getVert 5).val := by
      intro he
      rw [he] at hzX
      exact hsX hzX
    let t : Fin 6 → V := ![(F.splitA j).val, z, (p.getVert 4).val,
      (p.getVert 5).val, (p.getVert 6).val, (F.splitB i.val).val]
    have ht : Function.Injective t := by
      change Function.Injective ![(F.splitA j).val, z, (p.getVert 4).val, (p.getVert 5).val, (p.getVert 6).val, (F.splitB i.val).val]
      unfold Matrix.vecCons
      refine Fin.cons_injective_of_injective ?_ ?_
      · simpa only [Fin.range_cons, Matrix.range_empty, Set.mem_insert_iff,
          Set.mem_empty_iff_false, or_false, not_or] using
          (show (F.splitA j).val ≠ z ∧ (F.splitA j).val ≠ (p.getVert 4).val ∧ (F.splitA j).val ≠ (p.getVert 5).val ∧ (F.splitA j).val ≠ (p.getVert 6).val ∧ (F.splitA j).val ≠ (F.splitB i.val).val from
            ⟨(Ne.symm (hzN (F.splitA j))), (Ne.symm (h4N (F.splitA j))), (Ne.symm (h5N (F.splitA j))), (Ne.symm (h6N (F.splitA j))), (hcross j i.val)⟩)
      refine Fin.cons_injective_of_injective ?_ ?_
      · simpa only [Fin.range_cons, Matrix.range_empty, Set.mem_insert_iff,
          Set.mem_empty_iff_false, or_false, not_or] using
          (show z ≠ (p.getVert 4).val ∧ z ≠ (p.getVert 5).val ∧ z ≠ (p.getVert 6).val ∧ z ≠ (F.splitB i.val).val from
            ⟨(Ne.symm hmzne), (hz5), (hz6), (hzN (F.splitB i.val))⟩)
      refine Fin.cons_injective_of_injective ?_ ?_
      · simpa only [Fin.range_cons, Matrix.range_empty, Set.mem_insert_iff,
          Set.mem_empty_iff_false, or_false, not_or] using
          (show (p.getVert 4).val ≠ (p.getVert 5).val ∧ (p.getVert 4).val ≠ (p.getVert 6).val ∧ (p.getVert 4).val ≠ (F.splitB i.val).val from
            ⟨(h45ne), (h46ne), (h4N (F.splitB i.val))⟩)
      refine Fin.cons_injective_of_injective ?_ ?_
      · simpa only [Fin.range_cons, Matrix.range_empty, Set.mem_insert_iff,
          Set.mem_empty_iff_false, or_false, not_or] using
          (show (p.getVert 5).val ≠ (p.getVert 6).val ∧ (p.getVert 5).val ≠ (F.splitB i.val).val from
            ⟨(h56ne), (h5N (F.splitB i.val))⟩)
      exact injective_pair_iff_ne.mpr (h6N (F.splitB i.val))
    have htv : ∀ a : Fin 6, t a ≠ v := by
      intro a
      fin_cases a
      all_goals first | exact rootOutside_ne_root hzO | exact (p.getVert _).property | exact (F.splitA j).property.ne.symm | exact (F.splitB i.val).property.ne.symm
    exact rooted_five_path_same_color_false hr v c t ht htv (F.splitA j).property
      (F.splitB i.val).property hzj.symm hmz.symm h45 h56 h67 2 4 (by decide) (hc4.trans hc6.symm)
  have hY : ∀ j : Fin 5, G.Adj z (F.splitB j).val → i.val = j := by
    intro j hzj
    by_contra hij
    have hz5 : z ≠ (p.getVert 5).val := by
      intro he
      apply hsY
      rw [he] at hzj
      exact Finset.mem_filter.mpr ⟨h5O, j, hzj⟩
    have hBij := F.splitB_injective.ne hij
    let t : Fin 6 → V := ![(F.splitB j).val, z, (p.getVert 4).val,
      (p.getVert 5).val, (p.getVert 6).val, (F.splitB i.val).val]
    have ht : Function.Injective t := by
      change Function.Injective ![(F.splitB j).val, z, (p.getVert 4).val, (p.getVert 5).val, (p.getVert 6).val, (F.splitB i.val).val]
      unfold Matrix.vecCons
      refine Fin.cons_injective_of_injective ?_ ?_
      · simpa only [Fin.range_cons, Matrix.range_empty, Set.mem_insert_iff,
          Set.mem_empty_iff_false, or_false, not_or] using
          (show (F.splitB j).val ≠ z ∧ (F.splitB j).val ≠ (p.getVert 4).val ∧ (F.splitB j).val ≠ (p.getVert 5).val ∧ (F.splitB j).val ≠ (p.getVert 6).val ∧ (F.splitB j).val ≠ (F.splitB i.val).val from
            ⟨(Ne.symm (hzN (F.splitB j))), (Ne.symm (h4N (F.splitB j))), (Ne.symm (h5N (F.splitB j))), (Ne.symm (h6N (F.splitB j))), (Ne.symm hBij)⟩)
      refine Fin.cons_injective_of_injective ?_ ?_
      · simpa only [Fin.range_cons, Matrix.range_empty, Set.mem_insert_iff,
          Set.mem_empty_iff_false, or_false, not_or] using
          (show z ≠ (p.getVert 4).val ∧ z ≠ (p.getVert 5).val ∧ z ≠ (p.getVert 6).val ∧ z ≠ (F.splitB i.val).val from
            ⟨(Ne.symm hmzne), (hz5), (hz6), (hzN (F.splitB i.val))⟩)
      refine Fin.cons_injective_of_injective ?_ ?_
      · simpa only [Fin.range_cons, Matrix.range_empty, Set.mem_insert_iff,
          Set.mem_empty_iff_false, or_false, not_or] using
          (show (p.getVert 4).val ≠ (p.getVert 5).val ∧ (p.getVert 4).val ≠ (p.getVert 6).val ∧ (p.getVert 4).val ≠ (F.splitB i.val).val from
            ⟨(h45ne), (h46ne), (h4N (F.splitB i.val))⟩)
      refine Fin.cons_injective_of_injective ?_ ?_
      · simpa only [Fin.range_cons, Matrix.range_empty, Set.mem_insert_iff,
          Set.mem_empty_iff_false, or_false, not_or] using
          (show (p.getVert 5).val ≠ (p.getVert 6).val ∧ (p.getVert 5).val ≠ (F.splitB i.val).val from
            ⟨(h56ne), (h5N (F.splitB i.val))⟩)
      exact injective_pair_iff_ne.mpr (h6N (F.splitB i.val))
    have htv : ∀ a : Fin 6, t a ≠ v := by
      intro a
      fin_cases a
      all_goals first | exact rootOutside_ne_root hzO | exact (p.getVert _).property | exact (F.splitB j).property.ne.symm | exact (F.splitB i.val).property.ne.symm
    exact rooted_five_path_same_color_false hr v c t ht htv (F.splitB j).property
      (F.splitB i.val).property hzj.symm hmz.symm h45 h56 h67 2 4 (by decide) (hc4.trans hc6.symm)
  have hB : z ∈ F.centerPool 1 → z = (p.getVert 5).val := by
    intro hzB
    by_contra hz5
    have hbz := (Finset.mem_filter.mp hzB).2
    let t : Fin 6 → V := ![(F.center 1).val, z, (p.getVert 4).val,
      (p.getVert 5).val, (p.getVert 6).val, (F.splitB i.val).val]
    have ht : Function.Injective t := by
      change Function.Injective ![(F.center 1).val, z, (p.getVert 4).val, (p.getVert 5).val, (p.getVert 6).val, (F.splitB i.val).val]
      unfold Matrix.vecCons
      refine Fin.cons_injective_of_injective ?_ ?_
      · simpa only [Fin.range_cons, Matrix.range_empty, Set.mem_insert_iff,
          Set.mem_empty_iff_false, or_false, not_or] using
          (show (F.center 1).val ≠ z ∧ (F.center 1).val ≠ (p.getVert 4).val ∧ (F.center 1).val ≠ (p.getVert 5).val ∧ (F.center 1).val ≠ (p.getVert 6).val ∧ (F.center 1).val ≠ (F.splitB i.val).val from
            ⟨(Ne.symm (hzN (F.center 1))), (Ne.symm (h4N (F.center 1))), (Ne.symm (h5N (F.center 1))), (Ne.symm (h6N (F.center 1))), (hcb 1 i.val)⟩)
      refine Fin.cons_injective_of_injective ?_ ?_
      · simpa only [Fin.range_cons, Matrix.range_empty, Set.mem_insert_iff,
          Set.mem_empty_iff_false, or_false, not_or] using
          (show z ≠ (p.getVert 4).val ∧ z ≠ (p.getVert 5).val ∧ z ≠ (p.getVert 6).val ∧ z ≠ (F.splitB i.val).val from
            ⟨(Ne.symm hmzne), (hz5), (hz6), (hzN (F.splitB i.val))⟩)
      refine Fin.cons_injective_of_injective ?_ ?_
      · simpa only [Fin.range_cons, Matrix.range_empty, Set.mem_insert_iff,
          Set.mem_empty_iff_false, or_false, not_or] using
          (show (p.getVert 4).val ≠ (p.getVert 5).val ∧ (p.getVert 4).val ≠ (p.getVert 6).val ∧ (p.getVert 4).val ≠ (F.splitB i.val).val from
            ⟨(h45ne), (h46ne), (h4N (F.splitB i.val))⟩)
      refine Fin.cons_injective_of_injective ?_ ?_
      · simpa only [Fin.range_cons, Matrix.range_empty, Set.mem_insert_iff,
          Set.mem_empty_iff_false, or_false, not_or] using
          (show (p.getVert 5).val ≠ (p.getVert 6).val ∧ (p.getVert 5).val ≠ (F.splitB i.val).val from
            ⟨(h56ne), (h5N (F.splitB i.val))⟩)
      exact injective_pair_iff_ne.mpr (h6N (F.splitB i.val))
    have htv : ∀ a : Fin 6, t a ≠ v := by
      intro a
      fin_cases a
      all_goals first | exact rootOutside_ne_root hzO | exact (p.getVert _).property | exact (F.center 1).property.ne.symm | exact (F.splitB i.val).property.ne.symm
    exact rooted_five_path_same_color_false hr v c t ht htv (F.center 1).property
      (F.splitB i.val).property hbz hmz.symm h45 h56 h67 2 4 (by decide) (hc4.trans hc6.symm)
  exact ⟨hA, hX, hY, hB⟩

theorem SevenPathSystem.exists_last_pair_ne {v : V}
    {c : (G.induce {x | x ≠ v}).Coloring (Fin 7)}
    {F : DegreeTwelveFrame G v c} (P : SevenPathSystem F) (z : V) :
    ∃ i : ↥P.indices, z ≠ ((P.paths i).getVert 5).val := by
  classical
  by_contra hno
  have hall : ∀ i : ↥P.indices, z = ((P.paths i).getVert 5).val := by
    intro i
    by_contra hi
    exact hno ⟨i, hi⟩
  obtain ⟨i, hi, j, hj, hij⟩ := Finset.one_lt_card.mp (by
    have hh := P.card_ge_four
    omega : 1 < P.indices.card)
  let ii : ↥P.indices := ⟨i, hi⟩
  let jj : ↥P.indices := ⟨j, hj⟩
  have hs : ((P.paths ii).getVert 5).val = ((P.paths jj).getVert 5).val :=
    (hall ii).symm.trans (hall jj)
  have he := P.odd_position_injective 5 (by decide) (by decide) hs
  exact hij (congrArg Subtype.val he)

theorem SevenPathSystem.unique_middle_neighbors_residual (hr : RainbowSevenCycles G) {v : V}
    {c : (G.induce {x | x ≠ v}).Coloring (Fin 7)}
    {F : DegreeTwelveFrame G v c} (P : SevenPathSystem F) (hF : F.IsPureSplit)
    (huniq : ∀ i j : ↥P.indices, (P.paths i).getVert 4 = (P.paths j).getVert 4)
    (i0 : ↥P.indices) (z : V) (hmz : G.Adj ((P.paths i0).getVert 4).val z) :
    z ∈ F.residualPool := by
  have hmR := (P.middle_residual hr hF i0).2
  have hzO := F.residual_neighbor_outside hmR hmz
  have hcon (i : ↥P.indices) := P.middle_neighbor_constraints hr hF i z (by
    have he := congrArg Subtype.val (huniq i i0)
    rw [he]
    exact hmz)
  have hA : z ∉ F.centerPool 0 := (hcon i0).1
  have hX : z ∉ F.splitPoolA := (hcon i0).2.1
  have hY : z ∉ F.splitPoolB := by
    intro hzY
    obtain ⟨j, hzj⟩ := (Finset.mem_filter.mp hzY).2
    obtain ⟨i, hi, hij⟩ := Finset.exists_mem_ne (by
      have hh := P.card_ge_four
      omega : 1 < P.indices.card) j
    exact hij ((hcon ⟨i, hi⟩).2.2.1 j hzj)
  have hB : z ∉ F.centerPool 1 := by
    intro hzB
    obtain ⟨i, hzi⟩ := P.exists_last_pair_ne z
    exact hzi ((hcon i).2.2.2 hzB)
  exact F.mem_residualPool_iff.mpr ⟨hzO, hA, hB, hX, hY⟩

theorem SevenPathSystem.alpha_residual_card_ge_two
    (hcrit : IsCriticalPlus 7 G) (hc : modCycleCount 7 G = 2880)
    (hnot : ¬ IsCompleteOfOrder G 8) {v : V}
    {c : (G.induce {x | x ≠ v}).Coloring (Fin 7)}
    {F : DegreeTwelveFrame G v c} (P : SevenPathSystem F) (hF : F.IsPureSplit)
    (hsmall : F.residualPool.card ≤ 7) :
    2 ≤ (F.residualColorClass (F.singletonIndex 0).val).card := by
  have hdec :
      (inferInstance : DecidableRel G.Adj) =
        (fun a b => Classical.propDecidable (G.Adj a b)) := by
    funext a b
    exact Subsingleton.elim _ _
  cases hdec
  classical
  by_contra hlt
  have hle : (F.residualColorClass (F.singletonIndex 0).val).card ≤ 1 := by omega
  have hr : RainbowSevenCycles G := equality_rainbowSevenCycles hcrit hc
  have huniq : ∀ i j : ↥P.indices, (P.paths i).getVert 4 = (P.paths j).getVert 4 := by
    intro i j
    exact Finset.card_le_one.mp hle ((P.paths i).getVert 4)
      (P.middle_mem_alpha hr hF i) ((P.paths j).getVert 4) (P.middle_mem_alpha hr hF j)
  obtain ⟨i, hi⟩ := Finset.card_pos.mp (by
    have hh := P.card_ge_four
    omega : 0 < P.indices.card)
  let i0 : ↥P.indices := ⟨i, hi⟩
  have hsub : G.neighborFinset ((P.paths i0).getVert 4).val ⊆ F.residualPool := by
    intro z hz
    exact P.unique_middle_neighbors_residual hr hF huniq i0 z
      ((G.mem_neighborFinset ((P.paths i0).getVert 4).val z).mp hz)
  have hcard := Finset.card_le_card hsub
  rw [G.card_neighborFinset_eq_degree] at hcard
  have hlow := equality_noncomplete_degree_ge_twelve hcrit hc hnot ((P.paths i0).getVert 4).val
  omega

end TaskH.Seven
#print axioms TaskH.Seven.DegreeTwelveFrame.residualColorClass
#print axioms TaskH.Seven.DegreeTwelveFrame.residual_neighbor_outside
#print axioms TaskH.Seven.SevenPathSystem.middle_mem_alpha
#print axioms TaskH.Seven.SevenPathSystem.middle_neighbor_constraints
#print axioms TaskH.Seven.SevenPathSystem.exists_last_pair_ne
#print axioms TaskH.Seven.SevenPathSystem.unique_middle_neighbors_residual
#print axioms TaskH.Seven.SevenPathSystem.alpha_residual_card_ge_two
