import Research.TaskH.Seven.SevenCommonSplitOutside

/-! Common-representative outside color constraints use the actual path
r_i-z-r_j-a-r_k-b. In the all-common case no color remains. -/

set_option autoImplicit false
universe u
namespace TaskH.Seven
open SimpleGraph
open scoped Classical
variable {V : Type u} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem common_representative_outside_color_constraints
    (hr : RainbowSevenCycles G) {v : V}
    {c : (G.induce {x | x ≠ v}).Coloring (Fin 7)}
    (F : DegreeTwelveFrame G v c) (r : Fin 5 → G.neighborSet v)
    (hrcolor : ∀ i, neighborColor v c (r i) = (F.pairIndex i).val)
    (hra : ∀ i, G.Adj (F.center 0).val (r i).val)
    (hrb : ∀ i, G.Adj (F.center 1).val (r i).val)
    (z : {x : V // x ≠ v}) (hz : z.val ∉ insert v (G.neighborFinset v))
    (i j k : Fin 5) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hzi : G.Adj z.val (r i).val) (hzj : G.Adj z.val (r j).val) :
    c z ≠ (F.singletonIndex 0).val ∧ c z ≠ (F.singletonIndex 1).val ∧
      c z ≠ (F.pairIndex i).val ∧ c z ≠ (F.pairIndex j).val ∧
      c z ≠ (F.pairIndex k).val := by
  have hrinj : Function.Injective (fun l => (r l).val) := by
    intro l m he
    apply F.pairIndex.injective
    apply Subtype.ext
    have hh := congrArg (neighborColor v c) (Subtype.ext he)
    simpa only [hrcolor] using hh
  have hrc : ∀ l : Fin 5, ∀ d : Fin 2, (r l).val ≠ (F.center d).val := by
    intro l d he
    have hh := congrArg (neighborColor v c) (Subtype.ext he)
    rw [hrcolor, F.center_color] at hh
    exact (Finset.mem_compl.mp (F.pairIndex l).property)
      (hh.symm ▸ (F.singletonIndex d).property)
  have hzn : ∀ w : G.neighborSet v, z.val ≠ w.val := by
    intro w he
    apply hz
    exact Finset.mem_insert.mpr (Or.inr ((G.mem_neighborFinset v z.val).mpr
      (by rw [he]; exact w.property)))
  have hab := F.center_center_ne (by decide : (0 : Fin 2) ≠ 1)
  have hrij := hrinj.ne hij
  have hrik := hrinj.ne hik
  have hrjk := hrinj.ne hjk
  have hria := hrc i 0
  have hrib := hrc i 1
  have hrja := hrc j 0
  have hrjb := hrc j 1
  have hrka := hrc k 0
  have hrkb := hrc k 1
  have hzri := hzn (r i)
  have hzrj := hzn (r j)
  have hzrk := hzn (r k)
  have hza := hzn (F.center 0)
  have hzb := hzn (F.center 1)
  let t : Fin 6 → V := ![(r i).val, z.val, (r j).val,
    (F.center 0).val, (r k).val, (F.center 1).val]
  have ht : Function.Injective t := by
    change Function.Injective ![(r i).val, z.val, (r j).val,
      (F.center 0).val, (r k).val, (F.center 1).val]
    unfold Matrix.vecCons
    refine Fin.cons_injective_of_injective ?_ ?_
    · simpa only [Fin.range_cons, Matrix.range_empty, Set.mem_insert_iff,
        Set.mem_empty_iff_false, or_false, not_or] using
        (show (r i).val ≠ z.val ∧ (r i).val ≠ (r j).val ∧
          (r i).val ≠ (F.center 0).val ∧ (r i).val ≠ (r k).val ∧
          (r i).val ≠ (F.center 1).val from
          ⟨Ne.symm hzri, hrij, hria, hrik, hrib⟩)
    refine Fin.cons_injective_of_injective ?_ ?_
    · simpa only [Fin.range_cons, Matrix.range_empty, Set.mem_insert_iff,
        Set.mem_empty_iff_false, or_false, not_or] using
        (show z.val ≠ (r j).val ∧ z.val ≠ (F.center 0).val ∧
          z.val ≠ (r k).val ∧ z.val ≠ (F.center 1).val from
          ⟨hzrj, hza, hzrk, hzb⟩)
    refine Fin.cons_injective_of_injective ?_ ?_
    · simpa only [Fin.range_cons, Matrix.range_empty, Set.mem_insert_iff,
        Set.mem_empty_iff_false, or_false, not_or] using
        (show (r j).val ≠ (F.center 0).val ∧ (r j).val ≠ (r k).val ∧
          (r j).val ≠ (F.center 1).val from ⟨hrja, hrjk, hrjb⟩)
    refine Fin.cons_injective_of_injective ?_ ?_
    · simpa only [Fin.range_cons, Matrix.range_empty, Set.mem_insert_iff,
        Set.mem_empty_iff_false, or_false, not_or] using
        (show (F.center 0).val ≠ (r k).val ∧
          (F.center 0).val ≠ (F.center 1).val from ⟨Ne.symm hrka, hab⟩)
    exact injective_pair_iff_ne.mpr hrkb
  have htv : ∀ l : Fin 6, t l ≠ v := by
    intro l
    fin_cases l
    · exact (r i).property.ne.symm
    · exact z.property
    · exact (r j).property.ne.symm
    · exact (F.center 0).property.ne.symm
    · exact (r k).property.ne.symm
    · exact (F.center 1).property.ne.symm
  have hinj := rooted_five_path_colors_injective hr v c t ht htv
    (r i).property (F.center 1).property hzi.symm hzj (hra j).symm (hra k) (hrb k).symm
  let col : Fin 6 → Fin 7 := fun l => c ⟨t l, htv l⟩
  have h0 : col 0 = (F.pairIndex i).val := hrcolor i
  have h1 : col 1 = c z := rfl
  have h2 : col 2 = (F.pairIndex j).val := hrcolor j
  have h3 : col 3 = (F.singletonIndex 0).val := F.center_color 0
  have h4 : col 4 = (F.pairIndex k).val := hrcolor k
  have h5 : col 5 = (F.singletonIndex 1).val := F.center_color 1
  have hn : ∀ l : Fin 6, l ≠ 1 → col 1 ≠ col l := by
    intro l hl he
    exact hl (hinj he).symm
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simpa only [h1, h3] using hn 3 (by decide)
  · simpa only [h1, h5] using hn 5 (by decide)
  · simpa only [h1, h0] using hn 0 (by decide)
  · simpa only [h1, h2] using hn 2 (by decide)
  · simpa only [h1, h4] using hn 4 (by decide)

theorem all_common_representatives_outside_at_most_one
    (hr : RainbowSevenCycles G) {v : V}
    {c : (G.induce {x | x ≠ v}).Coloring (Fin 7)}
    (F : DegreeTwelveFrame G v c) (r : Fin 5 → G.neighborSet v)
    (hrcolor : ∀ i, neighborColor v c (r i) = (F.pairIndex i).val)
    (hra : ∀ i, G.Adj (F.center 0).val (r i).val)
    (hrb : ∀ i, G.Adj (F.center 1).val (r i).val)
    (z : {x : V // x ≠ v}) (hz : z.val ∉ insert v (G.neighborFinset v)) :
    ((Finset.univ : Finset (Fin 5)).filter (fun i => G.Adj z.val (r i).val)).card ≤ 1 := by
  classical
  apply Finset.card_le_one.mpr
  intro i hi j hj
  by_contra hij
  have hzi := (Finset.mem_filter.mp hi).2
  have hzj := (Finset.mem_filter.mp hj).2
  obtain ⟨k, hki, hkj⟩ : ∃ k : Fin 5, k ≠ i ∧ k ≠ j := by
    by_contra! hh
    have hs : (Finset.univ : Finset (Fin 5)) ⊆ {i, j} := by
      intro k _hk
      by_cases hki : k = i
      · exact Finset.mem_insert.mpr (Or.inl hki)
      · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr (hh k hki)))
    have hc := Finset.card_le_card hs
    have hp : ({i, j} : Finset (Fin 5)).card ≤ 2 := Finset.card_le_two
    have hc' : 5 ≤ ({i, j} : Finset (Fin 5)).card := by
      simpa only [Finset.card_univ, Fintype.card_fin] using hc
    omega
  have C := common_representative_outside_color_constraints hr F r hrcolor hra hrb z hz
    i j k hij (Ne.symm hki) (Ne.symm hkj) hzi hzj
  have hn : ∀ l : Fin 5, c z ≠ (F.pairIndex l).val := by
    intro l
    by_cases hli : l = i
    · simpa only [hli] using C.2.2.1
    · by_cases hlj : l = j
      · simpa only [hlj] using C.2.2.2.1
      · exact (common_representative_outside_color_constraints hr F r hrcolor hra hrb z hz
          i j l hij (Ne.symm hli) (Ne.symm hlj) hzi hzj).2.2.2.2
  rcases F.color_cases (c z) with ⟨d, hd⟩ | ⟨l, hl⟩
  · fin_cases d
    · exact C.1 hd.symm
    · exact C.2.1 hd.symm
  · exact hn l hl.symm

end TaskH.Seven
#print axioms TaskH.Seven.common_representative_outside_color_constraints
#print axioms TaskH.Seven.all_common_representatives_outside_at_most_one
