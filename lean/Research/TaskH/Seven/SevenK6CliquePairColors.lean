import Research.TaskH.Seven.SevenK6CliqueOrder

/-!
The actual two-hook clone class and its forced colors. The color equality
is proved in every deleted-vertex coloring avoiding the named configuration;
no compatibility between separately chosen colorings is assumed.
-/

set_option autoImplicit false

universe u

namespace TaskH.Seven

open SimpleGraph _root_.TaskH.Challenge _root_.TaskH.Six
open scoped Classical

variable {V : Type u} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable def sixPairClones (G : SimpleGraph V) [DecidableRel G.Adj]
    (q : Fin 6 → V) (y : V) : Finset V :=
  (sixCliqueSevenSet q y)ᶜ.filter
    (fun x => 2 ≤ (packingNeighborsIn G (sixCliqueSevenSet q y) x).card)

noncomputable def sixPairFamily (G : SimpleGraph V) [DecidableRel G.Adj]
    (q : Fin 6 → V) (y : V) : Finset V := insert y (sixPairClones G q y)

def SixCliqueForcedTo (G : SimpleGraph V) (q : Fin 6 → V) (y x : V) : Prop :=
  ∀ (w : V) (d : (G.induce {z | z ≠ w}).Coloring (Fin 7))
    (_hqw : ∀ i, q i ≠ w) (hyw : y ≠ w) (hxw : x ≠ w),
    d ⟨x, hxw⟩ = d ⟨y, hyw⟩

theorem six_pair_clone_outside (q : Fin 6 → V) (y x : V)
    (hx : x ∈ sixPairClones G q y) : x ∉ sixCliqueSevenSet q y :=
  Finset.mem_compl.mp (Finset.mem_filter.mp hx).1

theorem six_pair_family_outside_clique (q : Fin 6 → V) (y : V)
    (hy : ∀ i, y ≠ q i) (x : V) (hx : x ∈ sixPairFamily G q y) :
    ∀ i, x ≠ q i := by
  classical
  rcases Finset.mem_insert.mp hx with rfl | hx
  · exact hy
  · intro i he
    apply six_pair_clone_outside q y x hx
    rw [he]
    exact Finset.mem_insert_of_mem ((mem_sixCliqueSet q _).mpr ⟨i, rfl⟩)

theorem six_pair_clone_forced (hr : RainbowSevenCycles G)
    (q : Fin 6 → V) (hq : Function.Injective q)
    (hclique : ∀ i j, i ≠ j → G.Adj (q i) (q j))
    (y : V) (hy : ∀ i, y ≠ q i)
    (hy0 : G.Adj y (q 0)) (hy1 : G.Adj y (q 1))
    (x : V) (hx : x ∈ sixPairClones G q y) : SixCliqueForcedTo G q y x := by
  intro w d hqw hyw hxw
  have hxout := six_pair_clone_outside q y x hx
  have hout : x ≠ y ∧ ∀ i, x ≠ q i := by
    constructor
    · intro he
      exact hxout (he.symm ▸ Finset.mem_insert_self y (sixCliqueSet q))
    · intro i he
      apply hxout
      rw [he]
      exact Finset.mem_insert_of_mem ((mem_sixCliqueSet q _).mpr ⟨i, rfl⟩)
  have hcan := actual_six_clique_pair_coloring_constraint hr w d q hq hclique
    y hy 0 1 (by decide) hy0 hy1 hqw hyw x hxw hout
  have hlarge := (Finset.mem_filter.mp hx).2
  exact (hcan.resolve_left (by omega)).1

theorem six_pair_family_forced (hr : RainbowSevenCycles G)
    (q : Fin 6 → V) (hq : Function.Injective q)
    (hclique : ∀ i j, i ≠ j → G.Adj (q i) (q j))
    (y : V) (hy : ∀ i, y ≠ q i)
    (hy0 : G.Adj y (q 0)) (hy1 : G.Adj y (q 1))
    (x : V) (hx : x ∈ sixPairFamily G q y) : SixCliqueForcedTo G q y x := by
  rcases Finset.mem_insert.mp hx with rfl | hx
  · intro w d _hqw hyw hxw
    rfl
  · exact six_pair_clone_forced hr q hq hclique y hy hy0 hy1 x hx

theorem exists_deleted_away_six_clique (q : Fin 6 → V) (hq : Function.Injective q)
    (y : V) (hy : ∀ i, y ≠ q i) (S : Finset V) (hS : S.card ≤ 3)
    (hn : 11 ≤ Fintype.card V) :
    ∃ w : V, w ∉ sixCliqueSevenSet q y ∧ w ∉ S := by
  classical
  let T := sixCliqueSevenSet q y
  have hT : T.card = 7 := sixCliqueSevenSet_card q hq y hy
  have hU : (T ∪ S).card ≤ 10 := by
    have hh := Finset.card_union_le T S
    omega
  have hlt : (T ∪ S).card < (Finset.univ : Finset V).card := by
    rw [Finset.card_univ]
    omega
  obtain ⟨w, _hw, hwo⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
  refine ⟨w, ?_, ?_⟩
  · intro hw
    exact hwo (Finset.mem_union_left S hw)
  · intro hw
    exact hwo (Finset.mem_union_right T hw)

theorem six_pair_clone_neighbors_exact (hcrit : IsCriticalPlus 7 G)
    (hr : RainbowSevenCycles G) (hn : 11 ≤ Fintype.card V)
    (q : Fin 6 → V) (hq : Function.Injective q)
    (hclique : ∀ i j, i ≠ j → G.Adj (q i) (q j))
    (y : V) (hy : ∀ i, y ≠ q i)
    (hy0 : G.Adj y (q 0)) (hy1 : G.Adj y (q 1))
    (x : V) (hx : x ∈ sixPairClones G q y) :
    packingNeighborsIn G (sixCliqueSevenSet q y) x = {q 0, q 1} := by
  classical
  obtain ⟨w, hwT, hwx⟩ := exists_deleted_away_six_clique q hq y hy {x} (by simp) hn
  have hqw : ∀ i, q i ≠ w := by
    intro i he
    apply hwT
    rw [← he]
    exact Finset.mem_insert_of_mem ((mem_sixCliqueSet q _).mpr ⟨i, rfl⟩)
  have hyw : y ≠ w := fun he => hwT (he ▸ Finset.mem_insert_self y (sixCliqueSet q))
  have hxw : x ≠ w := fun he => hwx (he ▸ Finset.mem_singleton_self x)
  have hxout := six_pair_clone_outside q y x hx
  have hout : x ≠ y ∧ ∀ i, x ≠ q i := by
    constructor
    · intro he
      exact hxout (he.symm ▸ Finset.mem_insert_self y (sixCliqueSet q))
    · intro i he
      apply hxout
      rw [he]
      exact Finset.mem_insert_of_mem ((mem_sixCliqueSet q _).mpr ⟨i, rfl⟩)
  obtain ⟨d⟩ := TaskH.critical_colorable_deletedVertex hcrit w
  have hcan := actual_six_clique_pair_coloring_constraint hr w d q hq hclique
    y hy 0 1 (by decide) hy0 hy1 hqw hyw x hxw hout
  have hlarge := (Finset.mem_filter.mp hx).2
  have hsub := (hcan.resolve_left (by omega)).2
  apply Finset.eq_of_subset_of_card_le hsub
  rw [Finset.card_pair (hq.ne (by decide : (0 : Fin 6) ≠ 1))]
  exact hlarge

theorem six_pair_family_independent (hcrit : IsCriticalPlus 7 G)
    (hr : RainbowSevenCycles G) (hn : 11 ≤ Fintype.card V)
    (q : Fin 6 → V) (hq : Function.Injective q)
    (hclique : ∀ i j, i ≠ j → G.Adj (q i) (q j))
    (y : V) (hy : ∀ i, y ≠ q i)
    (hy0 : G.Adj y (q 0)) (hy1 : G.Adj y (q 1)) :
    ∀ x ∈ sixPairFamily G q y, ∀ x' ∈ sixPairFamily G q y, ¬ G.Adj x x' := by
  classical
  intro x hx x' hx' hxx'
  obtain ⟨w, hwT, hwS⟩ := exists_deleted_away_six_clique q hq y hy {x, x'}
    (Finset.card_le_two.trans (by decide)) hn
  have hqw : ∀ i, q i ≠ w := by
    intro i he
    apply hwT
    rw [← he]
    exact Finset.mem_insert_of_mem ((mem_sixCliqueSet q _).mpr ⟨i, rfl⟩)
  have hyw : y ≠ w := fun he => hwT (he ▸ Finset.mem_insert_self y (sixCliqueSet q))
  have hxw : x ≠ w := fun he => hwS (he ▸ Finset.mem_insert_self x {x'})
  have hx'w : x' ≠ w := fun he => hwS (he ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self x'))
  obtain ⟨d⟩ := TaskH.critical_colorable_deletedVertex hcrit w
  have hc := (six_pair_family_forced hr q hq hclique y hy hy0 hy1 x hx w d hqw hyw hxw).trans
    (six_pair_family_forced hr q hq hclique y hy hy0 hy1 x' hx' w d hqw hyw hx'w).symm
  have hadj : (G.induce {z | z ≠ w}).Adj ⟨x, hxw⟩ ⟨x', hx'w⟩ := hxx'
  exact (d.valid hadj) hc

end TaskH.Seven

#print axioms TaskH.Seven.sixPairClones
#print axioms TaskH.Seven.sixPairFamily
#print axioms TaskH.Seven.SixCliqueForcedTo
#print axioms TaskH.Seven.six_pair_clone_outside
#print axioms TaskH.Seven.six_pair_family_outside_clique
#print axioms TaskH.Seven.six_pair_clone_forced
#print axioms TaskH.Seven.six_pair_family_forced
#print axioms TaskH.Seven.exists_deleted_away_six_clique
#print axioms TaskH.Seven.six_pair_clone_neighbors_exact
#print axioms TaskH.Seven.six_pair_family_independent
