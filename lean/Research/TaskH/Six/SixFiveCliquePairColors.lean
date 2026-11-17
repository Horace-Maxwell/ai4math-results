import Research.TaskH.Six.SixFiveCliqueThreeHooks

/-!
The actual two-hook clone class and its forced colors. The color equality
is proved in every deleted-vertex coloring avoiding the named configuration;
no compatibility between separately chosen colorings is assumed.
-/

set_option autoImplicit false

universe u

namespace TaskH.Six

open SimpleGraph _root_.TaskH.Challenge
open scoped Classical

variable {V : Type u} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable def fivePairClones (G : SimpleGraph V) [DecidableRel G.Adj]
    (q : Fin 5 → V) (y : V) : Finset V :=
  (fiveCliqueSixSet q y)ᶜ.filter
    (fun x => 2 ≤ (packingNeighborsIn G (fiveCliqueSixSet q y) x).card)

noncomputable def fivePairFamily (G : SimpleGraph V) [DecidableRel G.Adj]
    (q : Fin 5 → V) (y : V) : Finset V := insert y (fivePairClones G q y)

def FiveCliqueForcedTo (G : SimpleGraph V) (q : Fin 5 → V) (y x : V) : Prop :=
  ∀ (w : V) (d : (G.induce {z | z ≠ w}).Coloring (Fin 6))
    (_hqw : ∀ i, q i ≠ w) (hyw : y ≠ w) (hxw : x ≠ w),
    d ⟨x, hxw⟩ = d ⟨y, hyw⟩

theorem five_pair_clone_outside (q : Fin 5 → V) (y x : V)
    (hx : x ∈ fivePairClones G q y) : x ∉ fiveCliqueSixSet q y :=
  Finset.mem_compl.mp (Finset.mem_filter.mp hx).1

theorem five_pair_family_outside_clique (q : Fin 5 → V) (y : V)
    (hy : ∀ i, y ≠ q i) (x : V) (hx : x ∈ fivePairFamily G q y) :
    ∀ i, x ≠ q i := by
  classical
  rcases Finset.mem_insert.mp hx with rfl | hx
  · exact hy
  · intro i he
    apply five_pair_clone_outside q y x hx
    rw [he]
    exact Finset.mem_insert_of_mem ((mem_fiveCliqueSet q _).mpr ⟨i, rfl⟩)

theorem five_pair_clone_forced (hr : RainbowSixCycles G)
    (q : Fin 5 → V) (hq : Function.Injective q)
    (hclique : ∀ i j, i ≠ j → G.Adj (q i) (q j))
    (y : V) (hy : ∀ i, y ≠ q i)
    (hy0 : G.Adj y (q 0)) (hy1 : G.Adj y (q 1))
    (x : V) (hx : x ∈ fivePairClones G q y) : FiveCliqueForcedTo G q y x := by
  intro w d hqw hyw hxw
  have hxout := five_pair_clone_outside q y x hx
  have hout : x ≠ y ∧ ∀ i, x ≠ q i := by
    constructor
    · intro he
      exact hxout (he.symm ▸ Finset.mem_insert_self y (fiveCliqueSet q))
    · intro i he
      apply hxout
      rw [he]
      exact Finset.mem_insert_of_mem ((mem_fiveCliqueSet q _).mpr ⟨i, rfl⟩)
  have hcan := actual_five_clique_pair_coloring_constraint hr w d q hq hclique
    y hy 0 1 (by decide) hy0 hy1 hqw hyw x hxw hout
  have hlarge := (Finset.mem_filter.mp hx).2
  exact (hcan.resolve_left (by omega)).1

theorem five_pair_family_forced (hr : RainbowSixCycles G)
    (q : Fin 5 → V) (hq : Function.Injective q)
    (hclique : ∀ i j, i ≠ j → G.Adj (q i) (q j))
    (y : V) (hy : ∀ i, y ≠ q i)
    (hy0 : G.Adj y (q 0)) (hy1 : G.Adj y (q 1))
    (x : V) (hx : x ∈ fivePairFamily G q y) : FiveCliqueForcedTo G q y x := by
  rcases Finset.mem_insert.mp hx with rfl | hx
  · intro w d _hqw hyw hxw
    rfl
  · exact five_pair_clone_forced hr q hq hclique y hy hy0 hy1 x hx

theorem exists_deleted_away_five_clique (q : Fin 5 → V) (hq : Function.Injective q)
    (y : V) (hy : ∀ i, y ≠ q i) (S : Finset V) (hS : S.card ≤ 3)
    (hn : 10 ≤ Fintype.card V) :
    ∃ w : V, w ∉ fiveCliqueSixSet q y ∧ w ∉ S := by
  classical
  let T := fiveCliqueSixSet q y
  have hT : T.card = 6 := fiveCliqueSixSet_card q hq y hy
  have hU : (T ∪ S).card ≤ 9 := by
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

theorem five_pair_clone_neighbors_exact (hcrit : IsCriticalPlus 6 G)
    (hr : RainbowSixCycles G) (hn : 10 ≤ Fintype.card V)
    (q : Fin 5 → V) (hq : Function.Injective q)
    (hclique : ∀ i j, i ≠ j → G.Adj (q i) (q j))
    (y : V) (hy : ∀ i, y ≠ q i)
    (hy0 : G.Adj y (q 0)) (hy1 : G.Adj y (q 1))
    (x : V) (hx : x ∈ fivePairClones G q y) :
    packingNeighborsIn G (fiveCliqueSixSet q y) x = {q 0, q 1} := by
  classical
  obtain ⟨w, hwT, hwx⟩ := exists_deleted_away_five_clique q hq y hy {x} (by simp) hn
  have hqw : ∀ i, q i ≠ w := by
    intro i he
    apply hwT
    rw [← he]
    exact Finset.mem_insert_of_mem ((mem_fiveCliqueSet q _).mpr ⟨i, rfl⟩)
  have hyw : y ≠ w := fun he => hwT (he ▸ Finset.mem_insert_self y (fiveCliqueSet q))
  have hxw : x ≠ w := fun he => hwx (he ▸ Finset.mem_singleton_self x)
  have hxout := five_pair_clone_outside q y x hx
  have hout : x ≠ y ∧ ∀ i, x ≠ q i := by
    constructor
    · intro he
      exact hxout (he.symm ▸ Finset.mem_insert_self y (fiveCliqueSet q))
    · intro i he
      apply hxout
      rw [he]
      exact Finset.mem_insert_of_mem ((mem_fiveCliqueSet q _).mpr ⟨i, rfl⟩)
  obtain ⟨d⟩ := TaskH.critical_colorable_deletedVertex hcrit w
  have hcan := actual_five_clique_pair_coloring_constraint hr w d q hq hclique
    y hy 0 1 (by decide) hy0 hy1 hqw hyw x hxw hout
  have hlarge := (Finset.mem_filter.mp hx).2
  have hsub := (hcan.resolve_left (by omega)).2
  apply Finset.eq_of_subset_of_card_le hsub
  rw [Finset.card_pair (hq.ne (by decide : (0 : Fin 5) ≠ 1))]
  exact hlarge

theorem five_pair_family_independent (hcrit : IsCriticalPlus 6 G)
    (hr : RainbowSixCycles G) (hn : 10 ≤ Fintype.card V)
    (q : Fin 5 → V) (hq : Function.Injective q)
    (hclique : ∀ i j, i ≠ j → G.Adj (q i) (q j))
    (y : V) (hy : ∀ i, y ≠ q i)
    (hy0 : G.Adj y (q 0)) (hy1 : G.Adj y (q 1)) :
    ∀ x ∈ fivePairFamily G q y, ∀ x' ∈ fivePairFamily G q y, ¬ G.Adj x x' := by
  classical
  intro x hx x' hx' hxx'
  obtain ⟨w, hwT, hwS⟩ := exists_deleted_away_five_clique q hq y hy {x, x'}
    (Finset.card_le_two.trans (by decide)) hn
  have hqw : ∀ i, q i ≠ w := by
    intro i he
    apply hwT
    rw [← he]
    exact Finset.mem_insert_of_mem ((mem_fiveCliqueSet q _).mpr ⟨i, rfl⟩)
  have hyw : y ≠ w := fun he => hwT (he ▸ Finset.mem_insert_self y (fiveCliqueSet q))
  have hxw : x ≠ w := fun he => hwS (he ▸ Finset.mem_insert_self x {x'})
  have hx'w : x' ≠ w := fun he => hwS (he ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self x'))
  obtain ⟨d⟩ := TaskH.critical_colorable_deletedVertex hcrit w
  have hc := (five_pair_family_forced hr q hq hclique y hy hy0 hy1 x hx w d hqw hyw hxw).trans
    (five_pair_family_forced hr q hq hclique y hy hy0 hy1 x' hx' w d hqw hyw hx'w).symm
  have hadj : (G.induce {z | z ≠ w}).Adj ⟨x, hxw⟩ ⟨x', hx'w⟩ := hxx'
  exact (d.valid hadj) hc

end TaskH.Six

#print axioms TaskH.Six.fivePairClones
#print axioms TaskH.Six.fivePairFamily
#print axioms TaskH.Six.FiveCliqueForcedTo
#print axioms TaskH.Six.five_pair_clone_outside
#print axioms TaskH.Six.five_pair_family_outside_clique
#print axioms TaskH.Six.five_pair_clone_forced
#print axioms TaskH.Six.five_pair_family_forced
#print axioms TaskH.Six.exists_deleted_away_five_clique
#print axioms TaskH.Six.five_pair_clone_neighbors_exact
#print axioms TaskH.Six.five_pair_family_independent
