import Research.TaskH.Seven.SevenK6CliquePairColors

/-!
Two distinct actual members of the forced two-hook family cannot share an
outside neighbor: the fixed clique path q0-q2-q3-q1 closes a genuine seven-cycle
with repeated colors in one and the same deleted-vertex coloring.
-/

set_option autoImplicit false

universe u

namespace TaskH.Seven

open SimpleGraph _root_.TaskH.Challenge _root_.TaskH.Six
open scoped Classical

variable {V : Type u} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem six_pair_family_hook_adj (hcrit : IsCriticalPlus 7 G)
    (hr : RainbowSevenCycles G) (hn : 11 ≤ Fintype.card V)
    (q : Fin 6 → V) (hq : Function.Injective q)
    (hclique : ∀ i j, i ≠ j → G.Adj (q i) (q j))
    (y : V) (hy : ∀ i, y ≠ q i)
    (hy0 : G.Adj y (q 0)) (hy1 : G.Adj y (q 1))
    (x : V) (hx : x ∈ sixPairFamily G q y) :
    G.Adj x (q 0) ∧ G.Adj x (q 1) := by
  classical
  rcases Finset.mem_insert.mp hx with rfl | hx
  · exact ⟨hy0, hy1⟩
  · have he := six_pair_clone_neighbors_exact hcrit hr hn q hq hclique y hy hy0 hy1 x hx
    have h0 : q 0 ∈ packingNeighborsIn G (sixCliqueSevenSet q y) x := by
      rw [he]
      exact Finset.mem_insert_self _ _
    have h1 : q 1 ∈ packingNeighborsIn G (sixCliqueSevenSet q y) x := by
      rw [he]
      exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
    exact ⟨(Finset.mem_filter.mp h0).2, (Finset.mem_filter.mp h1).2⟩

theorem six_pair_family_common_neighbor_unique (hcrit : IsCriticalPlus 7 G)
    (hr : RainbowSevenCycles G) (hn : 11 ≤ Fintype.card V)
    (q : Fin 6 → V) (hq : Function.Injective q)
    (hclique : ∀ i j, i ≠ j → G.Adj (q i) (q j))
    (y : V) (hy : ∀ i, y ≠ q i)
    (hy0 : G.Adj y (q 0)) (hy1 : G.Adj y (q 1)) :
    ∀ z ∉ sixCliqueSevenSet q y, ∀ x ∈ sixPairFamily G q y,
      ∀ x' ∈ sixPairFamily G q y, G.Adj x z → G.Adj x' z → x = x' := by
  classical
  intro z hz x hx x' hx' hxz hx'z
  by_contra hxx'
  have hxq := six_pair_family_outside_clique q y hy x hx
  have hx'q := six_pair_family_outside_clique q y hy x' hx'
  have hzq : ∀ i, z ≠ q i := by
    intro i he
    apply hz
    rw [he]
    exact Finset.mem_insert_of_mem ((mem_sixCliqueSet q _).mpr ⟨i, rfl⟩)
  have hx0 := (six_pair_family_hook_adj hcrit hr hn q hq hclique y hy hy0 hy1 x hx).1
  have hx'1 := (six_pair_family_hook_adj hcrit hr hn q hq hclique y hy hy0 hy1 x' hx').2
  have h02 := hclique 0 2 (by decide)
  have h23 := hclique 2 3 (by decide)
  have h31 := hclique 3 1 (by decide)
  let g : Fin 7 → V := ![x, q 0, q 2, q 3, q 1, x', z]
  have hg : Function.Injective g := by
    intro i j hij
    fin_cases i <;> fin_cases j
    all_goals first
      | rfl
      | exact False.elim (hxx' hij)
      | exact False.elim (hxx' hij.symm)
      | exact False.elim (hxz.ne hij)
      | exact False.elim (hxz.ne hij.symm)
      | exact False.elim (hx'z.ne hij)
      | exact False.elim (hx'z.ne hij.symm)
      | exact False.elim (hxq 0 hij)
      | exact False.elim (hxq 0 hij.symm)
      | exact False.elim (hxq 1 hij)
      | exact False.elim (hxq 1 hij.symm)
      | exact False.elim (hxq 2 hij)
      | exact False.elim (hxq 2 hij.symm)
      | exact False.elim (hx'q 0 hij)
      | exact False.elim (hx'q 0 hij.symm)
      | exact False.elim (hx'q 1 hij)
      | exact False.elim (hx'q 1 hij.symm)
      | exact False.elim (hx'q 2 hij)
      | exact False.elim (hx'q 2 hij.symm)
      | exact False.elim (hzq 0 hij)
      | exact False.elim (hzq 0 hij.symm)
      | exact False.elim (hzq 1 hij)
      | exact False.elim (hzq 1 hij.symm)
      | exact False.elim (hzq 2 hij)
      | exact False.elim (hzq 2 hij.symm)
      | exact False.elim (hxq 3 hij)
      | exact False.elim (hxq 3 hij.symm)
      | exact False.elim (hx'q 3 hij)
      | exact False.elim (hx'q 3 hij.symm)
      | exact False.elim (hzq 3 hij)
      | exact False.elim (hzq 3 hij.symm)
      | exact False.elim ((by decide : (0 : Fin 6) ≠ 1) (hq hij))
      | exact False.elim ((by decide : (0 : Fin 6) ≠ 2) (hq hij))
      | exact False.elim ((by decide : (1 : Fin 6) ≠ 0) (hq hij))
      | exact False.elim ((by decide : (1 : Fin 6) ≠ 2) (hq hij))
      | exact False.elim ((by decide : (2 : Fin 6) ≠ 0) (hq hij))
      | exact False.elim ((by decide : (2 : Fin 6) ≠ 1) (hq hij))
      | exact False.elim ((by decide : (0 : Fin 6) ≠ 3) (hq hij))
      | exact False.elim ((by decide : (1 : Fin 6) ≠ 3) (hq hij))
      | exact False.elim ((by decide : (2 : Fin 6) ≠ 3) (hq hij))
      | exact False.elim ((by decide : (3 : Fin 6) ≠ 0) (hq hij))
      | exact False.elim ((by decide : (3 : Fin 6) ≠ 1) (hq hij))
      | exact False.elim ((by decide : (3 : Fin 6) ≠ 2) (hq hij))
  let p := heptagonWalk G g hx0 h02 h23 h31 hx'1.symm hx'z hxz.symm
  have hp : p.IsCycle := heptagonWalk_isCycle G g hg hx0 h02 h23 h31 hx'1.symm hx'z hxz.symm
  obtain ⟨w, hwT, hwS⟩ := exists_deleted_away_six_clique q hq y hy {x, x', z}
    Finset.card_le_three hn
  have hqw : ∀ i, q i ≠ w := by
    intro i he
    apply hwT
    rw [← he]
    exact Finset.mem_insert_of_mem ((mem_sixCliqueSet q _).mpr ⟨i, rfl⟩)
  have hyw : y ≠ w := fun he => hwT (he ▸ Finset.mem_insert_self y (sixCliqueSet q))
  have hxw : x ≠ w := fun he => hwS (he ▸ Finset.mem_insert_self x {x', z})
  have hx'w : x' ≠ w := fun he => hwS (he ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self x' {z}))
  obtain ⟨d⟩ := TaskH.critical_colorable_deletedVertex hcrit w
  have hcolor := (six_pair_family_forced hr q hq hclique y hy hy0 hy1 x hx w d hqw hyw hxw).trans
    (six_pair_family_forced hr q hq hclique y hy hy0 hy1 x' hx' w d hqw hyw hx'w).symm
  have hx'in : x' ∈ p.support := by simp [p, heptagonWalk, g, Walk.support_cons]
  have he := hr w d p hp (by rfl) ⟨x, hxw⟩ ⟨x', hx'w⟩ p.start_mem_support hx'in hcolor
  exact hxx' (congrArg Subtype.val he)

end TaskH.Seven

#print axioms TaskH.Seven.six_pair_family_hook_adj
#print axioms TaskH.Seven.six_pair_family_common_neighbor_unique
