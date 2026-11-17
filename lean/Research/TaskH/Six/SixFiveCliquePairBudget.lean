import Research.TaskH.Six.SixFiveCliquePairPacking

/-!
The pair-clone packing and the exact twelve-edge six-point configuration
contradict the original incidence budget. All clone counts and degree sums
are finite sets of vertices of the actual graph.
-/

set_option autoImplicit false

universe u

namespace TaskH.Six

open SimpleGraph _root_.TaskH.Challenge
open scoped Classical

variable {V : Type u} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]

omit [Fintype V] [DecidableRel G.Adj] in
theorem five_pair_exact_adj (q : Fin 5 → V)
    (hclique : ∀ i j, i ≠ j → G.Adj (q i) (q j)) (y : V)
    (hexact : ∀ i : Fin 5, G.Adj y (q i) ↔ i = 0 ∨ i = 1)
    (i j : Fin 6) : G.Adj (fiveCliqueWithPoint q y i) (fiveCliqueWithPoint q y j) ↔
      FiveCliqueTwoAdj i j := by
  have hQ : ∀ a b : Fin 5, G.Adj (q a) (q b) ↔ a ≠ b := by
    intro a b
    constructor
    · intro hab he
      exact hab.ne (congrArg q he)
    · exact hclique a b
  fin_cases i <;> fin_cases j <;>
    norm_num [fiveCliqueWithPoint, FiveCliqueTwoAdj, hQ, hexact, G.adj_comm]

omit [Fintype V] in
theorem five_pair_internal_degree_sum (q : Fin 5 → V) (hq : Function.Injective q)
    (hclique : ∀ i j, i ≠ j → G.Adj (q i) (q j))
    (y : V) (hy : ∀ i, y ≠ q i)
    (hexact : ∀ i : Fin 5, G.Adj y (q i) ↔ i = 0 ∨ i = 1) :
    (∑ x ∈ fiveCliqueSixSet q y,
      (packingNeighborsIn G (fiveCliqueSixSet q y) x).card) = 24 := by
  classical
  let e := fiveCliqueWithPoint q y
  have he : Function.Injective e := fiveCliqueWithPoint_injective q y hq hy
  rw [fiveCliqueSixSet_eq_image, Finset.sum_image he.injOn]
  calc
    _ = ∑ i : Fin 6, ((Finset.univ : Finset (Fin 6)).filter
        (fun j => FiveCliqueTwoAdj i j)).card := by
      apply Finset.sum_congr rfl
      intro i _hi
      rw [fiveCliqueTwoNeighbors_card _ he]
      congr 1
      ext j
      simp only [fiveCliqueTwoNeighborIndices, Finset.mem_filter, Finset.mem_univ, true_and]
      exact five_pair_exact_adj q hclique y hexact i j
    _ = 24 := by decide +kernel

theorem five_pair_outside_neighbors_le_two (hcrit : IsCriticalPlus 6 G)
    (hr : RainbowSixCycles G) (hn : 10 ≤ Fintype.card V)
    (q : Fin 5 → V) (hq : Function.Injective q)
    (hclique : ∀ i j, i ≠ j → G.Adj (q i) (q j))
    (y : V) (hy : ∀ i, y ≠ q i)
    (hy0 : G.Adj y (q 0)) (hy1 : G.Adj y (q 1))
    (x : V) (hx : x ∉ fiveCliqueSixSet q y) :
    (packingNeighborsIn G (fiveCliqueSixSet q y) x).card ≤ 2 := by
  classical
  by_cases hlarge : 2 ≤ (packingNeighborsIn G (fiveCliqueSixSet q y) x).card
  · have hxZ : x ∈ fivePairClones G q y :=
      Finset.mem_filter.mpr ⟨Finset.mem_compl.mpr hx, hlarge⟩
    rw [five_pair_clone_neighbors_exact hcrit hr hn q hq hclique y hy hy0 hy1 x hxZ]
    exact Finset.card_le_two
  · omega

theorem five_pair_external_degree_sum (hcrit : IsCriticalPlus 6 G)
    (hr : RainbowSixCycles G) (hn : 10 ≤ Fintype.card V)
    (q : Fin 5 → V) (hq : Function.Injective q)
    (hclique : ∀ i j, i ≠ j → G.Adj (q i) (q j))
    (y : V) (hy : ∀ i, y ≠ q i)
    (hy0 : G.Adj y (q 0)) (hy1 : G.Adj y (q 1)) :
    (∑ x ∈ (fiveCliqueSixSet q y)ᶜ,
      (packingNeighborsIn G (fiveCliqueSixSet q y) x).card) ≤
      (fiveCliqueSixSet q y)ᶜ.card + (fivePairClones G q y).card := by
  classical
  let T := fiveCliqueSixSet q y
  have hrow : ∀ x ∈ Tᶜ, (packingNeighborsIn G T x).card ≤
      1 + if 2 ≤ (packingNeighborsIn G T x).card then 1 else 0 := by
    intro x hx
    have hh := five_pair_outside_neighbors_le_two hcrit hr hn q hq hclique y hy hy0 hy1
      x (Finset.mem_compl.mp hx)
    split_ifs <;> omega
  calc
    _ ≤ ∑ x ∈ Tᶜ, (1 + if 2 ≤ (packingNeighborsIn G T x).card then 1 else 0) :=
      Finset.sum_le_sum hrow
    _ = Tᶜ.card + (Tᶜ.filter
        (fun x => 2 ≤ (packingNeighborsIn G T x).card)).card := by
      rw [Finset.sum_add_distrib]
      have hones : (∑ _x ∈ Tᶜ, (1 : ℕ)) = Tᶜ.card := by
        simp only [Finset.sum_const, Nat.nsmul_eq_mul, Nat.mul_one]
      rw [hones]
      congr 1
      rw [Finset.card_eq_sum_ones, Finset.sum_filter]
    _ = _ := rfl

theorem critical_five_clique_no_two_hooks (hcrit : IsCriticalPlus 6 G)
    (hs : ShortSixCycles G) (hr : RainbowSixCycles G) (hc : modCycleCount 6 G = 420)
    (hn10 : 10 ≤ Fintype.card V) (hn37 : Fintype.card V ≤ 37)
    (hdegree : ∀ x : V, 8 ≤ G.degree x)
    (q : Fin 5 → V) (hq : Function.Injective q)
    (hclique : ∀ i j, i ≠ j → G.Adj (q i) (q j))
    (y : V) (hy : ∀ i, y ≠ q i)
    (hy0 : G.Adj y (q 0)) (hy1 : G.Adj y (q 1)) : False := by
  classical
  let T := fiveCliqueSixSet q y
  let r := (fivePairClones G q y).card
  have hpair := five_clique_hook_pair_exact hcrit hs hr hc (by omega) q hq hclique y hy hy0 hy1
  have hpack := five_pair_clone_packing hcrit hr hn10 hdegree q hq hclique y hy hpair
  have hr3 : r ≤ 3 := clone_count_le_three (Fintype.card V) r hn37 hpack
  have hD : (∑ x ∈ T, G.degree x) ≤ 24 + Tᶜ.card + r := by
    rw [six_sum_degrees_on_set, five_pair_internal_degree_sum q hq hclique y hy hpair]
    have hh := five_pair_external_degree_sum hcrit hr hn10 q hq hclique y hy hy0 hy1
    change (∑ x ∈ Tᶜ, (packingNeighborsIn G T x).card) ≤ Tᶜ.card + r at hh
    omega
  have hT : T.card = 6 := fiveCliqueSixSet_card q hq y hy
  have hb := six_set_incidence_degree_budget hs hc
    (fun x => critical_sixty_one_le_cycleDegree hcrit hs x)
    (fun x => critical_singleton_cycle_bound hcrit hs x) T hT (24 + Tᶜ.card + r) hD
  have hcard := Finset.card_add_card_compl T
  rw [hT] at hcard
  have hbudget : 2874 + Fintype.card V ≤ 2520 + 60 * r := by omega
  exact six_point_clone_incidence_incompatible (Fintype.card V) r hr3 hbudget

end TaskH.Six

#print axioms TaskH.Six.five_pair_exact_adj
#print axioms TaskH.Six.five_pair_internal_degree_sum
#print axioms TaskH.Six.five_pair_outside_neighbors_le_two
#print axioms TaskH.Six.five_pair_external_degree_sum
#print axioms TaskH.Six.critical_five_clique_no_two_hooks
