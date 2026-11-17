import Research.TaskH.Seven.SevenK6CliquePairPacking
import Research.TaskH.Seven.SevenBoundedIncidence

/-!
The pair-clone packing and the exact seventeen-edge seven-point configuration
contradict the original incidence budget. All clone counts and degree sums
are finite sets of vertices of the actual graph.
-/

set_option autoImplicit false

universe u

namespace TaskH.Seven

open SimpleGraph _root_.TaskH.Challenge _root_.TaskH.Six
open scoped Classical

variable {V : Type u} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]

omit [Fintype V] [DecidableRel G.Adj] in
theorem six_pair_exact_adj (q : Fin 6 → V)
    (hclique : ∀ i j, i ≠ j → G.Adj (q i) (q j)) (y : V)
    (hexact : ∀ i : Fin 6, G.Adj y (q i) ↔ i = 0 ∨ i = 1)
    (i j : Fin 7) : G.Adj (sixCliqueWithPoint q y i) (sixCliqueWithPoint q y j) ↔
      SixCliqueTwoAdj i j := by
  have hQ : ∀ a b : Fin 6, G.Adj (q a) (q b) ↔ a ≠ b := by
    intro a b
    constructor
    · intro hab he
      exact hab.ne (congrArg q he)
    · exact hclique a b
  fin_cases i <;> fin_cases j <;>
    norm_num [sixCliqueWithPoint, SixCliqueTwoAdj, hQ, hexact, G.adj_comm]

omit [Fintype V] in
theorem six_pair_internal_degree_sum (q : Fin 6 → V) (hq : Function.Injective q)
    (hclique : ∀ i j, i ≠ j → G.Adj (q i) (q j))
    (y : V) (hy : ∀ i, y ≠ q i)
    (hexact : ∀ i : Fin 6, G.Adj y (q i) ↔ i = 0 ∨ i = 1) :
    (∑ x ∈ sixCliqueSevenSet q y,
      (packingNeighborsIn G (sixCliqueSevenSet q y) x).card) = 34 := by
  classical
  let e := sixCliqueWithPoint q y
  have he : Function.Injective e := sixCliqueWithPoint_injective q y hq hy
  rw [sixCliqueSevenSet_eq_image, Finset.sum_image he.injOn]
  calc
    _ = ∑ i : Fin 7, ((Finset.univ : Finset (Fin 7)).filter
        (fun j => SixCliqueTwoAdj i j)).card := by
      apply Finset.sum_congr rfl
      intro i _hi
      rw [sixCliqueTwoNeighbors_card _ he]
      congr 1
      ext j
      simp only [sixCliqueTwoNeighborIndices, Finset.mem_filter, Finset.mem_univ, true_and]
      exact six_pair_exact_adj q hclique y hexact i j
    _ = 34 := by decide +kernel

theorem six_pair_outside_neighbors_le_two (hcrit : IsCriticalPlus 7 G)
    (hr : RainbowSevenCycles G) (hn : 11 ≤ Fintype.card V)
    (q : Fin 6 → V) (hq : Function.Injective q)
    (hclique : ∀ i j, i ≠ j → G.Adj (q i) (q j))
    (y : V) (hy : ∀ i, y ≠ q i)
    (hy0 : G.Adj y (q 0)) (hy1 : G.Adj y (q 1))
    (x : V) (hx : x ∉ sixCliqueSevenSet q y) :
    (packingNeighborsIn G (sixCliqueSevenSet q y) x).card ≤ 2 := by
  classical
  by_cases hlarge : 2 ≤ (packingNeighborsIn G (sixCliqueSevenSet q y) x).card
  · have hxZ : x ∈ sixPairClones G q y :=
      Finset.mem_filter.mpr ⟨Finset.mem_compl.mpr hx, hlarge⟩
    rw [six_pair_clone_neighbors_exact hcrit hr hn q hq hclique y hy hy0 hy1 x hxZ]
    exact Finset.card_le_two
  · omega

theorem six_pair_external_degree_sum (hcrit : IsCriticalPlus 7 G)
    (hr : RainbowSevenCycles G) (hn : 11 ≤ Fintype.card V)
    (q : Fin 6 → V) (hq : Function.Injective q)
    (hclique : ∀ i j, i ≠ j → G.Adj (q i) (q j))
    (y : V) (hy : ∀ i, y ≠ q i)
    (hy0 : G.Adj y (q 0)) (hy1 : G.Adj y (q 1)) :
    (∑ x ∈ (sixCliqueSevenSet q y)ᶜ,
      (packingNeighborsIn G (sixCliqueSevenSet q y) x).card) ≤
      (sixCliqueSevenSet q y)ᶜ.card + (sixPairClones G q y).card := by
  classical
  exact bounded_incidence_sum_le_card_add_ge_two (sixCliqueSevenSet q y)ᶜ
    (fun x => (packingNeighborsIn G (sixCliqueSevenSet q y) x).card)
    (by
      intro x hx
      exact six_pair_outside_neighbors_le_two hcrit hr hn q hq hclique y hy hy0 hy1
        x (Finset.mem_compl.mp hx))

theorem critical_six_clique_no_two_hooks (hcrit : IsCriticalPlus 7 G)
    (hs : ShortSevenCycles G) (hr : RainbowSevenCycles G) (hc : modCycleCount 7 G = 2880)
    (hn11 : 11 ≤ Fintype.card V) (hn51 : Fintype.card V ≤ 51)
    (hdegree : ∀ x : V, 8 ≤ G.degree x)
    (q : Fin 6 → V) (hq : Function.Injective q)
    (hclique : ∀ i j, i ≠ j → G.Adj (q i) (q j))
    (y : V) (hy : ∀ i, y ≠ q i)
    (hy0 : G.Adj y (q 0)) (hy1 : G.Adj y (q 1)) : False := by
  classical
  let T := sixCliqueSevenSet q y
  let r := (sixPairClones G q y).card
  have hpair := six_clique_hook_pair_exact hcrit hs hr hc (by omega) q hq hclique y hy hy0 hy1
  have hpack := six_pair_clone_packing hcrit hr hn11 hdegree q hq hclique y hy hpair
  have hr5 : r ≤ 5 := by omega
  have hD : (∑ x ∈ T, G.degree x) ≤ 34 + Tᶜ.card + r := by
    rw [seven_sum_degrees_on_set, six_pair_internal_degree_sum q hq hclique y hy hpair]
    have hh := six_pair_external_degree_sum hcrit hr hn11 q hq hclique y hy hy0 hy1
    change (∑ x ∈ Tᶜ, (packingNeighborsIn G T x).card) ≤ Tᶜ.card + r at hh
    omega
  have hT : T.card = 7 := sixCliqueSevenSet_card q hq y hy
  have hb := seven_set_incidence_degree_budget hs hc
    (fun x => critical_three_hundred_sixty_one_le_cycleDegree hcrit hs x)
    (fun x => critical_singleton_cycle_bound hcrit hs x) T hT (34 + Tᶜ.card + r) hD
  have hcard := Finset.card_add_card_compl T
  rw [hT] at hcard
  have hbudget : 2873 + Fintype.card V ≤ 360 * r := by omega
  omega

end TaskH.Seven

#print axioms TaskH.Seven.six_pair_exact_adj
#print axioms TaskH.Seven.six_pair_internal_degree_sum
#print axioms TaskH.Seven.six_pair_outside_neighbors_le_two
#print axioms TaskH.Seven.six_pair_external_degree_sum
#print axioms TaskH.Seven.critical_six_clique_no_two_hooks
