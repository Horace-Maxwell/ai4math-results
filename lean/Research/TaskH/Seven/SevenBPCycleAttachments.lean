import Research.TaskH.Seven.SevenBPAttachmentTwoEar
import Research.TaskH.Seven.SevenBPSameParitySupport
import Research.TaskH.Seven.SevenBPBoundaryBudget

/-! Actual outside C16 neighbors, including parity, the at-most-four bound,
and the exact partition into cycle and outside neighbors. -/

set_option autoImplicit false

universe u

namespace TaskH.Seven.BP

open SimpleGraph
open scoped Classical

variable {V : Type u} {G : SimpleGraph V}

noncomputable def outsideHookFinset (G : SimpleGraph V) (u : Fin 16 → V) (z : V) :
    Finset (Fin 16) := Finset.univ.filter (fun i => G.Adj z (u i))

theorem mem_outsideHookFinset (u : Fin 16 → V) (z : V) (i : Fin 16) :
    i ∈ outsideHookFinset G u z ↔ G.Adj z (u i) := by
  simp only [outsideHookFinset, Finset.mem_filter, Finset.mem_univ, true_and]

theorem outside_hook_indices_same_parity (u : Fin 16 → V)
    (hu : IsCycleSixteen G u) (c : G.Coloring Bool) (z : V)
    (i j : Fin 16) (hi : G.Adj z (u i)) (hj : G.Adj z (u j)) :
    i.val % 2 = j.val % 2 := by
  have hne1 := c.valid hi
  have hne2 := c.valid hj
  have hsame : c (u i) = c (u j) := by
    cases h0 : c z <;> cases h1 : c (u i) <;> cases h2 : c (u j) <;> simp_all
  have hei := cycle_sixteen_color_even_iff u hu c i
  have hej := cycle_sixteen_color_even_iff u hu c j
  have hev : Even i.val ↔ Even j.val := by
    rw [hsame] at hei
    exact hei.trans hej.symm
  simp only [Nat.even_iff] at hev
  omega

theorem outside_hook_card_le_four (hb : G.IsBipartite) (u : Fin 16 → V)
    (hu : IsCycleSixteen G u) (hn : NoFourteenCycle G)
    (z : V) (hz : z ∉ Set.range u) : (outsideHookFinset G u z).card ≤ 4 := by
  let c : G.Coloring Bool := SimpleGraph.recolorOfEquiv G finTwoEquiv hb.some
  apply same_parity_no_four_step_card_le_four
  · intro i hi hj
    exact outside_no_distance_four_hooks u hu hn z hz i
      ((mem_outsideHookFinset u z i).mp hi) ((mem_outsideHookFinset u z (i + 4)).mp hj)
  · intro i hi j hj
    exact outside_hook_indices_same_parity u hu c z i j
      ((mem_outsideHookFinset u z i).mp hi) ((mem_outsideHookFinset u z j).mp hj)

theorem actual_cycle_neighbor_card [Fintype V] (u : Fin 16 → V)
    (hu : Function.Injective u) (z : V) :
    (G.neighborFinset z ∩ Finset.univ.image u).card = (outsideHookFinset G u z).card := by
  classical
  have him : (outsideHookFinset G u z).image u =
      G.neighborFinset z ∩ Finset.univ.image u := by
    ext v
    constructor
    · intro hv
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hv
      exact Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr
        ((mem_outsideHookFinset u z i).mp hi),
        Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩⟩
    · intro hv
      obtain ⟨hn, hc⟩ := Finset.mem_inter.mp hv
      obtain ⟨i, _hi, rfl⟩ := Finset.mem_image.mp hc
      exact Finset.mem_image.mpr ⟨i, (mem_outsideHookFinset u z i).mpr
        ((G.mem_neighborFinset _ _).mp hn), rfl⟩
  rw [← him, Finset.card_image_of_injective _ hu]

theorem outside_degree_partition [Fintype V] (u : Fin 16 → V)
    (hu : Function.Injective u) (z : V) :
    (outsideHookFinset G u z).card +
      (G.neighborFinset z \ Finset.univ.image u).card = G.degree z := by
  have h := boundary_degree_partition (G := G) (Finset.univ.image u) z
  rw [actual_cycle_neighbor_card u hu z] at h
  exact h

theorem outside_degree_ge_three [Fintype V] (hb : G.IsBipartite)
    (u : Fin 16 → V) (hu : IsCycleSixteen G u) (hn : NoFourteenCycle G)
    (z : V) (hz : z ∉ Set.range u) (hd : 7 ≤ G.degree z) :
    3 ≤ (G.neighborFinset z \ Finset.univ.image u).card := by
  have hc := outside_hook_card_le_four hb u hu hn z hz
  have hp := outside_degree_partition (G := G) u hu.1 z
  omega

theorem outside_degree_ge_four_of_three_hooks [Fintype V]
    (u : Fin 16 → V) (hu : Function.Injective u) (z : V)
    (hh : (outsideHookFinset G u z).card = 3) (hd : 7 ≤ G.degree z) :
    4 ≤ (G.neighborFinset z \ Finset.univ.image u).card := by
  have hp := outside_degree_partition (G := G) u hu z
  omega

theorem outside_degree_ge_five_of_at_most_two_hooks [Fintype V]
    (u : Fin 16 → V) (hu : Function.Injective u) (z : V)
    (hh : (outsideHookFinset G u z).card ≤ 2) (hd : 7 ≤ G.degree z) :
    5 ≤ (G.neighborFinset z \ Finset.univ.image u).card := by
  have hp := outside_degree_partition (G := G) u hu z
  omega

end TaskH.Seven.BP

#print axioms TaskH.Seven.BP.outsideHookFinset
#print axioms TaskH.Seven.BP.mem_outsideHookFinset
#print axioms TaskH.Seven.BP.outside_hook_indices_same_parity
#print axioms TaskH.Seven.BP.outside_hook_card_le_four
#print axioms TaskH.Seven.BP.actual_cycle_neighbor_card
#print axioms TaskH.Seven.BP.outside_degree_partition
#print axioms TaskH.Seven.BP.outside_degree_ge_three
#print axioms TaskH.Seven.BP.outside_degree_ge_four_of_three_hooks
#print axioms TaskH.Seven.BP.outside_degree_ge_five_of_at_most_two_hooks
