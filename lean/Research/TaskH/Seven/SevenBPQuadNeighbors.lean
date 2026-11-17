import Research.TaskH.Seven.SevenBPForcedLow
import Research.TaskH.Seven.SevenBPQuadNeighborGroups

/-! Real adjacent outside neighbors of a four-hook C16 vertex have at most
two hooks. Thus four actual same-side zero-hook vertices are forced. -/

set_option autoImplicit false

universe u

namespace TaskH.Seven.BP

open SimpleGraph
open scoped Classical

variable {V : Type u} {G : SimpleGraph V}

theorem outsideHook_rotate_card (u : Fin 16 → V) (z : V) (i : Fin 16) :
    (outsideHookFinset G (earRotateSixteen u i) z).card =
      (outsideHookFinset G u z).card := by
  apply Finset.card_bij (fun j _ => i + j)
  · intro j hj
    exact (mem_outsideHookFinset u z (i + j)).mpr
      ((mem_outsideHookFinset (earRotateSixteen u i) z j).mp hj)
  · intro a _ b _ hab
    exact add_left_cancel hab
  · intro j hj
    refine ⟨j - i, ?_, ?_⟩
    · apply (mem_outsideHookFinset (earRotateSixteen u i) z (j - i)).mpr
      simpa only [earRotateSixteen, add_comm i (j - i), sub_add_cancel] using
        (mem_outsideHookFinset u z j).mp hj
    · simp only [add_comm i (j - i), sub_add_cancel]

theorem no_adjacent_distance_five_hooks (u : Fin 16 → V) (hu : IsCycleSixteen G u)
    (hn : NoFourteenCycle G) (z q : V) (hz : z ∉ Set.range u)
    (hq : q ∉ Set.range u) (hzq : G.Adj z q) (i : Fin 16)
    (hi : G.Adj z (u i)) : ¬ G.Adj q (u (i + 5)) := by
  have hr : ∀ x : V, x ∉ Set.range u → x ∉ Set.range (earRotateSixteen u i) := by
    intro x hx
    rintro ⟨j, hj⟩
    exact hx ⟨i + j, hj⟩
  have h0 : G.Adj z (earRotateSixteen u i 0) := by
    simpa only [earRotateSixteen, add_zero] using hi
  exact no_adjacent_zero_five_hooks (earRotateSixteen u i)
    (earRotateSixteen_isCycle u hu i) hn z q (hr z hz) (hr q hq) hzq h0

theorem no_adjacent_distance_eleven_hooks (u : Fin 16 → V) (hu : IsCycleSixteen G u)
    (hn : NoFourteenCycle G) (z q : V) (hz : z ∉ Set.range u)
    (hq : q ∉ Set.range u) (hzq : G.Adj z q) (i : Fin 16)
    (hi : G.Adj z (u i)) : ¬ G.Adj q (u (i + 11)) := by
  intro hj
  have hshift : ∀ j : Fin 16, (j + 11) + 5 = j := by
    decide +kernel
  have hc : (i + 11) + 5 = i := hshift i
  have hh := no_adjacent_distance_five_hooks u hu hn q z hq hz hzq.symm (i + 11) hj
  rw [hc] at hh
  exact hh hi

theorem adjacent_outside_hook_opposite_parity (u : Fin 16 → V)
    (hu : IsCycleSixteen G u) (c : G.Coloring Bool) (z q : V)
    (hzq : G.Adj z q) (h0 : G.Adj z (u 0)) (j : Fin 16)
    (hj : G.Adj q (u j)) : j.val % 2 = 1 := by
  have hc0 := c.valid h0
  have hc1 := c.valid hzq
  have hc2 := c.valid hj
  have he := cycle_sixteen_color_even_iff u hu c j
  have hn : ¬ Even j.val := by
    intro hev
    have hh := he.mp hev
    cases cz : c z <;> cases cq : c q <;> cases c0 : c (u 0) <;>
      cases cj : c (u j) <;> simp_all
  simp only [Nat.even_iff] at hn
  omega

theorem normalized_quad_neighbor_hook_card (hb : G.IsBipartite)
    (u : Fin 16 → V) (hu : IsCycleSixteen G u) (hn : NoFourteenCycle G)
    (z q : V) (hz : z ∉ Set.range u) (hq : q ∉ Set.range u)
    (hzq : G.Adj z q) (h0 : G.Adj z (u 0))
    (h4 : (outsideHookFinset G u z).card = 4) :
    (outsideHookFinset G u q).card ≤ 2 := by
  let c : G.Coloring Bool := SimpleGraph.recolorOfEquiv G finTwoEquiv hb.some
  apply quad_even_adjacent_odd_capacity (outsideHookFinset G u z)
    (outsideHookFinset G u q)
  · intro i hi hj
    exact outside_no_distance_four_hooks u hu hn z hz i
      ((mem_outsideHookFinset u z i).mp hi)
      ((mem_outsideHookFinset u z (i + 4)).mp hj)
  · intro i hi
    exact outside_hook_indices_same_parity u hu c z i 0
      ((mem_outsideHookFinset u z i).mp hi) h0
  · intro j hj
    exact adjacent_outside_hook_opposite_parity u hu c z q hzq h0 j
      ((mem_outsideHookFinset u q j).mp hj)
  · intro i hi hj
    exact no_adjacent_distance_five_hooks u hu hn z q hz hq hzq i
      ((mem_outsideHookFinset u z i).mp hi)
      ((mem_outsideHookFinset u q (i + 5)).mp hj)
  · intro i hi hj
    exact no_adjacent_distance_eleven_hooks u hu hn z q hz hq hzq i
      ((mem_outsideHookFinset u z i).mp hi)
      ((mem_outsideHookFinset u q (i + 11)).mp hj)
  · exact h4

theorem actual_quad_neighbor_hook_card (hb : G.IsBipartite)
    (u : Fin 16 → V) (hu : IsCycleSixteen G u) (hn : NoFourteenCycle G)
    (z q : V) (hz : z ∉ Set.range u) (hq : q ∉ Set.range u)
    (hzq : G.Adj z q) (h4 : (outsideHookFinset G u z).card = 4) :
    (outsideHookFinset G u q).card ≤ 2 := by
  obtain ⟨i, hi⟩ := Finset.card_pos.mp
    (show 0 < (outsideHookFinset G u z).card by omega)
  have hr : ∀ x : V, x ∉ Set.range u → x ∉ Set.range (earRotateSixteen u i) := by
    intro x hx
    rintro ⟨j, hj⟩
    exact hx ⟨i + j, hj⟩
  have h0 : G.Adj z (earRotateSixteen u i 0) := by
    simpa only [earRotateSixteen, add_zero] using (mem_outsideHookFinset u z i).mp hi
  have h4r : (outsideHookFinset G (earRotateSixteen u i) z).card = 4 := by
    rw [outsideHook_rotate_card u z i]
    exact h4
  have hh := normalized_quad_neighbor_hook_card hb (earRotateSixteen u i)
    (earRotateSixteen_isCycle u hu i) hn z q (hr z hz) (hr q hq) hzq h0 h4r
  rw [outsideHook_rotate_card u q i] at hh
  exact hh

theorem quad_forces_four_zero_actual [Fintype V] (hb : G.IsBipartite)
    (u : Fin 16 → V) (hu : IsCycleSixteen G u) (hn : NoFourteenCycle G)
    (hd : ∀ v : V, 7 ≤ G.degree v)
    (z : V) (hz : z ∉ Set.range u) (h4z : (outsideHookFinset G u z).card = 4) :
    ∃ q : V, G.Adj z q ∧ q ∉ Set.range u ∧
      4 ≤ (actualOutsideNeighbors G u q \ {z}).card ∧
      ∀ w ∈ actualOutsideNeighbors G u q \ {z},
        (outsideHookFinset G u w).card = 0 := by
  have hN3 : 3 ≤ (actualOutsideNeighbors G u z).card :=
    outside_degree_ge_three hb u hu hn z hz (hd z)
  obtain ⟨q, hqN⟩ := Finset.card_pos.mp
    (show 0 < (actualOutsideNeighbors G u z).card by omega)
  have hq' := (mem_actualOutsideNeighbors u z q).mp hqN
  have hq2 := actual_quad_neighbor_hook_card hb u hu hn z q hz hq'.2 hq'.1 h4z
  have hN5 : 5 ≤ (actualOutsideNeighbors G u q).card :=
    outside_degree_ge_five_of_at_most_two_hooks u hu.1 q hq2 (hd q)
  have hzN : z ∈ actualOutsideNeighbors G u q :=
    (mem_actualOutsideNeighbors u q z).mpr ⟨hq'.1.symm, hz⟩
  have hcard : (actualOutsideNeighbors G u q \ {z}).card + 1 =
      (actualOutsideNeighbors G u q).card := by
    simpa only [Finset.sdiff_singleton_eq_erase] using Finset.card_erase_add_one hzN
  refine ⟨q, hq'.1, hq'.2, by omega, ?_⟩
  intro w hw
  obtain ⟨hwN, hwe⟩ := Finset.mem_sdiff.mp hw
  have hw' := (mem_actualOutsideNeighbors u q w).mp hwN
  have hzw : z ≠ w := by
    intro he
    exact hwe (Finset.mem_singleton.mpr he.symm)
  exact actual_quad_shared_has_zero_hooks hb u hu hn z q w hz hq'.2 hw'.2
    hzw hq'.1 hw'.1 h4z

end TaskH.Seven.BP

#print axioms TaskH.Seven.BP.outsideHook_rotate_card
#print axioms TaskH.Seven.BP.no_adjacent_distance_five_hooks
#print axioms TaskH.Seven.BP.no_adjacent_distance_eleven_hooks
#print axioms TaskH.Seven.BP.adjacent_outside_hook_opposite_parity
#print axioms TaskH.Seven.BP.normalized_quad_neighbor_hook_card
#print axioms TaskH.Seven.BP.actual_quad_neighbor_hook_card
#print axioms TaskH.Seven.BP.quad_forces_four_zero_actual
