import Research.TaskH.Seven.SevenBPAttachmentFourEar
import Research.TaskH.Seven.SevenBPSharedHookGroups

/-! The residue capacity applies to the actual hook sets of two distinct
outside vertices with a real common outside neighbor. -/

set_option autoImplicit false

universe u

namespace TaskH.Seven.BP

open SimpleGraph
open scoped Classical

variable {V : Type u} {G : SimpleGraph V}

theorem shared_outside_hook_parity (u : Fin 16 → V) (hu : IsCycleSixteen G u)
    (c : G.Coloring Bool) (z q w : V) (hzq : G.Adj z q) (hqw : G.Adj q w)
    (i j : Fin 16) (hi : G.Adj z (u i)) (hj : G.Adj w (u j)) :
    i.val % 2 = j.val % 2 := by
  have h0 := c.valid hzq
  have h1 := c.valid hqw
  have h2 := c.valid hi
  have h3 := c.valid hj
  have he : c (u i) = c (u j) := by
    cases cz : c z <;> cases cq : c q <;> cases cw : c w <;>
      cases ci : c (u i) <;> cases cj : c (u j) <;> simp_all
  have hei := cycle_sixteen_color_even_iff u hu c i
  have hej := cycle_sixteen_color_even_iff u hu c j
  have hv : Even i.val ↔ Even j.val := by
    rw [he] at hei
    exact hei.trans hej.symm
  simp only [Nat.even_iff] at hv
  omega

theorem actual_high_shared_hook_capacity (hb : G.IsBipartite)
    (u : Fin 16 → V) (hu : IsCycleSixteen G u) (hn : NoFourteenCycle G)
    (z q w : V) (hz : z ∉ Set.range u) (hq : q ∉ Set.range u)
    (hw : w ∉ Set.range u) (hzw : z ≠ w) (hzq : G.Adj z q) (hqw : G.Adj q w)
    (hh : 3 ≤ (outsideHookFinset G u z).card) :
    (outsideHookFinset G u w).card ≤ 1 ∧
      (4 ≤ (outsideHookFinset G u z).card → (outsideHookFinset G u w).card = 0) := by
  let c : G.Coloring Bool := SimpleGraph.recolorOfEquiv G finTwoEquiv hb.some
  obtain ⟨i, hi⟩ := Finset.card_pos.mp
    (show 0 < (outsideHookFinset G u z).card by omega)
  have hzi := (mem_outsideHookFinset u z i).mp hi
  apply same_parity_shared_high_capacity (outsideHookFinset G u z)
    (outsideHookFinset G u w) (i.val % 2)
  · intro j hj hj4
    exact outside_no_distance_four_hooks u hu hn z hz j
      ((mem_outsideHookFinset u z j).mp hj)
      ((mem_outsideHookFinset u z (j + 4)).mp hj4)
  · intro j hj hj4
    exact outside_no_distance_four_hooks u hu hn w hw j
      ((mem_outsideHookFinset u w j).mp hj)
      ((mem_outsideHookFinset u w (j + 4)).mp hj4)
  · intro j hj
    exact outside_hook_indices_same_parity u hu c z j i
      ((mem_outsideHookFinset u z j).mp hj) hzi
  · intro j hj
    exact (shared_outside_hook_parity u hu c z q w hzq hqw i j hzi
      ((mem_outsideHookFinset u w j).mp hj)).symm
  · intro j hj hj6
    exact no_shared_distance_six_hooks u hu hn z q w hz hq hw hzw hzq hqw j
      ((mem_outsideHookFinset u z j).mp hj)
      ((mem_outsideHookFinset u w (j + 6)).mp hj6)
  · intro j hj hj10
    exact no_shared_distance_ten_hooks u hu hn z q w hz hq hw hzw hzq hqw j
      ((mem_outsideHookFinset u z j).mp hj)
      ((mem_outsideHookFinset u w (j + 10)).mp hj10)
  · exact hh

noncomputable def actualOutsideNeighbors [Fintype V] (G : SimpleGraph V)
    (u : Fin 16 → V) (z : V) : Finset V :=
  G.neighborFinset z \ Finset.univ.image u

theorem mem_actualOutsideNeighbors [Fintype V] (u : Fin 16 → V) (z q : V) :
    q ∈ actualOutsideNeighbors G u z ↔ G.Adj z q ∧ q ∉ Set.range u := by
  simp only [actualOutsideNeighbors, Finset.mem_sdiff, Finset.mem_image,
    Finset.mem_univ, true_and, Set.mem_range, G.mem_neighborFinset]

theorem high_outside_neighborhoods_disjoint [Fintype V] (hb : G.IsBipartite)
    (u : Fin 16 → V) (hu : IsCycleSixteen G u) (hn : NoFourteenCycle G)
    (z w : V) (hz : z ∉ Set.range u) (hw : w ∉ Set.range u) (hzw : z ≠ w)
    (h3z : 3 ≤ (outsideHookFinset G u z).card)
    (h3w : 3 ≤ (outsideHookFinset G u w).card) :
    Disjoint (actualOutsideNeighbors G u z) (actualOutsideNeighbors G u w) := by
  apply Finset.disjoint_left.mpr
  intro q hqz hqw
  have hqz' := (mem_actualOutsideNeighbors u z q).mp hqz
  have hqw' := (mem_actualOutsideNeighbors u w q).mp hqw
  have hh := actual_high_shared_hook_capacity hb u hu hn z q w hz hqz'.2 hw
    hzw hqz'.1 hqw'.1.symm h3z
  omega

theorem actual_quad_shared_has_zero_hooks (hb : G.IsBipartite)
    (u : Fin 16 → V) (hu : IsCycleSixteen G u) (hn : NoFourteenCycle G)
    (z q w : V) (hz : z ∉ Set.range u) (hq : q ∉ Set.range u)
    (hw : w ∉ Set.range u) (hzw : z ≠ w) (hzq : G.Adj z q) (hqw : G.Adj q w)
    (hh : (outsideHookFinset G u z).card = 4) :
    (outsideHookFinset G u w).card = 0 := by
  exact (actual_high_shared_hook_capacity hb u hu hn z q w hz hq hw hzw hzq hqw
    (by omega)).2 (by omega)

end TaskH.Seven.BP

#print axioms TaskH.Seven.BP.shared_outside_hook_parity
#print axioms TaskH.Seven.BP.actual_high_shared_hook_capacity
#print axioms TaskH.Seven.BP.actualOutsideNeighbors
#print axioms TaskH.Seven.BP.mem_actualOutsideNeighbors
#print axioms TaskH.Seven.BP.high_outside_neighborhoods_disjoint
#print axioms TaskH.Seven.BP.actual_quad_shared_has_zero_hooks
