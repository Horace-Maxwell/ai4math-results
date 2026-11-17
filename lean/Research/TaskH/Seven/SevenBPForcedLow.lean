import Research.TaskH.Seven.SevenBPSharedAttachments

/-! An actual high-hook outside vertex forces four actual low-hook
vertices on its own side through a real outside neighbor. -/

set_option autoImplicit false

universe u

namespace TaskH.Seven.BP

open SimpleGraph
open scoped Classical

variable {V : Type u} [Fintype V] {G : SimpleGraph V}

theorem outside_neighbors_high_count_le_one (hb : G.IsBipartite)
    (u : Fin 16 → V) (hu : IsCycleSixteen G u) (hn : NoFourteenCycle G)
    (z : V) (hz : z ∉ Set.range u) :
    ((actualOutsideNeighbors G u z).filter
      (fun q => 3 ≤ (outsideHookFinset G u q).card)).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro q hq w hw
  obtain ⟨hqN, hq3⟩ := Finset.mem_filter.mp hq
  obtain ⟨hwN, hw3⟩ := Finset.mem_filter.mp hw
  have hq' := (mem_actualOutsideNeighbors u z q).mp hqN
  have hw' := (mem_actualOutsideNeighbors u z w).mp hwN
  by_contra hqw
  have hh := actual_high_shared_hook_capacity hb u hu hn q z w hq'.2 hz hw'.2
    hqw hq'.1.symm hw'.1 hq3
  omega

theorem high_has_low_outside_neighbor (hb : G.IsBipartite)
    (u : Fin 16 → V) (hu : IsCycleSixteen G u) (hn : NoFourteenCycle G)
    (z : V) (hz : z ∉ Set.range u) (hd : 7 ≤ G.degree z) :
    ∃ q ∈ actualOutsideNeighbors G u z, (outsideHookFinset G u q).card ≤ 2 := by
  let N := actualOutsideNeighbors G u z
  let T := N.filter (fun q => 3 ≤ (outsideHookFinset G u q).card)
  have hn3 : 3 ≤ N.card := outside_degree_ge_three hb u hu hn z hz hd
  have ht1 : T.card ≤ 1 := outside_neighbors_high_count_le_one hb u hu hn z hz
  obtain ⟨q, hqN, hqT⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (show T.card < N.card by omega)
  refine ⟨q, hqN, ?_⟩
  have hnt : ¬ 3 ≤ (outsideHookFinset G u q).card := by
    intro h3
    exact hqT (Finset.mem_filter.mpr ⟨hqN, h3⟩)
  omega

theorem high_forces_four_low_actual (hb : G.IsBipartite)
    (u : Fin 16 → V) (hu : IsCycleSixteen G u) (hn : NoFourteenCycle G)
    (hd : ∀ v : V, 7 ≤ G.degree v)
    (z : V) (hz : z ∉ Set.range u) (h3z : 3 ≤ (outsideHookFinset G u z).card) :
    ∃ q : V, G.Adj z q ∧ q ∉ Set.range u ∧
      4 ≤ (actualOutsideNeighbors G u q \ {z}).card ∧
      ∀ w ∈ actualOutsideNeighbors G u q \ {z},
        (outsideHookFinset G u w).card ≤ 1 := by
  obtain ⟨q, hqN, hq2⟩ := high_has_low_outside_neighbor hb u hu hn z hz (hd z)
  have hq' := (mem_actualOutsideNeighbors u z q).mp hqN
  have hN5 : 5 ≤ (actualOutsideNeighbors G u q).card :=
    outside_degree_ge_five_of_at_most_two_hooks u hu.1 q hq2 (hd q)
  have hzN : z ∈ actualOutsideNeighbors G u q :=
    (mem_actualOutsideNeighbors u q z).mpr ⟨hq'.1.symm, hz⟩
  have hcard : (actualOutsideNeighbors G u q \ {z}).card + 1 =
      (actualOutsideNeighbors G u q).card := by
    simpa only [Finset.sdiff_singleton_eq_erase] using
      Finset.card_erase_add_one hzN
  refine ⟨q, hq'.1, hq'.2, by omega, ?_⟩
  intro w hw
  obtain ⟨hwN, hwe⟩ := Finset.mem_sdiff.mp hw
  have hw' := (mem_actualOutsideNeighbors u q w).mp hwN
  have hzw : z ≠ w := by
    intro he
    exact hwe (Finset.mem_singleton.mpr he.symm)
  exact (actual_high_shared_hook_capacity hb u hu hn z q w hz hq'.2 hw'.2
    hzw hq'.1 hw'.1 h3z).1

theorem forced_low_same_color (c : G.Coloring Bool) (z q w : V)
    (hzq : G.Adj z q) (hqw : G.Adj q w) : c z = c w := by
  let dec : DecidableEq V := (Fintype.equivFin V).decidableEq
  have hcases : z = q ∨ z ≠ q := by
    cases dec z q with
    | isTrue he => exact Or.inl he
    | isFalse hn => exact Or.inr hn
  rcases hcases with he | _hne
  · exact (hzq.ne he).elim
  have h0 := c.valid hzq
  have h1 := c.valid hqw
  cases hz : c z <;> cases hq : c q <;> cases hw : c w <;> simp_all

end TaskH.Seven.BP

#print axioms TaskH.Seven.BP.outside_neighbors_high_count_le_one
#print axioms TaskH.Seven.BP.high_has_low_outside_neighbor
#print axioms TaskH.Seven.BP.high_forces_four_low_actual
#print axioms TaskH.Seven.BP.forced_low_same_color
