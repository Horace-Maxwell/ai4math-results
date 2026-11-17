import Research.TaskH.Six.SixDegreeTenSplitWeight

/-! Actual paths separate the outside pools of the two four-leaf stars. -/

set_option autoImplicit false

universe u

namespace TaskH.Six

open SimpleGraph
open scoped Classical

variable {V : Type u} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]
variable {v : V} {c : (G.induce {x | x ≠ v}).Coloring (Fin 6)}

def degreeTenSplitMixedWord (ε : Fin 4 → Fin 2) (i j k : Fin 4) :
    Fin 5 → Option DegreeTenNeighborIndex :=
  ![some (Sum.inr (i, ε i)), none, some (Sum.inr (j, ε j + 1)),
    some (Sum.inl 1), some (Sum.inr (k, ε k + 1))]

theorem degreeTenSplitMixedWord_injective (ε : Fin 4 → Fin 2) (i j k : Fin 4)
    (hjk : j ≠ k) : Function.Injective (degreeTenSplitMixedWord ε i j k) := by
  have hnext : ∀ a : Fin 4, ε a ≠ ε a + 1 := by
    intro a
    generalize h : ε a = t
    fin_cases t <;> decide +kernel
  have hij' : ((i, ε i) : Fin 4 × Fin 2) ≠ (j, ε j + 1) := by
    intro h
    have hi : i = j := congrArg Prod.fst h
    subst i
    exact hnext j (congrArg Prod.snd h)
  have hik' : ((i, ε i) : Fin 4 × Fin 2) ≠ (k, ε k + 1) := by
    intro h
    have hi : i = k := congrArg Prod.fst h
    subst i
    exact hnext k (congrArg Prod.snd h)
  have hjk' : ((j, ε j + 1) : Fin 4 × Fin 2) ≠ (k, ε k + 1) :=
    fun h => hjk (congrArg Prod.fst h)
  intro b d he
  fin_cases b <;> fin_cases d
  all_goals first
    | rfl
    | exact False.elim (hij' (Sum.inr.inj (Option.some.inj he)))
    | exact False.elim (hij' (Sum.inr.inj (Option.some.inj he.symm)))
    | exact False.elim (hik' (Sum.inr.inj (Option.some.inj he)))
    | exact False.elim (hik' (Sum.inr.inj (Option.some.inj he.symm)))
    | exact False.elim (hjk' (Sum.inr.inj (Option.some.inj he)))
    | exact False.elim (hjk' (Sum.inr.inj (Option.some.inj he.symm)))
    | cases he

theorem degreeTen_split_mixed_outside_impossible (hr : RainbowSixCycles G)
    (F : DegreeTenColorFrame v c) (ε : Fin 4 → Fin 2)
    (hSplit : ∀ i, DegreeTenSplitAt F i (ε i)) (z : V)
    (hz : z ∈ degreeTenOutside G v) (i j : Fin 4)
    (hi : G.Adj z (degreeTenSplitLeaf F ε 0 i))
    (hj : G.Adj z (degreeTenSplitLeaf F ε 1 j)) : False := by
  have hz' := (mem_degreeTenOutside_iff z).mp hz
  have hi' : G.Adj z (degreeTenPair F i (ε i)).val := by
    simpa only [degreeTenSplitLeaf, add_zero] using hi
  have hpaths : ∀ k : Fin 4, j ≠ k →
      Function.Injective (fun d => c ⟨degreeTenExteriorVertex F z
        (degreeTenSplitMixedWord ε i j k d),
        degreeTenExteriorVertex_ne_root F z hz' (degreeTenSplitMixedWord ε i j k d)⟩) := by
    intro k hjk
    exact degreeTen_exterior_path_colors_injective hr F z hz'
      (degreeTenSplitMixedWord ε i j k) (degreeTenSplitMixedWord_injective ε i j k hjk)
      (degreeTenPair F i (ε i)).property hi'.symm hj (hSplit j).2.2.1.symm
      (hSplit k).2.2.1 (degreeTenPair F k (ε k + 1)).property.symm
  by_cases hij : i = j
  · subst j
    obtain ⟨k, hki, _⟩ := finFour_exists_ne_two i i
    have hcolor : neighborColor v c (degreeTenPair F i (ε i)) =
        neighborColor v c (degreeTenPair F i (ε i + 1)) :=
      (degreeTenPair_color F i (ε i)).trans (degreeTenPair_color F i (ε i + 1)).symm
    exact (by decide : (0 : Fin 5) ≠ 2) (hpaths k (fun he => hki he.symm) (a₁ := 0) (a₂ := 2) hcolor)
  · have hcolor : neighborColor v c (degreeTenPair F i (ε i)) =
        neighborColor v c (degreeTenPair F i (ε i + 1)) :=
      (degreeTenPair_color F i (ε i)).trans (degreeTenPair_color F i (ε i + 1)).symm
    exact (by decide : (0 : Fin 5) ≠ 4) (hpaths i (fun he => hij he.symm) (a₁ := 0) (a₂ := 4) hcolor)

theorem degreeTen_split_pools_disjoint (hr : RainbowSixCycles G)
    (F : DegreeTenColorFrame v c) (ε : Fin 4 → Fin 2)
    (hSplit : ∀ i, DegreeTenSplitAt F i (ε i)) :
    Disjoint (degreeTenSplitPool F ε 0) (degreeTenSplitPool F ε 1) := by
  apply Finset.disjoint_left.mpr
  intro z hzP hzQ
  obtain ⟨hz, hLP⟩ := Finset.mem_filter.mp hzP
  obtain ⟨_hz', hLQ⟩ := Finset.mem_filter.mp hzQ
  obtain ⟨i, hi⟩ := hLP
  obtain ⟨j, hj⟩ := hLQ
  exact degreeTen_split_mixed_outside_impossible hr F ε hSplit z hz i j
    ((mem_fourLeafLabels_iff _ z i).mp hi) ((mem_fourLeafLabels_iff _ z j).mp hj)

end TaskH.Six

#print axioms TaskH.Six.degreeTenSplitMixedWord
#print axioms TaskH.Six.degreeTenSplitMixedWord_injective
#print axioms TaskH.Six.degreeTen_split_mixed_outside_impossible
#print axioms TaskH.Six.degreeTen_split_pools_disjoint
