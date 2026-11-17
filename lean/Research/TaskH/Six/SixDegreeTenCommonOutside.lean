import Research.TaskH.Six.SixDegreeTenExteriorWords

/-!
The common-fiber alternative has two disjoint actual outside-neighbor pools.
No outside point meets two common vertices. All exclusions use genuine
four-edge paths and the one fixed coloring of the root-deleted graph.
-/

set_option autoImplicit false

universe u

namespace TaskH.Six

open SimpleGraph
open scoped Classical

variable {V : Type u} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]
variable {v : V} {c : (G.induce {x | x ≠ v}).Coloring (Fin 6)}

noncomputable def degreeTenClosedSet (G : SimpleGraph V) [DecidableRel G.Adj]
    (v : V) : Finset V := insert v (G.neighborFinset v)

noncomputable def degreeTenOutside (G : SimpleGraph V) [DecidableRel G.Adj]
    (v : V) : Finset V := (degreeTenClosedSet G v)ᶜ

theorem mem_degreeTenOutside_iff (z : V) :
    z ∈ degreeTenOutside G v ↔ z ≠ v ∧ ¬ G.Adj v z := by
  simp only [degreeTenOutside, Finset.mem_compl, degreeTenClosedSet,
    Finset.mem_insert, G.mem_neighborFinset, not_or]

theorem finFour_exists_ne_two (i j : Fin 4) :
    ∃ k : Fin 4, k ≠ i ∧ k ≠ j := by
  revert i j
  decide +kernel

theorem degreeTen_common_center_adj (F : DegreeTenColorFrame v c)
    (r : Fin 4 → Fin 2) (hCommon : ∀ i, DegreeTenCommonAt F i (r i))
    (a : Fin 2) (i : Fin 4) :
    G.Adj (degreeTenCenter F a).val (degreeTenPair F i (r i)).val := by
  fin_cases a
  · exact (hCommon i).1
  · exact (hCommon i).2.1

theorem degreeTen_common_fork_colors_ne (hr : RainbowSixCycles G)
    (F : DegreeTenColorFrame v c) (r : Fin 4 → Fin 2)
    (hCommon : ∀ i, DegreeTenCommonAt F i (r i)) (z : V)
    (hz : z ≠ v ∧ ¬ G.Adj v z) (i j k : Fin 4) (a : Fin 2)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hi : G.Adj z (degreeTenPair F i (r i)).val)
    (hj : G.Adj z (degreeTenPair F j (r j)).val) :
    c ⟨z, hz.1⟩ ≠ neighborColor v c (degreeTenPair F k (r k)) ∧
      c ⟨z, hz.1⟩ ≠ neighborColor v c (degreeTenCenter F a) := by
  let w := degreeTenCommonForkWord i j k (r i) (r j) (r k) a
  have hwi : Function.Injective w :=
    degreeTenCommonForkWord_injective i j k _ _ _ a hij hik hjk
  have hcolors := degreeTen_exterior_path_colors_injective hr F z hz w hwi
    (degreeTenPair F i (r i)).property hi.symm hj
    (degreeTen_common_center_adj F r hCommon a j).symm
    (degreeTen_common_center_adj F r hCommon a k)
    (degreeTenPair F k (r k)).property.symm
  constructor
  · intro he
    exact (by decide : (1 : Fin 5) ≠ 4) (hcolors (a₁ := 1) (a₂ := 4) he)
  · intro he
    exact (by decide : (1 : Fin 5) ≠ 3) (hcolors (a₁ := 1) (a₂ := 3) he)

theorem degreeTen_common_outside_hook_unique (hr : RainbowSixCycles G)
    (F : DegreeTenColorFrame v c) (r : Fin 4 → Fin 2)
    (hCommon : ∀ i, DegreeTenCommonAt F i (r i)) (z : V)
    (hz : z ∈ degreeTenOutside G v) (i j : Fin 4)
    (hi : G.Adj z (degreeTenPair F i (r i)).val)
    (hj : G.Adj z (degreeTenPair F j (r j)).val) : i = j := by
  by_contra hij
  have hz' := (mem_degreeTenOutside_iff z).mp hz
  obtain ⟨a, hcolor⟩ | ⟨k, hcolor⟩ :=
    degreeTenFrame_deleted_color_exhaustion F r ⟨z, hz'.1⟩
  · obtain ⟨k, hki, hkj⟩ := finFour_exists_ne_two i j
    exact (degreeTen_common_fork_colors_ne hr F r hCommon z hz'
      i j k a hij (fun he => hki he.symm) (fun he => hkj he.symm) hi hj).2 hcolor
  · by_cases hki : k = i
    · subst k
      have hp : c ⟨z, hz'.1⟩ ≠ neighborColor v c (degreeTenPair F i (r i)) := c.valid hi
      exact hp hcolor
    · by_cases hkj : k = j
      · subst k
        have hp : c ⟨z, hz'.1⟩ ≠ neighborColor v c (degreeTenPair F j (r j)) := c.valid hj
        exact hp hcolor
      · exact (degreeTen_common_fork_colors_ne hr F r hCommon z hz'
          i j k 0 hij (fun he => hki he.symm) (fun he => hkj he.symm) hi hj).1 hcolor

theorem degreeTen_common_mixed_outside_impossible (hr : RainbowSixCycles G)
    (F : DegreeTenColorFrame v c) (r : Fin 4 → Fin 2)
    (hCommon : ∀ i, DegreeTenCommonAt F i (r i)) (z : V)
    (hz : z ∈ degreeTenOutside G v) (i j : Fin 4)
    (hi : G.Adj z (degreeTenPair F i (r i)).val)
    (hj : G.Adj z (degreeTenPair F j (r j + 1)).val) : False := by
  have hz' := (mem_degreeTenOutside_iff z).mp hz
  have hpaths : ∀ k : Fin 4, k ≠ i →
      Function.Injective (fun d => c ⟨degreeTenExteriorVertex F z
        (degreeTenCommonMixedWord r k i j d),
        degreeTenExteriorVertex_ne_root F z hz' (degreeTenCommonMixedWord r k i j d)⟩) := by
    intro k hki
    exact degreeTen_exterior_path_colors_injective hr F z hz'
      (degreeTenCommonMixedWord r k i j) (degreeTenCommonMixedWord_injective r k i j hki)
      (degreeTenPair F k (r k)).property (hCommon k).1.symm (hCommon i).1 hi.symm hj
      (degreeTenPair F j (r j + 1)).property.symm
  by_cases hij : i = j
  · subst j
    obtain ⟨k, hki, _⟩ := finFour_exists_ne_two i i
    have hcolor : neighborColor v c (degreeTenPair F i (r i)) =
        neighborColor v c (degreeTenPair F i (r i + 1)) :=
      (degreeTenPair_color F i (r i)).trans (degreeTenPair_color F i (r i + 1)).symm
    exact (by decide : (2 : Fin 5) ≠ 4) (hpaths k hki (a₁ := 2) (a₂ := 4) hcolor)
  · have hcolor : neighborColor v c (degreeTenPair F j (r j)) =
        neighborColor v c (degreeTenPair F j (r j + 1)) :=
      (degreeTenPair_color F j (r j)).trans (degreeTenPair_color F j (r j + 1)).symm
    exact (by decide : (0 : Fin 5) ≠ 4) (hpaths j (fun he => hij he.symm) (a₁ := 0) (a₂ := 4) hcolor)

noncomputable def degreeTenCommonPool (F : DegreeTenColorFrame v c)
    (r : Fin 4 → Fin 2) : Finset V :=
  (degreeTenOutside G v).filter (fun z => ∃ i : Fin 4,
    G.Adj z (degreeTenPair F i (r i)).val)

noncomputable def degreeTenOtherPool (F : DegreeTenColorFrame v c)
    (r : Fin 4 → Fin 2) : Finset V :=
  (degreeTenOutside G v).filter (fun z => ∃ i : Fin 4,
    G.Adj z (degreeTenPair F i (r i + 1)).val)

theorem degreeTen_common_other_pool_disjoint (hr : RainbowSixCycles G)
    (F : DegreeTenColorFrame v c) (r : Fin 4 → Fin 2)
    (hCommon : ∀ i, DegreeTenCommonAt F i (r i)) :
    Disjoint (degreeTenCommonPool F r) (degreeTenOtherPool F r) := by
  apply Finset.disjoint_left.mpr
  intro z hzR hzS
  obtain ⟨hz, i, hi⟩ := Finset.mem_filter.mp hzR
  obtain ⟨_hz', j, hj⟩ := Finset.mem_filter.mp hzS
  exact degreeTen_common_mixed_outside_impossible hr F r hCommon z hz i j hi hj

end TaskH.Six

#print axioms TaskH.Six.degreeTenClosedSet
#print axioms TaskH.Six.degreeTenOutside
#print axioms TaskH.Six.mem_degreeTenOutside_iff
#print axioms TaskH.Six.finFour_exists_ne_two
#print axioms TaskH.Six.degreeTen_common_center_adj
#print axioms TaskH.Six.degreeTen_common_fork_colors_ne
#print axioms TaskH.Six.degreeTen_common_outside_hook_unique
#print axioms TaskH.Six.degreeTen_common_mixed_outside_impossible
#print axioms TaskH.Six.degreeTenCommonPool
#print axioms TaskH.Six.degreeTenOtherPool
#print axioms TaskH.Six.degreeTen_common_other_pool_disjoint
