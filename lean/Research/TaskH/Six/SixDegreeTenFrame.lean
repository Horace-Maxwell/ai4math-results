import Research.TaskH.Six.SixDegreeTenCenterCoverage

/-!
An actual enumeration of all ten neighbors, with two singleton vertices and
four two-vertex fibers, constructed from the original coloring. The frame is
finite data derived from criticality, S, R, K4-freeness and degree ten. Its
coverage fields are proved by actual following cycles, never assumed.
-/

set_option autoImplicit false

universe u

namespace TaskH.Six

open SimpleGraph _root_.TaskH.Challenge
open scoped Classical

variable {V : Type u} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]

structure DegreeTenColorFrame (v : V)
    (c : (G.induce {x | x ≠ v}).Coloring (Fin 6)) where
  singletonColors : ↥(singletonNeighborColors v c) ≃ Fin 2
  doubleColors : ↥((singletonNeighborColors v c)ᶜ) ≃ Fin 4
  pairFibers : ∀ i : Fin 4,
    ↥(neighborColorFiber v c (doubleColors.symm i).val) ≃ Fin 2

noncomputable def degreeTenColorFrame
    (hcrit : IsCriticalPlus 6 G) (hs : ShortSixCycles G) (hr : RainbowSixCycles G)
    (hfree : G.CliqueFree 4) (v : V)
    (c : (G.induce {x | x ≠ v}).Coloring (Fin 6)) (hv : G.degree v = 10) :
    DegreeTenColorFrame v c := by
  classical
  have hS := degreeTen_singleton_colors_card hcrit hs hr hfree v c hv
  have hD : ((singletonNeighborColors v c)ᶜ).card = 4 := by
    rw [Finset.card_compl, hS]
    norm_num
  let eS := Finset.equivFinOfCardEq hS
  let eD := Finset.equivFinOfCardEq hD
  refine ⟨eS, eD, ?_⟩
  intro i
  apply Finset.equivFinOfCardEq
  have hk : (eD.symm i).val ∉ singletonNeighborColors v c :=
    Finset.mem_compl.mp (eD.symm i).property
  rw [degreeTen_neighborColorFiber_card hcrit hs hr hfree v c hv, ite_eq_right hk]

noncomputable def degreeTenCenter {v : V}
    {c : (G.induce {x | x ≠ v}).Coloring (Fin 6)}
    (F : DegreeTenColorFrame v c) (j : Fin 2) : G.neighborSet v :=
  singletonNeighbor v c (F.singletonColors.symm j)

noncomputable def degreeTenPair {v : V}
    {c : (G.induce {x | x ≠ v}).Coloring (Fin 6)}
    (F : DegreeTenColorFrame v c) (i : Fin 4) (j : Fin 2) : G.neighborSet v :=
  ((F.pairFibers i).symm j).val

theorem degreeTenCenter_color {v : V}
    {c : (G.induce {x | x ≠ v}).Coloring (Fin 6)}
    (F : DegreeTenColorFrame v c) (j : Fin 2) :
    neighborColor v c (degreeTenCenter F j) = (F.singletonColors.symm j).val :=
  singletonNeighbor_color v c (F.singletonColors.symm j)

theorem degreeTenPair_color {v : V}
    {c : (G.induce {x | x ≠ v}).Coloring (Fin 6)}
    (F : DegreeTenColorFrame v c) (i : Fin 4) (j : Fin 2) :
    neighborColor v c (degreeTenPair F i j) = (F.doubleColors.symm i).val :=
  (mem_neighborColorFiber v c _ _).mp ((F.pairFibers i).symm j).property

theorem degreeTenCenter_val_injective {v : V}
    {c : (G.induce {x | x ≠ v}).Coloring (Fin 6)}
    (F : DegreeTenColorFrame v c) :
    Function.Injective (fun j => (degreeTenCenter F j).val) :=
  (degreeTenSingletonNeighbor_val_injective v c).comp F.singletonColors.symm.injective

theorem degreeTenPair_injective {v : V}
    {c : (G.induce {x | x ≠ v}).Coloring (Fin 6)}
    (F : DegreeTenColorFrame v c) (i : Fin 4) :
    Function.Injective (degreeTenPair F i) :=
  Subtype.val_injective.comp (F.pairFibers i).symm.injective

theorem degreeTenPair_all_val_injective {v : V}
    {c : (G.induce {x | x ≠ v}).Coloring (Fin 6)}
    (F : DegreeTenColorFrame v c) :
    Function.Injective (fun ij : Fin 4 × Fin 2 => (degreeTenPair F ij.1 ij.2).val) := by
  rintro ⟨i, j⟩ ⟨k, l⟩ he
  have hsub : degreeTenPair F i j = degreeTenPair F k l := Subtype.ext he
  have hcolor := congrArg (neighborColor v c) hsub
  rw [degreeTenPair_color, degreeTenPair_color] at hcolor
  have hik : i = k := F.doubleColors.symm.injective (Subtype.ext hcolor)
  subst k
  have hjl : j = l := degreeTenPair_injective F i hsub
  exact Prod.ext rfl hjl

theorem degreeTenCenter_pair_ne {v : V}
    {c : (G.induce {x | x ≠ v}).Coloring (Fin 6)}
    (F : DegreeTenColorFrame v c) (j : Fin 2) (i : Fin 4) (k : Fin 2) :
    (degreeTenCenter F j).val ≠ (degreeTenPair F i k).val := by
  intro he
  have hsub : degreeTenCenter F j = degreeTenPair F i k := Subtype.ext he
  have hcolor := congrArg (neighborColor v c) hsub
  rw [degreeTenCenter_color, degreeTenPair_color] at hcolor
  have hS := (F.singletonColors.symm j).property
  have hnot := Finset.mem_compl.mp (F.doubleColors.symm i).property
  exact hnot (hcolor ▸ hS)

theorem degreeTenCenter_exhausts_singleton {v : V}
    {c : (G.induce {x | x ≠ v}).Coloring (Fin 6)}
    (F : DegreeTenColorFrame v c) (z : G.neighborSet v)
    (hz : neighborColor v c z ∈ singletonNeighborColors v c) :
    ∃ j : Fin 2, degreeTenCenter F j = z := by
  let s : ↥(singletonNeighborColors v c) := ⟨neighborColor v c z, hz⟩
  refine ⟨F.singletonColors s, ?_⟩
  change singletonNeighbor v c (F.singletonColors.symm (F.singletonColors s)) = z
  rw [F.singletonColors.symm_apply_apply]
  exact (singletonNeighbor_eq_of_color v c s z rfl).symm

theorem degreeTenPair_exhausts_double {v : V}
    {c : (G.induce {x | x ≠ v}).Coloring (Fin 6)}
    (F : DegreeTenColorFrame v c) (z : G.neighborSet v)
    (hz : neighborColor v c z ∉ singletonNeighborColors v c) :
    ∃ i : Fin 4, ∃ j : Fin 2, degreeTenPair F i j = z := by
  classical
  let d : ↥((singletonNeighborColors v c)ᶜ) :=
    ⟨neighborColor v c z, Finset.mem_compl.mpr hz⟩
  let i : Fin 4 := F.doubleColors d
  have hcolor : (F.doubleColors.symm i).val = neighborColor v c z :=
    congrArg Subtype.val (F.doubleColors.symm_apply_apply d)
  let zf : ↥(neighborColorFiber v c (F.doubleColors.symm i).val) :=
    ⟨z, (mem_neighborColorFiber v c _ z).mpr hcolor.symm⟩
  refine ⟨i, F.pairFibers i zf, ?_⟩
  change ((F.pairFibers i).symm (F.pairFibers i zf)).val = z
  rw [(F.pairFibers i).symm_apply_apply]

theorem degreeTenFrame_neighbor_exhaustion {v : V}
    {c : (G.induce {x | x ≠ v}).Coloring (Fin 6)}
    (F : DegreeTenColorFrame v c) (z : G.neighborSet v) :
    (∃ j : Fin 2, degreeTenCenter F j = z) ∨
      ∃ i : Fin 4, ∃ j : Fin 2, degreeTenPair F i j = z := by
  classical
  by_cases hz : neighborColor v c z ∈ singletonNeighborColors v c
  · exact Or.inl (degreeTenCenter_exhausts_singleton F z hz)
  · exact Or.inr (degreeTenPair_exhausts_double F z hz)

theorem degreeTenPair_same_color_not_adj {v : V}
    {c : (G.induce {x | x ≠ v}).Coloring (Fin 6)}
    (F : DegreeTenColorFrame v c) (i : Fin 4) (j k : Fin 2) :
    ¬ G.Adj (degreeTenPair F i j).val (degreeTenPair F i k).val := by
  intro hadj
  have ha : (G.induce {x | x ≠ v}).Adj
      ⟨(degreeTenPair F i j).val, (degreeTenPair F i j).property.ne.symm⟩
      ⟨(degreeTenPair F i k).val, (degreeTenPair F i k).property.ne.symm⟩ := hadj
  exact (c.valid ha) ((degreeTenPair_color F i j).trans (degreeTenPair_color F i k).symm)

theorem degreeTenCenter_covers_each_pair
    (hcrit : IsCriticalPlus 6 G) (hs : ShortSixCycles G) (hr : RainbowSixCycles G)
    {v : V} {c : (G.induce {x | x ≠ v}).Coloring (Fin 6)}
    (F : DegreeTenColorFrame v c) (j : Fin 2) (i : Fin 4) :
    ∃ k : Fin 2, G.Adj (degreeTenCenter F j).val (degreeTenPair F i k).val := by
  classical
  let s := F.singletonColors.symm (j + 1)
  let t := F.singletonColors.symm j
  have hst : s ≠ t := by
    apply F.singletonColors.symm.injective.ne
    fin_cases j <;> decide +kernel
  have hpairnot := Finset.mem_compl.mp (F.doubleColors.symm i).property
  have hsk : s.val ≠ (F.doubleColors.symm i).val := by
    intro he
    exact hpairnot (he ▸ s.property)
  have htk : t.val ≠ (F.doubleColors.symm i).val := by
    intro he
    exact hpairnot (he ▸ t.property)
  obtain ⟨z, hzcolor, hzadj⟩ := singleton_center_covers_other_color hcrit hs hr
    v c s t hst (F.doubleColors.symm i).val hsk htk
  let zf : ↥(neighborColorFiber v c (F.doubleColors.symm i).val) :=
    ⟨z, (mem_neighborColorFiber v c _ z).mpr hzcolor⟩
  refine ⟨F.pairFibers i zf, ?_⟩
  have he : degreeTenPair F i (F.pairFibers i zf) = z := by
    change ((F.pairFibers i).symm (F.pairFibers i zf)).val = z
    rw [(F.pairFibers i).symm_apply_apply]
  rw [he]
  exact hzadj.symm

end TaskH.Six

#print axioms TaskH.Six.DegreeTenColorFrame
#print axioms TaskH.Six.DegreeTenColorFrame.singletonColors
#print axioms TaskH.Six.DegreeTenColorFrame.doubleColors
#print axioms TaskH.Six.DegreeTenColorFrame.pairFibers
#print axioms TaskH.Six.degreeTenColorFrame
#print axioms TaskH.Six.degreeTenCenter
#print axioms TaskH.Six.degreeTenPair
#print axioms TaskH.Six.degreeTenCenter_color
#print axioms TaskH.Six.degreeTenPair_color
#print axioms TaskH.Six.degreeTenCenter_val_injective
#print axioms TaskH.Six.degreeTenPair_injective
#print axioms TaskH.Six.degreeTenPair_all_val_injective
#print axioms TaskH.Six.degreeTenCenter_pair_ne
#print axioms TaskH.Six.degreeTenCenter_exhausts_singleton
#print axioms TaskH.Six.degreeTenPair_exhausts_double
#print axioms TaskH.Six.degreeTenFrame_neighbor_exhaustion
#print axioms TaskH.Six.degreeTenPair_same_color_not_adj
#print axioms TaskH.Six.degreeTenCenter_covers_each_pair
