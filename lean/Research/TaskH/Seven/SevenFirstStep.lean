import Research.TaskH.Seven.SingletonClique

/-! Prescribed first two colors transport an actual singleton following
circle to a true root neighbor of the requested original deleted color. -/

set_option autoImplicit false
universe u
namespace TaskH.Seven
open SimpleGraph _root_.TaskH.Challenge
open scoped Classical
variable {V : Type u} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem exists_order_zero_one_two (i eta j : Fin 7)
    (hie : i ≠ eta) (hij : i ≠ j) (hej : eta ≠ j) :
    ∃ π : Equiv.Perm (Fin 7), π i = 0 ∧ π eta = 1 ∧ π j = 2 := by
  classical
  obtain ⟨ρ, hρi, hρe⟩ := exists_order_zero_one i eta hie
  have hj0 : ρ j ≠ 0 := by
    intro he
    exact hij (ρ.injective (hρi.trans he.symm))
  have hj1 : ρ j ≠ 1 := by
    intro he
    exact hej (ρ.injective (hρe.trans he.symm))
  let π := ρ.trans (Equiv.swap (ρ j) 2)
  refine ⟨π, ?_, ?_, ?_⟩
  · change Equiv.swap (ρ j) 2 (ρ i) = 0
    rw [hρi]
    exact Equiv.swap_apply_of_ne_of_ne (Ne.symm hj0) (by decide)
  · change Equiv.swap (ρ j) 2 (ρ eta) = 1
    rw [hρe]
    exact Equiv.swap_apply_of_ne_of_ne (Ne.symm hj1) (by decide)
  · change Equiv.swap (ρ j) 2 (ρ j) = 2
    exact Equiv.swap_apply_left _ _

theorem singleton_following_first_step
    (hcrit : IsCriticalPlus 7 G) (hs : ShortSevenCycles G) (hr : RainbowSevenCycles G)
    (v : V) (c : (G.induce {x | x ≠ v}).Coloring (Fin 7))
    (i j : ↥(singletonNeighborColors v c)) (hij : i ≠ j)
    (eta : Fin 7) (hie : i.val ≠ eta) (hej : eta ≠ j.val) :
    ∃ z : G.neighborSet v, neighborColor v c z = eta ∧
      G.Adj z.val (singletonNeighbor v c j).val := by
  classical
  have hijval : i.val ≠ j.val := fun he => hij (Subtype.ext he)
  obtain ⟨π, hπi, hπe, hπj⟩ := exists_order_zero_one_two i.val eta j.val hie hijval hej
  obtain ⟨p, hp, hlen, hf, _havoid⟩ := singleton_through_ordered_cycle hcrit hs v c i π
  have hjmem := singleton_cycle_contains_other_neighbor hr v c i j hij π p hp hlen hf
  have h1 := follows_getVert p (fun z => π (singletonEdgeColoring v c i z))
    (finRotate 7) hf 1 (by omega)
  rw [singletonEdgeColoring_base, hπi, pow_one] at h1
  have h1' : π (singletonEdgeColoring v c i (p.getVert 1)) = 1 :=
    h1.trans (by decide +kernel)
  have h2 := follows_getVert p (fun z => π (singletonEdgeColoring v c i z))
    (finRotate 7) hf 2 (by omega)
  rw [singletonEdgeColoring_base, hπi] at h2
  have h2' : π (singletonEdgeColoring v c i (p.getVert 2)) = 2 :=
    h2.trans (by decide +kernel)
  have hjcolor : π (singletonEdgeColoring v c i (singletonNeighbor v c j).val) = 2 := by
    rw [singletonEdgeColoring_outside v c i _ (singletonNeighbor v c j).property.ne.symm]
    exact (congrArg π (singletonNeighbor_color v c j)).trans hπj
  have heq : p.getVert 2 = (singletonNeighbor v c j).val :=
    follows_seven_cycle_color_unique p _ hf hlen (p.getVert_mem_support 2) hjmem
      (h2'.trans hjcolor.symm)
  have hadj : G.Adj v (p.getVert 1) := by
    simpa only [Walk.getVert_zero] using p.adj_getVert_succ (i := 0) (by omega)
  have hnext : G.Adj (p.getVert 1) (singletonNeighbor v c j).val := by
    rw [← heq]
    exact p.adj_getVert_succ (i := 1) (by omega)
  have hcolor : neighborColor v c ⟨p.getVert 1, hadj⟩ = eta := by
    have he : singletonEdgeColoring v c i (p.getVert 1) = eta :=
      π.injective (h1'.trans hπe.symm)
    rw [singletonEdgeColoring_outside v c i _ hadj.ne.symm] at he
    exact he
  exact ⟨⟨p.getVert 1, hadj⟩, hcolor, hnext⟩

theorem singleton_meets_nonsingleton_color
    (hcrit : IsCriticalPlus 7 G) (hs : ShortSevenCycles G) (hr : RainbowSevenCycles G)
    (v : V) (c : (G.induce {x | x ≠ v}).Coloring (Fin 7))
    (hcard : 3 ≤ (singletonNeighborColors v c).card)
    (j : ↥(singletonNeighborColors v c)) (eta : Fin 7)
    (heta : eta ∉ singletonNeighborColors v c) :
    ∃ z : G.neighborSet v, neighborColor v c z = eta ∧
      G.Adj z.val (singletonNeighbor v c j).val := by
  classical
  have hlt : ({j.val} : Finset (Fin 7)).card < (singletonNeighborColors v c).card := by
    rw [Finset.card_singleton]
    omega
  obtain ⟨i0, hi0, hiout⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
  let i : ↥(singletonNeighborColors v c) := ⟨i0, hi0⟩
  have hij : i ≠ j := by
    intro he
    exact hiout (Finset.mem_singleton.mpr (congrArg Subtype.val he))
  have hie : i.val ≠ eta := by intro he; exact heta (he ▸ i.property)
  have hej : eta ≠ j.val := by intro he; exact heta (he.symm ▸ j.property)
  exact singleton_following_first_step hcrit hs hr v c i j hij eta hie hej

end TaskH.Seven
#print axioms TaskH.Seven.exists_order_zero_one_two
#print axioms TaskH.Seven.singleton_following_first_step
#print axioms TaskH.Seven.singleton_meets_nonsingleton_color
