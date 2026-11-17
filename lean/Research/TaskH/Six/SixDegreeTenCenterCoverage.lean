import Research.TaskH.Six.SixDegreeTenColors

/-!
A specified three-color order constructs an actual first neighbor adjacent
to the retained opposite singleton center. This is a graph-witness statement,
not merely the numerical lower bound of sixty cycles per color.
-/

set_option autoImplicit false

universe u

namespace TaskH.Six

open SimpleGraph _root_.TaskH.Challenge
open scoped Classical

variable {V : Type u} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem exists_order_zero_one_two (a b c : Fin 6)
    (hab : a ≠ b) (hca : c ≠ a) (hcb : c ≠ b) :
    ∃ π : Equiv.Perm (Fin 6), π a = 0 ∧ π b = 1 ∧ π c = 2 := by
  classical
  obtain ⟨τ, hτa, hτb⟩ := exists_order_zero_one a b hab
  have hc0 : τ c ≠ 0 := by
    intro he
    exact hca (τ.injective (he.trans hτa.symm))
  have hc1 : τ c ≠ 1 := by
    intro he
    exact hcb (τ.injective (he.trans hτb.symm))
  let π := τ.trans (Equiv.swap (τ c) 2)
  refine ⟨π, ?_, ?_, ?_⟩
  · change Equiv.swap (τ c) 2 (τ a) = 0
    rw [hτa]
    exact Equiv.swap_apply_of_ne_of_ne (Ne.symm hc0) (by decide)
  · change Equiv.swap (τ c) 2 (τ b) = 1
    rw [hτb]
    exact Equiv.swap_apply_of_ne_of_ne (Ne.symm hc1) (by decide)
  · change Equiv.swap (τ c) 2 (τ c) = 2
    exact Equiv.swap_apply_left _ _

theorem singleton_center_covers_other_color
    (hcrit : IsCriticalPlus 6 G) (hs : ShortSixCycles G) (hr : RainbowSixCycles G)
    (v : V) (c : (G.induce {x | x ≠ v}).Coloring (Fin 6))
    (i j : ↥(singletonNeighborColors v c)) (hij : i ≠ j)
    (k : Fin 6) (hik : i.val ≠ k) (hjk : j.val ≠ k) :
    ∃ z : G.neighborSet v, neighborColor v c z = k ∧
      G.Adj z.val (singletonNeighbor v c j).val := by
  classical
  have hijval : j.val ≠ i.val := fun he => hij (Subtype.ext he.symm)
  obtain ⟨π, hπi, hπk, hπj⟩ :=
    exists_order_zero_one_two i.val k j.val hik hijval hjk
  obtain ⟨p, hp, hlen, hf, _hout⟩ := singleton_through_ordered_cycle hcrit hs v c i π
  let C : V → Fin 6 := fun z => π (singletonEdgeColoring v c i z)
  have hbase : C v = 0 := by
    exact (congrArg π (singletonEdgeColoring_base v c i)).trans hπi
  have hget1 : C (p.getVert 1) = 1 := by
    have hh := follows_getVert p C (finRotate 6) hf 1 (by omega)
    rw [hbase] at hh
    exact hh.trans (by decide +kernel : (finRotate 6 ^ 1) (0 : Fin 6) = 1)
  have hget2 : C (p.getVert 2) = 2 := by
    have hh := follows_getVert p C (finRotate 6) hf 2 (by omega)
    rw [hbase] at hh
    exact hh.trans (by decide +kernel : (finRotate 6 ^ 2) (0 : Fin 6) = 2)
  have h1v : p.getVert 1 ≠ v := by
    intro he
    have hh := congrArg C he
    rw [hget1, hbase] at hh
    exact (by decide : (1 : Fin 6) ≠ 0) hh
  have h1full : singletonEdgeColoring v c i (p.getVert 1) = k :=
    π.injective (hget1.trans hπk.symm)
  have h1color : c ⟨p.getVert 1, h1v⟩ = k :=
    (singletonEdgeColoring_outside v c i (p.getVert 1) h1v).symm.trans h1full
  have hroot : G.Adj v (p.getVert 1) := by
    simpa only [Walk.getVert_zero] using p.adj_getVert_succ (i := 0) (by omega)
  let z : G.neighborSet v := ⟨p.getVert 1, hroot⟩
  have hzcolor : neighborColor v c z = k := h1color
  have hjmem := singleton_cycle_contains_other_neighbor hr v c i j hij π p hp hlen hf
  have hjC : C (singletonNeighbor v c j).val = 2 := by
    change π (singletonEdgeColoring v c i (singletonNeighbor v c j).val) = 2
    rw [singletonEdgeColoring_outside v c i _ (singletonNeighbor v c j).property.ne.symm]
    exact (congrArg π (singletonNeighbor_color v c j)).trans hπj
  have h2eq : p.getVert 2 = (singletonNeighbor v c j).val :=
    follows_six_cycle_color_unique p C hf hlen (p.getVert_mem_support 2) hjmem
      (hget2.trans hjC.symm)
  refine ⟨z, hzcolor, ?_⟩
  have hh := p.adj_getVert_succ (i := 1) (by omega : 1 < p.length)
  change G.Adj (p.getVert 1) (p.getVert 2) at hh
  change G.Adj (p.getVert 1) (singletonNeighbor v c j).val
  rwa [h2eq] at hh

end TaskH.Six

#print axioms TaskH.Six.exists_order_zero_one_two
#print axioms TaskH.Six.singleton_center_covers_other_color
