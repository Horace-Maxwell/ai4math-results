import Research.TaskH.Five.Definitions
import Research.TaskH.Degree
import Research.TaskH.Recolor

/-!
Degree-five neighbors and actual reachability in the deleted graph.
The neighbors are identified with their actual colors by criticality and
degree, and the reachable-set recoloring proves the required predecessor
paths. No counting, short-cycle, or equality-case hypothesis is assumed.
-/

set_option autoImplicit false

universe u

namespace TaskH.Five

open _root_.TaskH.Challenge SimpleGraph

variable {V : Type u} {G : SimpleGraph V}

section FiniteGraph

variable [Fintype V] [DecidableRel G.Adj]

theorem degreeFiveNeighborColor_bijective (hcrit : IsCriticalPlus 5 G) (v : V)
    (c : (G.induce {x | x ≠ v}).Coloring (Fin 5)) (hdegree : G.degree v = 5) :
    Function.Bijective (neighborColor v c) := by
  apply (Fintype.bijective_iff_surjective_and_card (neighborColor v c)).mpr
  refine ⟨critical_neighborColor_surjective hcrit v c, ?_⟩
  rw [G.card_neighborSet_eq_degree, Fintype.card_fin, hdegree]

/-- The actual neighbor/color bijection, with no chosen ambient ordering. -/
noncomputable def degreeFiveNeighborEquiv (hcrit : IsCriticalPlus 5 G) (v : V)
    (c : (G.induce {x | x ≠ v}).Coloring (Fin 5)) (hdegree : G.degree v = 5) :
    G.neighborSet v ≃ Fin 5 :=
  Equiv.ofBijective (neighborColor v c) (degreeFiveNeighborColor_bijective hcrit v c hdegree)

/-- The unique neighbor with color i, as a vertex of the actual deleted graph. -/
noncomputable def degreeFiveNeighbor (hcrit : IsCriticalPlus 5 G) (v : V)
    (c : (G.induce {x | x ≠ v}).Coloring (Fin 5)) (hdegree : G.degree v = 5)
    (i : Fin 5) : {x : V // x ≠ v} := by
  let z := (degreeFiveNeighborEquiv hcrit v c hdegree).symm i
  exact ⟨z.val, ((G.mem_neighborSet v z.val).mp z.property).ne.symm⟩

theorem degreeFiveNeighbor_adj (hcrit : IsCriticalPlus 5 G) (v : V)
    (c : (G.induce {x | x ≠ v}).Coloring (Fin 5)) (hdegree : G.degree v = 5)
    (i : Fin 5) : G.Adj v (degreeFiveNeighbor hcrit v c hdegree i).val := by
  exact ((degreeFiveNeighborEquiv hcrit v c hdegree).symm i).property

theorem degreeFiveNeighbor_color (hcrit : IsCriticalPlus 5 G) (v : V)
    (c : (G.induce {x | x ≠ v}).Coloring (Fin 5)) (hdegree : G.degree v = 5)
    (i : Fin 5) : c (degreeFiveNeighbor hcrit v c hdegree i) = i := by
  change neighborColor v c ((degreeFiveNeighborEquiv hcrit v c hdegree).symm i) = i
  exact (degreeFiveNeighborEquiv hcrit v c hdegree).apply_symm_apply i

theorem degreeFiveNeighbor_eq_of_color (hcrit : IsCriticalPlus 5 G) (v : V)
    (c : (G.induce {x | x ≠ v}).Coloring (Fin 5)) (hdegree : G.degree v = 5)
    (i : Fin 5) (z : {x : V // x ≠ v}) (hz : G.Adj v z.val) (hc : c z = i) :
    z = degreeFiveNeighbor hcrit v c hdegree i := by
  let nz : G.neighborSet v := ⟨z.val, hz⟩
  have hnz : neighborColor v c nz = i := hc
  have he : nz = (degreeFiveNeighborEquiv hcrit v c hdegree).symm i := by
    apply (degreeFiveNeighborEquiv hcrit v c hdegree).injective
    change neighborColor v c nz =
      neighborColor v c ((degreeFiveNeighborEquiv hcrit v c hdegree).symm i)
    exact hnz.trans ((degreeFiveNeighborEquiv hcrit v c hdegree).apply_symm_apply i).symm
  apply Subtype.ext
  exact congrArg (fun t : G.neighborSet v => t.val) he

/-- The predecessor-neighbor reachability holds for every color permutation,
and in particular for each full four-color cycle. The only inputs are actual
criticality, actual degree five, and the actual deleted-vertex coloring. -/
theorem degreeFiveNeighbor_reachable (hcrit : IsCriticalPlus 5 G) (v : V)
    (c : (G.induce {x | x ≠ v}).Coloring (Fin 5)) (hdegree : G.degree v = 5)
    (σ : Equiv.Perm (Fin 5)) (i : Fin 5) :
    Relation.ReflTransGen (ColorStep (G.induce {x | x ≠ v}) c σ)
      (degreeFiveNeighbor hcrit v c hdegree i)
      (degreeFiveNeighbor hcrit v c hdegree (σ.symm i)) := by
  classical
  by_contra hnot
  let R : Set {x : V // x ≠ v} := {z |
    Relation.ReflTransGen (ColorStep (G.induce {x | x ≠ v}) c σ)
      (degreeFiveNeighbor hcrit v c hdegree i) z}
  have hclosed : ∀ {a b : {x : V // x ≠ v}}, a ∈ R →
      ColorStep (G.induce {x | x ≠ v}) c σ a b → b ∈ R := by
    intro a b ha hab
    exact ha.tail hab
  let d := recolorClosed c σ R hclosed
  obtain ⟨z, hz⟩ := critical_neighborColor_surjective hcrit v d i
  let z' : {x : V // x ≠ v} :=
    ⟨z.val, ((G.mem_neighborSet v z.val).mp z.property).ne.symm⟩
  have hzcolor : d z' = i := hz
  have hzadj : G.Adj v z'.val := z.property
  by_cases hzR : z' ∈ R
  · have hshift : σ (c z') = i := by
      simpa only [ite_eq_left hzR] using
        (recolorClosed_apply c σ R hclosed z').symm.trans hzcolor
    have hold : c z' = σ.symm i := by
      calc
        c z' = σ.symm (σ (c z')) := (σ.symm_apply_apply (c z')).symm
        _ = σ.symm i := congrArg σ.symm hshift
    have he := degreeFiveNeighbor_eq_of_color hcrit v c hdegree (σ.symm i) z' hzadj hold
    have htarget : degreeFiveNeighbor hcrit v c hdegree (σ.symm i) ∈ R := by
      rw [← he]
      exact hzR
    exact hnot htarget
  · have hold : c z' = i := by
      simpa only [ite_eq_right hzR] using
        (recolorClosed_apply c σ R hclosed z').symm.trans hzcolor
    have he := degreeFiveNeighbor_eq_of_color hcrit v c hdegree i z' hzadj hold
    have hsource : degreeFiveNeighbor hcrit v c hdegree i ∈ R := Relation.ReflTransGen.refl
    apply hzR
    rw [he]
    exact hsource

end FiniteGraph

end TaskH.Five

#print axioms TaskH.Five.degreeFiveNeighborColor_bijective
#print axioms TaskH.Five.degreeFiveNeighborEquiv
#print axioms TaskH.Five.degreeFiveNeighbor
#print axioms TaskH.Five.degreeFiveNeighbor_adj
#print axioms TaskH.Five.degreeFiveNeighbor_color
#print axioms TaskH.Five.degreeFiveNeighbor_eq_of_color
#print axioms TaskH.Five.degreeFiveNeighbor_reachable
