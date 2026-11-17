import Research.TaskH.Six.SixDegreeTenFrame
import Research.TaskH.Six.SixNeighborPathRule

/-! Explicit simple neighbor paths in the actual degree-ten frame. -/

set_option autoImplicit false

universe u

namespace TaskH.Six

open SimpleGraph

variable {V : Type u} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]
variable {v : V} {c : (G.induce {x | x ≠ v}).Coloring (Fin 6)}

abbrev DegreeTenNeighborIndex := Fin 2 ⊕ (Fin 4 × Fin 2)

noncomputable def degreeTenIndexedNeighbor (F : DegreeTenColorFrame v c) :
    DegreeTenNeighborIndex → G.neighborSet v :=
  Sum.elim (degreeTenCenter F) (fun ij => degreeTenPair F ij.1 ij.2)

noncomputable def degreeTenIndexedVertex (F : DegreeTenColorFrame v c)
    (i : DegreeTenNeighborIndex) : V := (degreeTenIndexedNeighbor F i).val

theorem degreeTenIndexedVertex_injective (F : DegreeTenColorFrame v c) :
    Function.Injective (degreeTenIndexedVertex F) := by
  rintro (i | ij) (j | kl) he
  · exact congrArg Sum.inl (degreeTenCenter_val_injective F he)
  · exact False.elim (degreeTenCenter_pair_ne F i kl.1 kl.2 he)
  · exact False.elim (degreeTenCenter_pair_ne F j ij.1 ij.2 he.symm)
  · exact congrArg Sum.inr (degreeTenPair_all_val_injective F he)

def degreeTenCrossWord (i j : Fin 4) (u w s : Fin 2) :
    Fin 5 → DegreeTenNeighborIndex :=
  ![Sum.inr (j, u), Sum.inl 0, Sum.inr (i, s), Sum.inr (j, w), Sum.inl 1]

def degreeTenCommonCrossWord (i j : Fin 4) (u w s : Fin 2) :
    Fin 5 → DegreeTenNeighborIndex :=
  ![Sum.inr (j, u), Sum.inr (i, s), Sum.inl 0, Sum.inr (j, w), Sum.inl 1]

theorem degreeTenCrossWord_injective (i j : Fin 4) (u w s : Fin 2)
    (hij : i ≠ j) (huw : u ≠ w) :
    Function.Injective (degreeTenCrossWord i j u w s) := by
  intro a b he
  fin_cases a <;> fin_cases b <;> simp_all [degreeTenCrossWord, Prod.mk.injEq]

theorem degreeTenCommonCrossWord_injective (i j : Fin 4) (u w s : Fin 2)
    (hij : i ≠ j) (huw : u ≠ w) :
    Function.Injective (degreeTenCommonCrossWord i j u w s) := by
  intro a b he
  fin_cases a <;> fin_cases b <;> simp_all [degreeTenCommonCrossWord, Prod.mk.injEq]

theorem degreeTen_indexed_path_colors_injective (hr : RainbowSixCycles G)
    (F : DegreeTenColorFrame v c) (w : Fin 5 → DegreeTenNeighborIndex)
    (hw : Function.Injective w)
    (h01 : G.Adj (degreeTenIndexedVertex F (w 0)) (degreeTenIndexedVertex F (w 1)))
    (h12 : G.Adj (degreeTenIndexedVertex F (w 1)) (degreeTenIndexedVertex F (w 2)))
    (h23 : G.Adj (degreeTenIndexedVertex F (w 2)) (degreeTenIndexedVertex F (w 3)))
    (h34 : G.Adj (degreeTenIndexedVertex F (w 3)) (degreeTenIndexedVertex F (w 4))) :
    Function.Injective (fun i => neighborColor v c (degreeTenIndexedNeighbor F (w i))) := by
  let t : Fin 5 → V := degreeTenIndexedVertex F ∘ w
  have hti : Function.Injective t := (degreeTenIndexedVertex_injective F).comp hw
  have htv : ∀ i, t i ≠ v :=
    fun i => (degreeTenIndexedNeighbor F (w i)).property.ne.symm
  exact rainbow_five_path_colors_injective hr v c t hti htv
    (degreeTenIndexedNeighbor F (w 0)).property h01 h12 h23 h34
    (degreeTenIndexedNeighbor F (w 4)).property.symm

end TaskH.Six

#print axioms TaskH.Six.DegreeTenNeighborIndex
#print axioms TaskH.Six.degreeTenIndexedNeighbor
#print axioms TaskH.Six.degreeTenIndexedVertex
#print axioms TaskH.Six.degreeTenIndexedVertex_injective
#print axioms TaskH.Six.degreeTenCrossWord
#print axioms TaskH.Six.degreeTenCommonCrossWord
#print axioms TaskH.Six.degreeTenCrossWord_injective
#print axioms TaskH.Six.degreeTenCommonCrossWord_injective
#print axioms TaskH.Six.degreeTen_indexed_path_colors_injective
