import Research.TaskH.Six.SixDegreeTenLocalShape

/-!
Actual simple four-edge paths with one vertex outside the root's closed
neighborhood. Their indices separate this outside vertex from every member
of the already constructed ten-neighbor frame.
-/

set_option autoImplicit false

universe u

namespace TaskH.Six

open SimpleGraph
open scoped Classical

variable {V : Type u} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]
variable {v : V} {c : (G.induce {x | x ≠ v}).Coloring (Fin 6)}

noncomputable def degreeTenExteriorVertex (F : DegreeTenColorFrame v c) (z : V) :
    Option DegreeTenNeighborIndex → V
  | none => z
  | some i => degreeTenIndexedVertex F i

theorem degreeTenExteriorVertex_injective (F : DegreeTenColorFrame v c) (z : V)
    (hz : z ≠ v ∧ ¬ G.Adj v z) :
    Function.Injective (degreeTenExteriorVertex F z) := by
  intro a b he
  cases a with
  | none =>
    cases b with
    | none => rfl
    | some j =>
      change z = degreeTenIndexedVertex F j at he
      have hjadj : G.Adj v (degreeTenIndexedVertex F j) :=
        (degreeTenIndexedNeighbor F j).property
      exact False.elim (hz.2 (by simpa only [he] using hjadj))
  | some i =>
    cases b with
    | none =>
      change degreeTenIndexedVertex F i = z at he
      have hiadj : G.Adj v (degreeTenIndexedVertex F i) :=
        (degreeTenIndexedNeighbor F i).property
      exact False.elim (hz.2 (by simpa only [← he] using hiadj))
    | some j =>
      change degreeTenIndexedVertex F i = degreeTenIndexedVertex F j at he
      exact congrArg some (degreeTenIndexedVertex_injective F he)

theorem degreeTenExteriorVertex_ne_root (F : DegreeTenColorFrame v c) (z : V)
    (hz : z ≠ v ∧ ¬ G.Adj v z) (a : Option DegreeTenNeighborIndex) :
    degreeTenExteriorVertex F z a ≠ v := by
  cases a with
  | none => exact hz.1
  | some i => exact (degreeTenIndexedNeighbor F i).property.ne.symm

def degreeTenCommonForkWord (i j k : Fin 4) (ri rj rk a : Fin 2) :
    Fin 5 → Option DegreeTenNeighborIndex :=
  ![some (Sum.inr (i, ri)), none, some (Sum.inr (j, rj)),
    some (Sum.inl a), some (Sum.inr (k, rk))]

theorem degreeTenCommonForkWord_injective (i j k : Fin 4) (ri rj rk a : Fin 2)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    Function.Injective (degreeTenCommonForkWord i j k ri rj rk a) := by
  intro b d he
  fin_cases b <;> fin_cases d <;>
    simp_all [degreeTenCommonForkWord, Prod.mk.injEq]

def degreeTenCommonMixedWord (r : Fin 4 → Fin 2) (k i j : Fin 4) :
    Fin 5 → Option DegreeTenNeighborIndex :=
  ![some (Sum.inr (k, r k)), some (Sum.inl 0),
    some (Sum.inr (i, r i)), none, some (Sum.inr (j, r j + 1))]

theorem degreeTenCommonMixedWord_injective (r : Fin 4 → Fin 2) (k i j : Fin 4)
    (hki : k ≠ i) : Function.Injective (degreeTenCommonMixedWord r k i j) := by
  have hnext : ∀ a : Fin 4, r a ≠ r a + 1 := by
    intro a
    generalize h : r a = t
    fin_cases t <;> decide +kernel
  have hki' : ((k, r k) : Fin 4 × Fin 2) ≠ (i, r i) :=
    fun h => hki (congrArg Prod.fst h)
  have hkj' : ((k, r k) : Fin 4 × Fin 2) ≠ (j, r j + 1) := by
    intro h
    have hk : k = j := congrArg Prod.fst h
    subst k
    exact hnext j (congrArg Prod.snd h)
  have hij' : ((i, r i) : Fin 4 × Fin 2) ≠ (j, r j + 1) := by
    intro h
    have hi : i = j := congrArg Prod.fst h
    subst i
    exact hnext j (congrArg Prod.snd h)
  intro b d he
  fin_cases b <;> fin_cases d
  all_goals first
    | rfl
    | exact False.elim (hki' (Sum.inr.inj (Option.some.inj he)))
    | exact False.elim (hki' (Sum.inr.inj (Option.some.inj he.symm)))
    | exact False.elim (hkj' (Sum.inr.inj (Option.some.inj he)))
    | exact False.elim (hkj' (Sum.inr.inj (Option.some.inj he.symm)))
    | exact False.elim (hij' (Sum.inr.inj (Option.some.inj he)))
    | exact False.elim (hij' (Sum.inr.inj (Option.some.inj he.symm)))
    | cases he

theorem degreeTen_exterior_path_colors_injective (hr : RainbowSixCycles G)
    (F : DegreeTenColorFrame v c) (z : V) (hz : z ≠ v ∧ ¬ G.Adj v z)
    (w : Fin 5 → Option DegreeTenNeighborIndex) (hw : Function.Injective w)
    (hv0 : G.Adj v (degreeTenExteriorVertex F z (w 0)))
    (h01 : G.Adj (degreeTenExteriorVertex F z (w 0))
      (degreeTenExteriorVertex F z (w 1)))
    (h12 : G.Adj (degreeTenExteriorVertex F z (w 1))
      (degreeTenExteriorVertex F z (w 2)))
    (h23 : G.Adj (degreeTenExteriorVertex F z (w 2))
      (degreeTenExteriorVertex F z (w 3)))
    (h34 : G.Adj (degreeTenExteriorVertex F z (w 3))
      (degreeTenExteriorVertex F z (w 4)))
    (h4v : G.Adj (degreeTenExteriorVertex F z (w 4)) v) :
    Function.Injective (fun i =>
      c ⟨degreeTenExteriorVertex F z (w i), degreeTenExteriorVertex_ne_root F z hz (w i)⟩) := by
  exact rainbow_five_path_colors_injective hr v c
    (degreeTenExteriorVertex F z ∘ w)
    ((degreeTenExteriorVertex_injective F z hz).comp hw)
    (fun i => degreeTenExteriorVertex_ne_root F z hz (w i)) hv0 h01 h12 h23 h34 h4v

theorem degreeTenFrame_deleted_color_exhaustion (F : DegreeTenColorFrame v c)
    (r : Fin 4 → Fin 2) (z : {x : V // x ≠ v}) :
    (∃ a : Fin 2, c z = neighborColor v c (degreeTenCenter F a)) ∨
      ∃ i : Fin 4, c z = neighborColor v c (degreeTenPair F i (r i)) := by
  by_cases hS : c z ∈ singletonNeighborColors v c
  · let s : ↥(singletonNeighborColors v c) := ⟨c z, hS⟩
    refine Or.inl ⟨F.singletonColors s, ?_⟩
    rw [degreeTenCenter_color, F.singletonColors.symm_apply_apply]
  · let s : ↥((singletonNeighborColors v c)ᶜ) := ⟨c z, Finset.mem_compl.mpr hS⟩
    refine Or.inr ⟨F.doubleColors s, ?_⟩
    rw [degreeTenPair_color, F.doubleColors.symm_apply_apply]

end TaskH.Six

#print axioms TaskH.Six.degreeTenExteriorVertex
#print axioms TaskH.Six.degreeTenExteriorVertex_injective
#print axioms TaskH.Six.degreeTenExteriorVertex_ne_root
#print axioms TaskH.Six.degreeTenCommonForkWord
#print axioms TaskH.Six.degreeTenCommonForkWord_injective
#print axioms TaskH.Six.degreeTenCommonMixedWord
#print axioms TaskH.Six.degreeTenCommonMixedWord_injective
#print axioms TaskH.Six.degreeTen_exterior_path_colors_injective
#print axioms TaskH.Six.degreeTenFrame_deleted_color_exhaustion
