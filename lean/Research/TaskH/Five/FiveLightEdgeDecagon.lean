import Research.TaskH.Five.FiveLightEdgeData

/-! Genuine ten-edge cycle witnesses used by the light-edge argument. -/

universe u

namespace TaskH.Five

open SimpleGraph

variable {V : Type u} {G : SimpleGraph V}

def lightDecagonWalk (r : Fin 10 → V)
    (h : ∀ i : Fin 10, G.Adj (r i) (r (i + 1))) : G.Walk (r 0) (r 0) :=
  .cons (h 0) (.cons (h 1) (.cons (h 2) (.cons (h 3) (.cons (h 4)
    (.cons (h 5) (.cons (h 6) (.cons (h 7) (.cons (h 8) (.cons (h 9) .nil)))))))))

theorem lightDecagonWalk_isCycle (r : Fin 10 → V) (hr : Function.Injective r)
    (h : ∀ i : Fin 10, G.Adj (r i) (r (i + 1))) :
    (lightDecagonWalk r h).IsCycle := by
  rw [lightDecagonWalk, Walk.cons_isCycle_iff]
  constructor
  · apply Walk.IsPath.mk'
    simp [Walk.support_cons, hr.eq_iff]
  · simp [Walk.edges_cons, Sym2.eq, Sym2.rel_iff', Prod.mk.injEq,
      Prod.swap_prod_mk, hr.eq_iff]

theorem lightDecagonWalk_length (r : Fin 10 → V)
    (h : ∀ i : Fin 10, G.Adj (r i) (r (i + 1))) :
    (lightDecagonWalk r h).length = 10 := rfl

theorem shortFive_forbids_decagon (hs : ShortFiveCycles G)
    (r : Fin 10 → V) (hr : Function.Injective r)
    (h : ∀ i : Fin 10, G.Adj (r i) (r (i + 1))) : False := by
  have he := hs (lightDecagonWalk r h) (lightDecagonWalk_isCycle r hr h)
    (by decide : 5 ∣ 10)
  have hl := lightDecagonWalk_length r h
  omega

def lightInterleave (f x : Fin 5 → V) : Fin 10 → V :=
  ![f 0, x 0, f 1, x 1, f 2, x 2, f 3, x 3, f 4, x 4]

theorem lightInterleave_injective (f x : Fin 5 → V)
    (hf : Function.Injective f) (hx : Function.Injective x)
    (hxf : ∀ i j : Fin 5, x i ≠ f j) :
    Function.Injective (lightInterleave f x) := by
  have hfx : ∀ i j : Fin 5, f i ≠ x j := fun i j => (hxf j i).symm
  intro i j he
  fin_cases i <;> fin_cases j <;>
    simp_all [lightInterleave, hf.eq_iff, hx.eq_iff]

theorem lightInterleave_adj (f x : Fin 5 → V)
    (hl : ∀ i : Fin 5, G.Adj (f i) (x i))
    (hr : ∀ i : Fin 5, G.Adj (x i) (f (i + 1))) :
    ∀ i : Fin 10, G.Adj (lightInterleave f x i) (lightInterleave f x (i + 1)) := by
  intro i
  fin_cases i
  · exact hl 0
  · exact hr 0
  · exact hl 1
  · exact hr 1
  · exact hl 2
  · exact hr 2
  · exact hl 3
  · exact hr 3
  · exact hl 4
  · exact hr 4

theorem shortFive_forbids_interleaved_neighbors (hs : ShortFiveCycles G)
    (f x : Fin 5 → V) (hf : Function.Injective f) (hx : Function.Injective x)
    (hxf : ∀ i j : Fin 5, x i ≠ f j)
    (hl : ∀ i : Fin 5, G.Adj (f i) (x i))
    (hr : ∀ i : Fin 5, G.Adj (x i) (f (i + 1))) : False :=
  shortFive_forbids_decagon hs (lightInterleave f x)
    (lightInterleave_injective f x hf hx hxf) (lightInterleave_adj f x hl hr)

end TaskH.Five

#print axioms TaskH.Five.lightDecagonWalk
#print axioms TaskH.Five.lightDecagonWalk_isCycle
#print axioms TaskH.Five.lightDecagonWalk_length
#print axioms TaskH.Five.shortFive_forbids_decagon
#print axioms TaskH.Five.lightInterleave
#print axioms TaskH.Five.lightInterleave_injective
#print axioms TaskH.Five.lightInterleave_adj
#print axioms TaskH.Five.shortFive_forbids_interleaved_neighbors
