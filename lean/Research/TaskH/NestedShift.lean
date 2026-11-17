import Research.TaskH.CycleFlux
import Research.TaskH.DirectedCycle

set_option autoImplicit false

universe u

namespace TaskH.GoodCycles

open SimpleGraph

theorem finite_nested_forward :
    ∀ (a b : Fin 4) (ai aj bi bj : Bool),
      (aj = true → ai = true) → (bj = true → bi = true) →
      shiftBit b bi = finRotate 4 (shiftBit a ai) →
      shiftBit b bj = finRotate 4 (shiftBit a aj) →
      (ai && !aj) = (bi && !bj) := by
  decide +kernel

theorem finite_nested_opposite :
    ∀ (a b : Fin 4) (ai aj bi bj : Bool),
      (aj = true → ai = true) → (bj = true → bi = true) →
      shiftBit b bi = finRotate 4 (shiftBit a ai) →
      shiftBit a aj = finRotate 4 (shiftBit b bj) → False := by
  decide +kernel

variable {V : Type u} {G : SimpleGraph V}

theorem dart_constant_on_support {β : Type*} {x y : V} (p : G.Walk x y) (f : V → β)
    (hf : ∀ d ∈ p.darts, f d.fst = f d.snd) :
    ∀ z ∈ p.support, f z = f x := by
  revert hf
  induction p with
  | @nil a =>
    intro _ z hz
    have hz' : z = a := by simpa using hz
    subst z
    rfl
  | @cons x y w h p ih =>
    intro hf z hz
    have hfirst : f x = f y := by
      apply hf ⟨(x, y), h⟩
      simp [Walk.darts_cons]
    have htail := ih (by
      intro d hd
      apply hf d
      rw [Walk.darts_cons]
      exact List.mem_cons.mpr (Or.inr hd))
    rw [Walk.support_cons, List.mem_cons] at hz
    rcases hz with rfl | hz
    · rfl
    · exact (htail z hz).trans hfirst.symm

theorem nested_mark_constant {x y : V} (p : G.Walk x y) (c : V → Fin 4)
    (si sj : V → Bool) (hsub : ∀ z, sj z = true → si z = true)
    (hi : Follows p (fun z => shiftBit (c z) (si z)) (finRotate 4))
    (hj : Follows p (fun z => shiftBit (c z) (sj z)) (finRotate 4)) :
    ∀ z ∈ p.support, (si z && !sj z) = (si x && !sj x) := by
  apply dart_constant_on_support p (fun z => si z && !sj z)
  intro d hd
  exact finite_nested_forward (c d.fst) (c d.snd)
    (si d.fst) (sj d.fst) (si d.snd) (sj d.snd)
    (hsub d.fst) (hsub d.snd) (hi d hd) (hj d hd)

theorem nested_opposite_impossible {x y : V} (p : G.Walk x y) (hpos : 0 < p.length)
    (c : V → Fin 4) (si sj : V → Bool)
    (hsub : ∀ z, sj z = true → si z = true)
    (hi : Follows p (fun z => shiftBit (c z) (si z)) (finRotate 4))
    (hj : Follows p.reverse (fun z => shiftBit (c z) (sj z)) (finRotate 4)) : False := by
  cases p with
  | nil => simp at hpos
  | @cons x y z h p =>
    have hmi : (⟨(x, y), h⟩ : G.Dart) ∈ (Walk.cons h p).darts := by
      simp [Walk.darts_cons]
    have hmj : (⟨(y, x), h.symm⟩ : G.Dart) ∈ (Walk.cons h p).reverse.darts := by
      rw [Walk.mem_darts_reverse]
      exact hmi
    exact finite_nested_opposite (c x) (c y) (si x) (sj x) (si y) (sj y)
      (hsub x) (hsub y) (hi _ hmi) (hj _ hmj)

#print axioms finite_nested_forward
#print axioms finite_nested_opposite
#print axioms nested_mark_constant
#print axioms nested_opposite_impossible

end TaskH.GoodCycles
