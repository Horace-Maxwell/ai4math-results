import Research.TaskH.Five.CycleFlux
import Research.TaskH.NestedShift

set_option autoImplicit false

universe u

namespace TaskH.Five.GoodCycles

open SimpleGraph

theorem finite_nested_forward :
    ∀ (a b : Fin 5) (ai aj bi bj : Bool),
      (aj = true → ai = true) → (bj = true → bi = true) →
      shiftBit b bi = finRotate 5 (shiftBit a ai) →
      shiftBit b bj = finRotate 5 (shiftBit a aj) →
      (ai && !aj) = (bi && !bj) := by
  decide +kernel

theorem finite_nested_opposite :
    ∀ (a b : Fin 5) (ai aj bi bj : Bool),
      (aj = true → ai = true) → (bj = true → bi = true) →
      shiftBit b bi = finRotate 5 (shiftBit a ai) →
      shiftBit a aj = finRotate 5 (shiftBit b bj) → False := by
  decide +kernel

variable {V : Type u} {G : SimpleGraph V}

theorem nested_mark_constant {x y : V} (p : G.Walk x y) (c : V → Fin 5)
    (si sj : V → Bool) (hsub : ∀ z, sj z = true → si z = true)
    (hi : Follows p (fun z => shiftBit (c z) (si z)) (finRotate 5))
    (hj : Follows p (fun z => shiftBit (c z) (sj z)) (finRotate 5)) :
    ∀ z ∈ p.support, (si z && !sj z) = (si x && !sj x) := by
  apply TaskH.GoodCycles.dart_constant_on_support p (fun z => si z && !sj z)
  intro d hd
  exact finite_nested_forward (c d.fst) (c d.snd)
    (si d.fst) (sj d.fst) (si d.snd) (sj d.snd)
    (hsub d.fst) (hsub d.snd) (hi d hd) (hj d hd)

theorem nested_opposite_impossible {x y : V} (p : G.Walk x y) (hpos : 0 < p.length)
    (c : V → Fin 5) (si sj : V → Bool)
    (hsub : ∀ z, sj z = true → si z = true)
    (hi : Follows p (fun z => shiftBit (c z) (si z)) (finRotate 5))
    (hj : Follows p.reverse (fun z => shiftBit (c z) (sj z)) (finRotate 5)) : False := by
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


end TaskH.Five.GoodCycles

#print axioms TaskH.Five.GoodCycles.finite_nested_forward
#print axioms TaskH.Five.GoodCycles.finite_nested_opposite
#print axioms TaskH.Five.GoodCycles.nested_mark_constant
#print axioms TaskH.Five.GoodCycles.nested_opposite_impossible
