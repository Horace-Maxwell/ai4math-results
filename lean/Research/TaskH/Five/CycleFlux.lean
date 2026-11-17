import Research.TaskH.Five.RawDescents

set_option autoImplicit false

universe u

namespace TaskH.Five.GoodCycles

open SimpleGraph

def shiftBit (a : Fin 5) (t : Bool) : Fin 5 :=
  if t then (finRotate 5).symm a else a

/-- The local integer identity for the original five-color layer shift.
This finite check concerns five colors and four Boolean flags, not graphs. -/
theorem finite_layer_flow :
    ∀ (a b : Fin 5) (tx ty rx ry : Bool),
      (rx = true → a = 4 ∧ tx = false) →
      (ry = true → b = 4 ∧ ty = false) →
      ¬ (rx = true ∧ ry = true) →
      (rx = false ∧ ry = false → a ≠ b) →
      shiftBit b ty = finRotate 5 (shiftBit a tx) →
      ((b.val : ℤ) - (if ty then 1 else 0)) -
        ((a.val : ℤ) - (if tx then 1 else 0)) =
        1 - 5 * (if (if ry then 5 else b.val) < (if rx then 5 else a.val)
          then 1 else 0) := by
  decide +kernel

variable {V : Type u} {G : SimpleGraph V}

/-- Telescoping the actual dart increments identifies length and descents. -/
theorem walk_flux {x y : V} (p : G.Walk x y) (r : V → Fin 6) (label : V → ℤ)
    (hf : ∀ d ∈ p.darts, label d.snd - label d.fst =
      1 - 5 * (if r d.snd < r d.fst then 1 else 0)) :
    (p.length : ℤ) = label y - label x + 5 * (rawDescents r p : ℤ) := by
  revert hf
  induction p with
  | nil => intro _; simp [rawDescents_nil]
  | @cons x y z hxy p ih =>
    intro hf
    have hfirst : label y - label x = 1 - 5 * (if r y < r x then 1 else 0) := by
      apply hf ⟨(x, y), hxy⟩
      simp [Walk.darts_cons]
    have htail := ih (by
      intro d hd
      apply hf d
      rw [Walk.darts_cons]
      exact List.mem_cons.mpr (Or.inr hd))
    rw [Walk.length_cons, rawDescents_cons]
    by_cases hd : r y < r x
    · simp only [ite_eq_left hd, Nat.cast_add, Nat.cast_one] at hfirst ⊢
      omega
    · simp only [ite_eq_right hd, Nat.cast_add, Nat.cast_one, zero_add]
        at hfirst ⊢
      omega

theorem closed_length_eq_five_descents {x : V} (p : G.Walk x x)
    (r : V → Fin 6) (label : V → ℤ)
    (hf : ∀ d ∈ p.darts, label d.snd - label d.fst =
      1 - 5 * (if r d.snd < r d.fst then 1 else 0)) :
    p.length = 5 * rawDescents r p := by
  have h := walk_flux p r label hf
  simp only [sub_self, zero_add] at h
  exact_mod_cast h


end TaskH.Five.GoodCycles

#print axioms TaskH.Five.GoodCycles.shiftBit
#print axioms TaskH.Five.GoodCycles.finite_layer_flow
#print axioms TaskH.Five.GoodCycles.walk_flux
#print axioms TaskH.Five.GoodCycles.closed_length_eq_five_descents
