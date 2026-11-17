import Research.TaskH.Six.RawDescents

set_option autoImplicit false

universe u

namespace TaskH.Six.GoodCycles

open SimpleGraph

def shiftBit (a : Fin 6) (t : Bool) : Fin 6 :=
  if t then (finRotate 6).symm a else a

/-- The local integer identity for the original six-color layer shift.
This finite check concerns six colors and four Boolean flags, not graphs. -/
theorem finite_layer_flow :
    ∀ (a b : Fin 6) (tx ty rx ry : Bool),
      (rx = true → a = 5 ∧ tx = false) →
      (ry = true → b = 5 ∧ ty = false) →
      ¬ (rx = true ∧ ry = true) →
      (rx = false ∧ ry = false → a ≠ b) →
      shiftBit b ty = finRotate 6 (shiftBit a tx) →
      ((b.val : ℤ) - (if ty then 1 else 0)) -
        ((a.val : ℤ) - (if tx then 1 else 0)) =
        1 - 6 * (if (if ry then 6 else b.val) < (if rx then 6 else a.val)
          then 1 else 0) := by
  decide +kernel

variable {V : Type u} {G : SimpleGraph V}

/-- Telescoping the actual dart increments identifies length and descents. -/
theorem walk_flux {x y : V} (p : G.Walk x y) (r : V → Fin 7) (label : V → ℤ)
    (hf : ∀ d ∈ p.darts, label d.snd - label d.fst =
      1 - 6 * (if r d.snd < r d.fst then 1 else 0)) :
    (p.length : ℤ) = label y - label x + 6 * (rawDescents r p : ℤ) := by
  revert hf
  induction p with
  | nil => intro _; simp [rawDescents_nil]
  | @cons x y z hxy p ih =>
    intro hf
    have hfirst : label y - label x = 1 - 6 * (if r y < r x then 1 else 0) := by
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

theorem closed_length_eq_six_descents {x : V} (p : G.Walk x x)
    (r : V → Fin 7) (label : V → ℤ)
    (hf : ∀ d ∈ p.darts, label d.snd - label d.fst =
      1 - 6 * (if r d.snd < r d.fst then 1 else 0)) :
    p.length = 6 * rawDescents r p := by
  have h := walk_flux p r label hf
  simp only [sub_self, zero_add] at h
  exact_mod_cast h


end TaskH.Six.GoodCycles

#print axioms TaskH.Six.GoodCycles.shiftBit
#print axioms TaskH.Six.GoodCycles.finite_layer_flow
#print axioms TaskH.Six.GoodCycles.walk_flux
#print axioms TaskH.Six.GoodCycles.closed_length_eq_six_descents
