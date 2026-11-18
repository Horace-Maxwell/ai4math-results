import Research.TaskH.General.RawDescents
import Mathlib.Logic.Equiv.Fin.Rotate

set_option autoImplicit false
universe u
namespace TaskH.General.GoodCycles
open SimpleGraph
variable {k : ℕ}

def shiftBit (a : Fin k) (t : Bool) : Fin k :=
  if t then (finRotate k).symm a else a

theorem rotate_symm_zero (n : ℕ) :
    (finRotate (n + 1)).symm (0 : Fin (n + 1)) = Fin.last n := by
  apply (finRotate (n + 1)).injective
  simp only [Equiv.apply_symm_apply, finRotate_last]

/-- The exact integer representative of a single modular shift. -/
theorem shiftBit_value (n : ℕ) (a : Fin (n + 1)) (t : Bool) :
    ((shiftBit a t).val : ℤ) = (a.val : ℤ) - (if t then 1 else 0) +
      (if t = true ∧ a = 0 then (n + 1 : ℕ) else 0) := by
  cases t with
  | false => simp [shiftBit]
  | true =>
    by_cases ha : a = 0
    · subst a
      simp [shiftBit]
    · have hv := coe_finRotate_symm_of_ne_zero ha
      have ha0 : a.val ≠ 0 := by
        intro he
        exact ha (Fin.ext he)
      have hvZ : (((finRotate (n + 1)).symm a).val : ℤ) = (a.val : ℤ) - 1 := by
        rw [hv]
        omega
      simpa [shiftBit, ha] using hvZ

/-- Symbolic arbitrary-color identity; only Boolean structural cases are split. -/
theorem layer_flow (hk : 3 ≤ k) (a b : Fin k) (tx ty rx ry : Bool)
    (hx : rx = true → a.val + 1 = k ∧ tx = false)
    (hy : ry = true → b.val + 1 = k ∧ ty = false)
    (hrr : ¬ (rx = true ∧ ry = true))
    (hne : rx = false ∧ ry = false → a ≠ b)
    (hstep : shiftBit b ty = finRotate k (shiftBit a tx)) :
    ((b.val : ℤ) - (if ty then 1 else 0)) -
      ((a.val : ℤ) - (if tx then 1 else 0)) =
      1 - (k : ℤ) * (if (if ry then k else b.val) <
        (if rx then k else a.val) then 1 else 0) := by
  cases k with
  | zero => omega
  | succ n =>
    have hsa := shiftBit_value n a tx
    have hsb := shiftBit_value n b ty
    have hrot := congrArg Fin.val hstep
    rw [coe_finRotate] at hrot
    have heq : shiftBit a tx = Fin.last n ↔ (shiftBit a tx).val = n := by
      constructor
      · intro he
        exact congrArg Fin.val he
      · intro he
        exact Fin.ext he
    have ha0 : a = 0 ↔ a.val = 0 := by
      constructor
      · intro he
        exact congrArg Fin.val he
      · intro he
        exact Fin.ext he
    have hb0 : b = 0 ↔ b.val = 0 := by
      constructor
      · intro he
        exact congrArg Fin.val he
      · intro he
        exact Fin.ext he
    have hneval : rx = false ∧ ry = false → a.val ≠ b.val := by
      intro h he
      exact hne h (Fin.ext he)
    simp only [heq] at hrot
    simp only [ha0] at hsa
    simp only [hb0] at hsb
    have ha := a.isLt
    have hb := b.isLt
    cases tx <;> cases ty <;> cases rx <;> cases ry <;>
      simp at hx hy hrr hneval hsa hsb hrot ⊢
    all_goals
      split_ifs at hsa hsb hrot ⊢ <;> omega

variable {V : Type u} {G : SimpleGraph V}

/-- Telescope actual darts for every k, retaining the original raw count. -/
theorem walk_flux {x y : V} (p : G.Walk x y) (r : V → Fin (k + 1))
    (label : V → ℤ)
    (hf : ∀ d ∈ p.darts, label d.snd - label d.fst =
      1 - (k : ℤ) * (if r d.snd < r d.fst then 1 else 0)) :
    (p.length : ℤ) = label y - label x + (k : ℤ) * (rawDescents r p : ℤ) := by
  revert hf
  induction p with
  | nil => intro _; simp [rawDescents_nil]
  | @cons x y z hxy p ih =>
    intro hf
    have hfirst : label y - label x =
        1 - (k : ℤ) * (if r y < r x then 1 else 0) := by
      apply hf ⟨(x, y), hxy⟩
      simp [Walk.darts_cons]
    have htail := ih (by
      intro d hd
      apply hf d
      rw [Walk.darts_cons]
      exact List.mem_cons.mpr (Or.inr hd))
    rw [Walk.length_cons, rawDescents_cons]
    by_cases hd : r y < r x
    · simp only [ite_eq_left hd, Nat.cast_add, Nat.cast_one, mul_add, mul_one]
        at hfirst ⊢
      omega
    · simp only [ite_eq_right hd, Nat.cast_add, Nat.cast_one, zero_add]
        at hfirst ⊢
      omega

theorem closed_length_eq_k_descents {x : V} (p : G.Walk x x)
    (r : V → Fin (k + 1)) (label : V → ℤ)
    (hf : ∀ d ∈ p.darts, label d.snd - label d.fst =
      1 - (k : ℤ) * (if r d.snd < r d.fst then 1 else 0)) :
    p.length = k * rawDescents r p := by
  have h := walk_flux p r label hf
  simp only [sub_self, zero_add] at h
  exact_mod_cast h

#print axioms shiftBit
#print axioms rotate_symm_zero
#print axioms shiftBit_value
#print axioms layer_flow
#print axioms walk_flux
#print axioms closed_length_eq_k_descents
end TaskH.General.GoodCycles
