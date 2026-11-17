import Research.TaskH.DirectedCycle

set_option autoImplicit false

universe u

namespace TaskH

open SimpleGraph

/-- Three representatives of the six oriented four-color cycles modulo reversal. -/
def fourColorCycle (i : Fin 3) : Equiv.Perm (Fin 4) :=
  ![finRotate 4,
    (Equiv.swap (2 : Fin 4) 3).trans ((finRotate 4).trans (Equiv.swap (2 : Fin 4) 3)),
    (Equiv.swap (1 : Fin 4) 2).trans ((finRotate 4).trans (Equiv.swap (1 : Fin 4) 2))] i

theorem fourColorCycle_fourth_power (i : Fin 3) : fourColorCycle i ^ 4 = 1 := by
  have h : ∀ i : Fin 3, fourColorCycle i ^ 4 = 1 := by decide +kernel
  exact h i

theorem fourColorCycle_no_two_step (i : Fin 3) (j : Fin 4) :
    fourColorCycle i (fourColorCycle i j) ≠ j := by
  have h : ∀ (i : Fin 3) (j : Fin 4),
      fourColorCycle i (fourColorCycle i j) ≠ j := by decide +kernel
  exact h i j

theorem fourColorCycle_small_fixed_iff (i : Fin 3) (j r : Fin 4) :
    (fourColorCycle i ^ r.val) j = j ↔ r = 0 := by
  have h : ∀ (i : Fin 3) (j r : Fin 4),
      (fourColorCycle i ^ r.val) j = j ↔ r = 0 := by decide +kernel
  exact h i j r

theorem fourColorCycle_order (i : Fin 3) : orderOf (fourColorCycle i) = 4 := by
  apply (orderOf_eq_iff (by decide : 0 < 4)).mpr
  refine ⟨fourColorCycle_fourth_power i, ?_⟩
  intro m hm hpos heq
  have hfix : (fourColorCycle i ^ m) (0 : Fin 4) = 0 := by rw [heq]; rfl
  have hz := (fourColorCycle_small_fixed_iff i 0 ⟨m, hm⟩).mp hfix
  have hv := congrArg Fin.val hz
  exact (Nat.ne_of_gt hpos) hv

theorem fourColorCycle_pow_fixed_iff (i : Fin 3) (j : Fin 4) (n : ℕ) :
    (fourColorCycle i ^ n) j = j ↔ 4 ∣ n := by
  have hp : fourColorCycle i ^ (n % 4) = fourColorCycle i ^ n := by
    simpa only [fourColorCycle_order i] using pow_mod_orderOf (fourColorCycle i) n
  rw [← hp]
  have hr : n % 4 < 4 := Nat.mod_lt _ (by decide)
  rw [show (fourColorCycle i ^ (n % 4)) j = j ↔
      (⟨n % 4, hr⟩ : Fin 4) = 0 from fourColorCycle_small_fixed_iff i j ⟨n % 4, hr⟩]
  constructor
  · intro h
    exact Nat.dvd_of_mod_eq_zero (congrArg Fin.val h)
  · intro h
    apply Fin.ext
    exact Nat.mod_eq_zero_of_dvd h

variable {V : Type u} {G : SimpleGraph V}

theorem follows_endColor {α : Type*} {x y : V} (p : G.Walk x y)
    (c : V → α) (σ : Equiv.Perm α) (hf : Follows p c σ) :
    c y = (σ ^ p.length) (c x) := by
  revert hf
  induction p with
  | nil => intro _; rfl
  | @cons x y z h p ih =>
    intro hf
    have hs := (follows_cons h p c σ).mp hf
    calc
      c z = (σ ^ p.length) (c y) := ih hs.2
      _ = (σ ^ (.cons h p : G.Walk x z).length) (c x) := by
        rw [hs.1, Walk.length_cons, pow_succ]
        rfl

theorem follows_fourColorCycle_length_dvd {x : V} (p : G.Walk x x)
    (c : V → Fin 4) (i : Fin 3) (hf : Follows p c (fourColorCycle i)) :
    4 ∣ p.length := by
  apply (fourColorCycle_pow_fixed_iff i (c x) p.length).mp
  exact (follows_endColor p c (fourColorCycle i) hf).symm

#print axioms fourColorCycle_no_two_step
#print axioms fourColorCycle_pow_fixed_iff
#print axioms follows_endColor
#print axioms follows_fourColorCycle_length_dvd

end TaskH
