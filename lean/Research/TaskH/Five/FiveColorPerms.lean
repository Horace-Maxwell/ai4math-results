import Research.TaskH.Five.Definitions

/-!
Twelve explicit complete five-color cycles, one representative per reversal
class. All finite color identities below are proved by the Lean kernel.
-/

set_option autoImplicit false

universe u

namespace TaskH.Five

open SimpleGraph

def fiveColorNext : Fin 12 → Fin 5 → Fin 5 :=
  ![![1, 2, 3, 4, 0], ![1, 2, 4, 0, 3],
    ![1, 3, 4, 2, 0], ![1, 3, 0, 4, 2],
    ![1, 4, 3, 0, 2], ![1, 4, 0, 2, 3],
    ![2, 3, 1, 4, 0], ![2, 4, 1, 0, 3],
    ![2, 4, 3, 1, 0], ![2, 3, 4, 0, 1],
    ![3, 2, 4, 1, 0], ![3, 4, 1, 2, 0]]

def fiveColorCycle (i : Fin 12) : Equiv.Perm (Fin 5) where
  toFun := fiveColorNext i
  invFun := Nat.iterate (fiveColorNext i) 4
  left_inv := by
    have h : ∀ (j : Fin 12) (x : Fin 5),
        Nat.iterate (fiveColorNext j) 4 (fiveColorNext j x) = x := by decide +kernel
    exact h i
  right_inv := by
    have h : ∀ (j : Fin 12) (x : Fin 5),
        fiveColorNext j (Nat.iterate (fiveColorNext j) 4 x) = x := by decide +kernel
    exact h i

theorem fiveColorCycle_fifth_power (i : Fin 12) : fiveColorCycle i ^ 5 = 1 := by
  have h : ∀ i : Fin 12, fiveColorCycle i ^ 5 = 1 := by decide +kernel
  exact h i

theorem fiveColorCycle_no_two_step (i : Fin 12) (j : Fin 5) :
    fiveColorCycle i (fiveColorCycle i j) ≠ j := by
  have h : ∀ (i : Fin 12) (j : Fin 5),
      fiveColorCycle i (fiveColorCycle i j) ≠ j := by decide +kernel
  exact h i j

theorem fiveColorCycle_small_fixed_iff (i : Fin 12) (j r : Fin 5) :
    (fiveColorCycle i ^ r.val) j = j ↔ r = 0 := by
  have h : ∀ (i : Fin 12) (j r : Fin 5),
      (fiveColorCycle i ^ r.val) j = j ↔ r = 0 := by decide +kernel
  exact h i j r

theorem fiveColorCycle_order (i : Fin 12) : orderOf (fiveColorCycle i) = 5 := by
  apply (orderOf_eq_iff (by decide : 0 < 5)).mpr
  refine ⟨fiveColorCycle_fifth_power i, ?_⟩
  intro m hm hpos heq
  have hfix : (fiveColorCycle i ^ m) (0 : Fin 5) = 0 := by rw [heq]; rfl
  have hz := (fiveColorCycle_small_fixed_iff i 0 ⟨m, hm⟩).mp hfix
  have hv := congrArg Fin.val hz
  exact (Nat.ne_of_gt hpos) hv

theorem fiveColorCycle_pow_fixed_iff (i : Fin 12) (j : Fin 5) (n : ℕ) :
    (fiveColorCycle i ^ n) j = j ↔ 5 ∣ n := by
  have hp : fiveColorCycle i ^ (n % 5) = fiveColorCycle i ^ n := by
    simpa only [fiveColorCycle_order i] using pow_mod_orderOf (fiveColorCycle i) n
  rw [← hp]
  have hr : n % 5 < 5 := Nat.mod_lt _ (by decide)
  rw [show (fiveColorCycle i ^ (n % 5)) j = j ↔
      (⟨n % 5, hr⟩ : Fin 5) = 0 from fiveColorCycle_small_fixed_iff i j ⟨n % 5, hr⟩]
  constructor
  · intro h
    exact Nat.dvd_of_mod_eq_zero (congrArg Fin.val h)
  · intro h
    apply Fin.ext
    exact Nat.mod_eq_zero_of_dvd h

variable {V : Type u} {G : SimpleGraph V}

theorem follows_fiveColorCycle_length_dvd {x : V} (p : G.Walk x x)
    (c : V → Fin 5) (i : Fin 12) (hf : Follows p c (fiveColorCycle i)) :
    5 ∣ p.length := by
  apply (fiveColorCycle_pow_fixed_iff i (c x) p.length).mp
  exact (TaskH.follows_endColor p c (fiveColorCycle i) hf).symm

end TaskH.Five

#print axioms TaskH.Five.fiveColorNext
#print axioms TaskH.Five.fiveColorCycle
#print axioms TaskH.Five.fiveColorCycle_fifth_power
#print axioms TaskH.Five.fiveColorCycle_no_two_step
#print axioms TaskH.Five.fiveColorCycle_small_fixed_iff
#print axioms TaskH.Five.fiveColorCycle_order
#print axioms TaskH.Five.fiveColorCycle_pow_fixed_iff
#print axioms TaskH.Five.follows_fiveColorCycle_length_dvd
