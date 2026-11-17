import Research.TaskH.LayerTail

/-! Seven-color rotation facts. Generic chain/walk lemmas remain imported. -/

set_option autoImplicit false

namespace TaskH.Seven

theorem rotate_seventh_power : (finRotate 7) ^ 7 = 1 := by
  decide +kernel

theorem rotate_no_two_step (a : Fin 7) :
    finRotate 7 (finRotate 7 a) ≠ a := by
  have h : ∀ a : Fin 7, finRotate 7 (finRotate 7 a) ≠ a := by decide +kernel
  exact h a

theorem rotate_small_fixed_iff (a r : Fin 7) :
    ((finRotate 7) ^ r.val) a = a ↔ r = 0 := by
  have h : ∀ a r : Fin 7, ((finRotate 7) ^ r.val) a = a ↔ r = 0 := by
    decide +kernel
  exact h a r

theorem rotate_order : orderOf (finRotate 7) = 7 := by
  apply (orderOf_eq_iff (by decide : 0 < 7)).mpr
  refine ⟨rotate_seventh_power, ?_⟩
  intro m hm hpos heq
  have hfix : ((finRotate 7) ^ m) (0 : Fin 7) = 0 := by rw [heq]; rfl
  have hz := (rotate_small_fixed_iff 0 ⟨m, hm⟩).mp hfix
  have hv := congrArg Fin.val hz
  exact (Nat.ne_of_gt hpos) hv

theorem rotate_pow_fixed_iff (a : Fin 7) (n : ℕ) :
    ((finRotate 7) ^ n) a = a ↔ 7 ∣ n := by
  have hp : (finRotate 7) ^ (n % 7) = (finRotate 7) ^ n := by
    simpa only [rotate_order] using pow_mod_orderOf (finRotate 7) n
  rw [← hp]
  have hr : n % 7 < 7 := Nat.mod_lt _ (by decide)
  rw [show ((finRotate 7) ^ (n % 7)) a = a ↔
      (⟨n % 7, hr⟩ : Fin 7) = 0 from rotate_small_fixed_iff a ⟨n % 7, hr⟩]
  constructor
  · intro h
    exact Nat.dvd_of_mod_eq_zero (congrArg Fin.val h)
  · intro h
    apply Fin.ext
    exact Nat.mod_eq_zero_of_dvd h

end TaskH.Seven

#print axioms TaskH.Seven.rotate_seventh_power
#print axioms TaskH.Seven.rotate_no_two_step
#print axioms TaskH.Seven.rotate_small_fixed_iff
#print axioms TaskH.Seven.rotate_order
#print axioms TaskH.Seven.rotate_pow_fixed_iff
