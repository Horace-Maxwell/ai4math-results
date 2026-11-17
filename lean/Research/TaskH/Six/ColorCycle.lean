import Research.TaskH.LayerTail

/-! Six-color rotation facts. Generic chain/walk lemmas remain imported. -/

set_option autoImplicit false

namespace TaskH.Six

theorem rotate_sixth_power : (finRotate 6) ^ 6 = 1 := by
  decide +kernel

theorem rotate_no_two_step (a : Fin 6) :
    finRotate 6 (finRotate 6 a) ≠ a := by
  have h : ∀ a : Fin 6, finRotate 6 (finRotate 6 a) ≠ a := by decide +kernel
  exact h a

theorem rotate_small_fixed_iff (a r : Fin 6) :
    ((finRotate 6) ^ r.val) a = a ↔ r = 0 := by
  have h : ∀ a r : Fin 6, ((finRotate 6) ^ r.val) a = a ↔ r = 0 := by
    decide +kernel
  exact h a r

theorem rotate_order : orderOf (finRotate 6) = 6 := by
  apply (orderOf_eq_iff (by decide : 0 < 6)).mpr
  refine ⟨rotate_sixth_power, ?_⟩
  intro m hm hpos heq
  have hfix : ((finRotate 6) ^ m) (0 : Fin 6) = 0 := by rw [heq]; rfl
  have hz := (rotate_small_fixed_iff 0 ⟨m, hm⟩).mp hfix
  have hv := congrArg Fin.val hz
  exact (Nat.ne_of_gt hpos) hv

theorem rotate_pow_fixed_iff (a : Fin 6) (n : ℕ) :
    ((finRotate 6) ^ n) a = a ↔ 6 ∣ n := by
  have hp : (finRotate 6) ^ (n % 6) = (finRotate 6) ^ n := by
    simpa only [rotate_order] using pow_mod_orderOf (finRotate 6) n
  rw [← hp]
  have hr : n % 6 < 6 := Nat.mod_lt _ (by decide)
  rw [show ((finRotate 6) ^ (n % 6)) a = a ↔
      (⟨n % 6, hr⟩ : Fin 6) = 0 from rotate_small_fixed_iff a ⟨n % 6, hr⟩]
  constructor
  · intro h
    exact Nat.dvd_of_mod_eq_zero (congrArg Fin.val h)
  · intro h
    apply Fin.ext
    exact Nat.mod_eq_zero_of_dvd h

end TaskH.Six

#print axioms TaskH.Six.rotate_sixth_power
#print axioms TaskH.Six.rotate_no_two_step
#print axioms TaskH.Six.rotate_small_fixed_iff
#print axioms TaskH.Six.rotate_order
#print axioms TaskH.Six.rotate_pow_fixed_iff
