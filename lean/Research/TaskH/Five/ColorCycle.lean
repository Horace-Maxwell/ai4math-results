import Research.TaskH.LayerTail

/-! Five-color rotation facts. Generic chain/walk lemmas remain imported. -/

namespace TaskH.Five

theorem rotate_fifth_power : (finRotate 5) ^ 5 = 1 := by
  decide +kernel

theorem rotate_no_two_step (a : Fin 5) :
    finRotate 5 (finRotate 5 a) ≠ a := by
  have h : ∀ a : Fin 5, finRotate 5 (finRotate 5 a) ≠ a := by decide +kernel
  exact h a

theorem rotate_small_fixed_iff (a r : Fin 5) :
    ((finRotate 5) ^ r.val) a = a ↔ r = 0 := by
  have h : ∀ a r : Fin 5, ((finRotate 5) ^ r.val) a = a ↔ r = 0 := by
    decide +kernel
  exact h a r

theorem rotate_order : orderOf (finRotate 5) = 5 := by
  apply (orderOf_eq_iff (by decide : 0 < 5)).mpr
  refine ⟨rotate_fifth_power, ?_⟩
  intro m hm hpos heq
  have hfix : ((finRotate 5) ^ m) (0 : Fin 5) = 0 := by rw [heq]; rfl
  have hz := (rotate_small_fixed_iff 0 ⟨m, hm⟩).mp hfix
  have hv := congrArg Fin.val hz
  exact (Nat.ne_of_gt hpos) hv

theorem rotate_pow_fixed_iff (a : Fin 5) (n : ℕ) :
    ((finRotate 5) ^ n) a = a ↔ 5 ∣ n := by
  have hp : (finRotate 5) ^ (n % 5) = (finRotate 5) ^ n := by
    simpa only [rotate_order] using pow_mod_orderOf (finRotate 5) n
  rw [← hp]
  have hr : n % 5 < 5 := Nat.mod_lt _ (by decide)
  rw [show ((finRotate 5) ^ (n % 5)) a = a ↔
      (⟨n % 5, hr⟩ : Fin 5) = 0 from rotate_small_fixed_iff a ⟨n % 5, hr⟩]
  constructor
  · intro h
    exact Nat.dvd_of_mod_eq_zero (congrArg Fin.val h)
  · intro h
    apply Fin.ext
    exact Nat.mod_eq_zero_of_dvd h

end TaskH.Five

#print axioms TaskH.Five.rotate_fifth_power
#print axioms TaskH.Five.rotate_no_two_step
#print axioms TaskH.Five.rotate_small_fixed_iff
#print axioms TaskH.Five.rotate_order
#print axioms TaskH.Five.rotate_pow_fixed_iff
