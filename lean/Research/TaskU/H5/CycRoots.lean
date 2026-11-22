import Research.TaskU.H5.CycPhase
import Research.TaskU.H5.CycEval

namespace TaskU.H5.Cyc5

lemma character_pow (t : ZMod 5) (n : ℕ) : (ZMod.stdAddChar t)^n = ZMod.stdAddChar ((n:ZMod 5)*t) := by
  rw [← AddChar.map_nsmul_eq_pow, nsmul_eq_mul]

lemma character_rel (t : ZMod 5) (ht : t ≠ 0) :
    1 + ZMod.stdAddChar t + (ZMod.stdAddChar t)^2 + (ZMod.stdAddChar t)^3 + (ZMod.stdAddChar t)^4 = 0 := by
  have hp : (ZMod.stdAddChar t)^5=1 := by
    rw [character_pow,show ((5:ℕ):ZMod 5)=0 by decide,zero_mul,AddChar.map_zero_eq_one]
  have hn : ZMod.stdAddChar t ≠ 1 := by
    intro h
    apply ht
    apply (ZMod.injective_stdAddChar (N:=5))
    simpa using h
  have h := show (ZMod.stdAddChar t-1)*(1+ZMod.stdAddChar t+(ZMod.stdAddChar t)^2+
      (ZMod.stdAddChar t)^3+(ZMod.stdAddChar t)^4)=0 by linear_combination hp
  exact (mul_eq_zero.mp h).resolve_left (sub_ne_zero.mpr hn)

lemma val_rootAt (k : ZMod 5) (z : ℂ) (hz : 1+z+z^2+z^3+z^4=0) : val (rootAt k) z = z^k.val := by
  fin_cases k <;> norm_num [rootAt,root,scalar,val,ZMod.val]
  linear_combination -hz

lemma val_rootAt_character (k t : ZMod 5) (ht : t ≠ 0) :
    val (rootAt k) (ZMod.stdAddChar t) = ZMod.stdAddChar (k*t) := by
  rw [val_rootAt _ _ (character_rel t ht),character_pow,ZMod.natCast_zmod_val]

lemma val_neg (v : V) (z : ℂ) : val (neg v) z = -val v z := by simp [val,neg]; ring

lemma val_conj_character (v : V) (t : ZMod 5) (ht : t ≠ 0) :
    val (conj v) (ZMod.stdAddChar t) = val v (ZMod.stdAddChar (-t)) := by
  rw [val_conj _ _ (character_rel t ht),character_pow]
  congr 2
  calc ((4:ℕ):ZMod 5)*t = (-1)*t := by congr 1
       _ = -t := neg_one_mul t

lemma phase_character (v : V) (k : ZMod 5) (h : conj v = neg (mul (rootAt k) v))
    (t : ZMod 5) (ht : t ≠ 0) : val v (ZMod.stdAddChar (-t)) =
      -(ZMod.stdAddChar (k*t)) * val v (ZMod.stdAddChar t) := by
  rw [← val_conj_character _ t ht,h,val_neg,val_mul _ _ _ (character_rel t ht),
    val_rootAt_character _ _ ht,neg_mul]

end TaskU.H5.Cyc5
