import Research.Backfill.Paper7.CRTPrimeAux03

/-! Recursive Lucas certificate candidates. Every candidate factor product,
recursive prime reference and binary modular-power equality is checked by Lean.
The JSON numerals are untrusted input, not proof hypotheses. -/
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 800000

namespace Paper7CRTPrimes
open Paper7Moduli

theorem prime_4611686018427387817 : Nat.Prime 4611686018427387817 := by
  have hneq_2 : (5 : ZMod 4611686018427387817) ^ ((4611686018427387817 - 1) / 2) ≠ 1 := by
    have hpow : (5 : ZMod 4611686018427387817) ^ ((4611686018427387817 - 1) / 2) = 4611686018427387816 := by
      reduce_mod_char
    rw [hpow]
    decide +kernel
  have hneq_3 : (5 : ZMod 4611686018427387817) ^ ((4611686018427387817 - 1) / 3) ≠ 1 := by
    have hpow : (5 : ZMod 4611686018427387817) ^ ((4611686018427387817 - 1) / 3) = 1124699437272757338 := by
      reduce_mod_char
    rw [hpow]
    decide +kernel
  have hneq_7 : (5 : ZMod 4611686018427387817) ^ ((4611686018427387817 - 1) / 7) ≠ 1 := by
    have hpow : (5 : ZMod 4611686018427387817) ^ ((4611686018427387817 - 1) / 7) = 967187804784749880 := by
      reduce_mod_char
    rw [hpow]
    decide +kernel
  have hneq_67 : (5 : ZMod 4611686018427387817) ^ ((4611686018427387817 - 1) / 67) ≠ 1 := by
    have hpow : (5 : ZMod 4611686018427387817) ^ ((4611686018427387817 - 1) / 67) = 1705239726277590146 := by
      reduce_mod_char
    rw [hpow]
    decide +kernel
  have hneq_97 : (5 : ZMod 4611686018427387817) ^ ((4611686018427387817 - 1) / 97) ≠ 1 := by
    have hpow : (5 : ZMod 4611686018427387817) ^ ((4611686018427387817 - 1) / 97) = 4528566601136566078 := by
      reduce_mod_char
    rw [hpow]
    decide +kernel
  have hneq_4273 : (5 : ZMod 4611686018427387817) ^ ((4611686018427387817 - 1) / 4273) ≠ 1 := by
    have hpow : (5 : ZMod 4611686018427387817) ^ ((4611686018427387817 - 1) / 4273) = 1994828251344675459 := by
      reduce_mod_char
    rw [hpow]
    decide +kernel
  have hneq_4759 : (5 : ZMod 4611686018427387817) ^ ((4611686018427387817 - 1) / 4759) ≠ 1 := by
    have hpow : (5 : ZMod 4611686018427387817) ^ ((4611686018427387817 - 1) / 4759) = 758462057960180643 := by
      reduce_mod_char
    rw [hpow]
    decide +kernel
  have hneq_207709 : (5 : ZMod 4611686018427387817) ^ ((4611686018427387817 - 1) / 207709) ≠ 1 := by
    have hpow : (5 : ZMod 4611686018427387817) ^ ((4611686018427387817 - 1) / 207709) = 1466745583536028106 := by
      reduce_mod_char
    rw [hpow]
    decide +kernel
  refine prime_of_lucas_list 4611686018427387817 5 [2, 2, 2, 3, 7, 67, 97, 4273, 4759, 207709] ?_ ?_ ?_ ?_
  · norm_num [List.prod_cons, List.prod_nil]
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Paper7Moduli.prime_2
    · exact Paper7Moduli.prime_2
    · exact Paper7Moduli.prime_2
    · exact Paper7Moduli.prime_3
    · exact Paper7Moduli.prime_7
    · exact Paper7CRTPrimes.prime_67
    · exact Paper7CRTPrimes.prime_97
    · exact Paper7CRTPrimes.prime_4273
    · exact Paper7CRTPrimes.prime_4759
    · exact Paper7CRTPrimes.prime_207709
  · reduce_mod_char
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hneq_2
    · exact hneq_2
    · exact hneq_2
    · exact hneq_3
    · exact hneq_7
    · exact hneq_67
    · exact hneq_97
    · exact hneq_4273
    · exact hneq_4759
    · exact hneq_207709

#print axioms Paper7CRTPrimes.prime_4611686018427387817

end Paper7CRTPrimes
