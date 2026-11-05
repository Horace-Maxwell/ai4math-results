import Research.Backfill.Paper7.CRTPrimeAux03

/-! Recursive Lucas certificate candidates. Every candidate factor product,
recursive prime reference and binary modular-power equality is checked by Lean.
The JSON numerals are untrusted input, not proof hypotheses. -/
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 800000

namespace Paper7CRTPrimes
open Paper7Moduli

theorem prime_4611686018427387847 : Nat.Prime 4611686018427387847 := by
  have hneq_2 : (6 : ZMod 4611686018427387847) ^ ((4611686018427387847 - 1) / 2) ≠ 1 := by
    have hpow : (6 : ZMod 4611686018427387847) ^ ((4611686018427387847 - 1) / 2) = 4611686018427387846 := by
      reduce_mod_char
    rw [hpow]
    decide +kernel
  have hneq_3 : (6 : ZMod 4611686018427387847) ^ ((4611686018427387847 - 1) / 3) ≠ 1 := by
    have hpow : (6 : ZMod 4611686018427387847) ^ ((4611686018427387847 - 1) / 3) = 654667280544682955 := by
      reduce_mod_char
    rw [hpow]
    decide +kernel
  have hneq_1289 : (6 : ZMod 4611686018427387847) ^ ((4611686018427387847 - 1) / 1289) ≠ 1 := by
    have hpow : (6 : ZMod 4611686018427387847) ^ ((4611686018427387847 - 1) / 1289) = 2323342967876120209 := by
      reduce_mod_char
    rw [hpow]
    decide +kernel
  have hneq_198762435067123 : (6 : ZMod 4611686018427387847) ^ ((4611686018427387847 - 1) / 198762435067123) ≠ 1 := by
    have hpow : (6 : ZMod 4611686018427387847) ^ ((4611686018427387847 - 1) / 198762435067123) = 1773082713526747453 := by
      reduce_mod_char
    rw [hpow]
    decide +kernel
  refine prime_of_lucas_list 4611686018427387847 6 [2, 3, 3, 1289, 198762435067123] ?_ ?_ ?_ ?_
  · norm_num [List.prod_cons, List.prod_nil]
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact Paper7Moduli.prime_2
    · exact Paper7Moduli.prime_3
    · exact Paper7Moduli.prime_3
    · exact Paper7CRTPrimes.prime_1289
    · exact Paper7CRTPrimes.prime_198762435067123
  · reduce_mod_char
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact hneq_2
    · exact hneq_3
    · exact hneq_3
    · exact hneq_1289
    · exact hneq_198762435067123

#print axioms Paper7CRTPrimes.prime_4611686018427387847

end Paper7CRTPrimes
