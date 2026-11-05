import Research.Backfill.Paper7.CRTPrimeAux03

/-! Recursive Lucas certificate candidates. Every candidate factor product,
recursive prime reference and binary modular-power equality is checked by Lean.
The JSON numerals are untrusted input, not proof hypotheses. -/
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 800000

namespace Paper7CRTPrimes
open Paper7Moduli

theorem prime_4611686018427387787 : Nat.Prime 4611686018427387787 := by
  have hneq_2 : (2 : ZMod 4611686018427387787) ^ ((4611686018427387787 - 1) / 2) ≠ 1 := by
    have hpow : (2 : ZMod 4611686018427387787) ^ ((4611686018427387787 - 1) / 2) = 4611686018427387786 := by
      reduce_mod_char
    rw [hpow]
    decide +kernel
  have hneq_3 : (2 : ZMod 4611686018427387787) ^ ((4611686018427387787 - 1) / 3) ≠ 1 := by
    have hpow : (2 : ZMod 4611686018427387787) ^ ((4611686018427387787 - 1) / 3) = 890761647704586931 := by
      reduce_mod_char
    rw [hpow]
    decide +kernel
  have hneq_4488751 : (2 : ZMod 4611686018427387787) ^ ((4611686018427387787 - 1) / 4488751) ≠ 1 := by
    have hpow : (2 : ZMod 4611686018427387787) ^ ((4611686018427387787 - 1) / 4488751) = 504338135944733434 := by
      reduce_mod_char
    rw [hpow]
    decide +kernel
  have hneq_171231225881 : (2 : ZMod 4611686018427387787) ^ ((4611686018427387787 - 1) / 171231225881) ≠ 1 := by
    have hpow : (2 : ZMod 4611686018427387787) ^ ((4611686018427387787 - 1) / 171231225881) = 3260536713239837528 := by
      reduce_mod_char
    rw [hpow]
    decide +kernel
  refine prime_of_lucas_list 4611686018427387787 2 [2, 3, 4488751, 171231225881] ?_ ?_ ?_ ?_
  · norm_num [List.prod_cons, List.prod_nil]
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact Paper7Moduli.prime_2
    · exact Paper7Moduli.prime_3
    · exact Paper7CRTPrimes.prime_4488751
    · exact Paper7CRTPrimes.prime_171231225881
  · reduce_mod_char
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact hneq_2
    · exact hneq_3
    · exact hneq_4488751
    · exact hneq_171231225881

#print axioms Paper7CRTPrimes.prime_4611686018427387787

end Paper7CRTPrimes
