import Research.Backfill.Paper7.CRTPrimeAux03

/-! Recursive Lucas certificate candidates. Every candidate factor product,
recursive prime reference and binary modular-power equality is checked by Lean.
The JSON numerals are untrusted input, not proof hypotheses. -/
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 800000

namespace Paper7CRTPrimes
open Paper7Moduli

theorem prime_4611686018427387761 : Nat.Prime 4611686018427387761 := by
  have hneq_2 : (3 : ZMod 4611686018427387761) ^ ((4611686018427387761 - 1) / 2) ≠ 1 := by
    have hpow : (3 : ZMod 4611686018427387761) ^ ((4611686018427387761 - 1) / 2) = 4611686018427387760 := by
      reduce_mod_char
    rw [hpow]
    decide +kernel
  have hneq_5 : (3 : ZMod 4611686018427387761) ^ ((4611686018427387761 - 1) / 5) ≠ 1 := by
    have hpow : (3 : ZMod 4611686018427387761) ^ ((4611686018427387761 - 1) / 5) = 351299331798424327 := by
      reduce_mod_char
    rw [hpow]
    decide +kernel
  have hneq_7 : (3 : ZMod 4611686018427387761) ^ ((4611686018427387761 - 1) / 7) ≠ 1 := by
    have hpow : (3 : ZMod 4611686018427387761) ^ ((4611686018427387761 - 1) / 7) = 1795934395461563772 := by
      reduce_mod_char
    rw [hpow]
    decide +kernel
  have hneq_1901 : (3 : ZMod 4611686018427387761) ^ ((4611686018427387761 - 1) / 1901) ≠ 1 := by
    have hpow : (3 : ZMod 4611686018427387761) ^ ((4611686018427387761 - 1) / 1901) = 4582964390891236787 := by
      reduce_mod_char
    rw [hpow]
    decide +kernel
  have hneq_8069 : (3 : ZMod 4611686018427387761) ^ ((4611686018427387761 - 1) / 8069) ≠ 1 := by
    have hpow : (3 : ZMod 4611686018427387761) ^ ((4611686018427387761 - 1) / 8069) = 1716771857223593292 := by
      reduce_mod_char
    rw [hpow]
    decide +kernel
  have hneq_536870909 : (3 : ZMod 4611686018427387761) ^ ((4611686018427387761 - 1) / 536870909) ≠ 1 := by
    have hpow : (3 : ZMod 4611686018427387761) ^ ((4611686018427387761 - 1) / 536870909) = 3714375429996400171 := by
      reduce_mod_char
    rw [hpow]
    decide +kernel
  refine prime_of_lucas_list 4611686018427387761 3 [2, 2, 2, 2, 5, 7, 1901, 8069, 536870909] ?_ ?_ ?_ ?_
  · norm_num [List.prod_cons, List.prod_nil]
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Paper7Moduli.prime_2
    · exact Paper7Moduli.prime_2
    · exact Paper7Moduli.prime_2
    · exact Paper7Moduli.prime_2
    · exact Paper7Moduli.prime_5
    · exact Paper7Moduli.prime_7
    · exact Paper7CRTPrimes.prime_1901
    · exact Paper7CRTPrimes.prime_8069
    · exact Paper7CRTPrimes.prime_536870909
  · reduce_mod_char
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hneq_2
    · exact hneq_2
    · exact hneq_2
    · exact hneq_2
    · exact hneq_5
    · exact hneq_7
    · exact hneq_1901
    · exact hneq_8069
    · exact hneq_536870909

#print axioms Paper7CRTPrimes.prime_4611686018427387761

end Paper7CRTPrimes
