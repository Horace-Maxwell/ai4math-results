import Research.Backfill.Paper7.ModuliPrimeCertificates

/-! Recursive Lucas certificate candidates. Every candidate factor product,
recursive prime reference and binary modular-power equality is checked by Lean.
The JSON numerals are untrusted input, not proof hypotheses. -/
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 800000

namespace Paper7CRTPrimes
open Paper7Moduli

theorem prime_1289 : Nat.Prime 1289 := by
  have hneq_2 : (6 : ZMod 1289) ^ ((1289 - 1) / 2) ≠ 1 := by
    have hpow : (6 : ZMod 1289) ^ ((1289 - 1) / 2) = 1288 := by
      reduce_mod_char
    rw [hpow]
    decide +kernel
  have hneq_7 : (6 : ZMod 1289) ^ ((1289 - 1) / 7) ≠ 1 := by
    have hpow : (6 : ZMod 1289) ^ ((1289 - 1) / 7) = 1085 := by
      reduce_mod_char
    rw [hpow]
    decide +kernel
  have hneq_23 : (6 : ZMod 1289) ^ ((1289 - 1) / 23) ≠ 1 := by
    have hpow : (6 : ZMod 1289) ^ ((1289 - 1) / 23) = 916 := by
      reduce_mod_char
    rw [hpow]
    decide +kernel
  refine prime_of_lucas_list 1289 6 [2, 2, 2, 7, 23] ?_ ?_ ?_ ?_
  · norm_num [List.prod_cons, List.prod_nil]
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact Paper7Moduli.prime_2
    · exact Paper7Moduli.prime_2
    · exact Paper7Moduli.prime_2
    · exact Paper7Moduli.prime_7
    · exact Paper7Moduli.prime_23
  · reduce_mod_char
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact hneq_2
    · exact hneq_2
    · exact hneq_2
    · exact hneq_7
    · exact hneq_23

#print axioms Paper7CRTPrimes.prime_1289

theorem prime_37 : Nat.Prime 37 := by
  have hneq_2 : (2 : ZMod 37) ^ ((37 - 1) / 2) ≠ 1 := by
    have hpow : (2 : ZMod 37) ^ ((37 - 1) / 2) = 36 := by
      reduce_mod_char
    rw [hpow]
    decide +kernel
  have hneq_3 : (2 : ZMod 37) ^ ((37 - 1) / 3) ≠ 1 := by
    have hpow : (2 : ZMod 37) ^ ((37 - 1) / 3) = 26 := by
      reduce_mod_char
    rw [hpow]
    decide +kernel
  refine prime_of_lucas_list 37 2 [2, 2, 3, 3] ?_ ?_ ?_ ?_
  · norm_num [List.prod_cons, List.prod_nil]
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact Paper7Moduli.prime_2
    · exact Paper7Moduli.prime_2
    · exact Paper7Moduli.prime_3
    · exact Paper7Moduli.prime_3
  · reduce_mod_char
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact hneq_2
    · exact hneq_2
    · exact hneq_3
    · exact hneq_3

#print axioms Paper7CRTPrimes.prime_37

theorem prime_223 : Nat.Prime 223 := by
  have hneq_2 : (3 : ZMod 223) ^ ((223 - 1) / 2) ≠ 1 := by
    have hpow : (3 : ZMod 223) ^ ((223 - 1) / 2) = 222 := by
      reduce_mod_char
    rw [hpow]
    decide +kernel
  have hneq_3 : (3 : ZMod 223) ^ ((223 - 1) / 3) ≠ 1 := by
    have hpow : (3 : ZMod 223) ^ ((223 - 1) / 3) = 183 := by
      reduce_mod_char
    rw [hpow]
    decide +kernel
  have hneq_37 : (3 : ZMod 223) ^ ((223 - 1) / 37) ≠ 1 := by
    have hpow : (3 : ZMod 223) ^ ((223 - 1) / 37) = 60 := by
      reduce_mod_char
    rw [hpow]
    decide +kernel
  refine prime_of_lucas_list 223 3 [2, 3, 37] ?_ ?_ ?_ ?_
  · norm_num [List.prod_cons, List.prod_nil]
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact Paper7Moduli.prime_2
    · exact Paper7Moduli.prime_3
    · exact Paper7CRTPrimes.prime_37
  · reduce_mod_char
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact hneq_2
    · exact hneq_3
    · exact hneq_37

#print axioms Paper7CRTPrimes.prime_223

theorem prime_127 : Nat.Prime 127 := by
  have hneq_2 : (3 : ZMod 127) ^ ((127 - 1) / 2) ≠ 1 := by
    have hpow : (3 : ZMod 127) ^ ((127 - 1) / 2) = 126 := by
      reduce_mod_char
    rw [hpow]
    decide +kernel
  have hneq_3 : (3 : ZMod 127) ^ ((127 - 1) / 3) ≠ 1 := by
    have hpow : (3 : ZMod 127) ^ ((127 - 1) / 3) = 107 := by
      reduce_mod_char
    rw [hpow]
    decide +kernel
  have hneq_7 : (3 : ZMod 127) ^ ((127 - 1) / 7) ≠ 1 := by
    have hpow : (3 : ZMod 127) ^ ((127 - 1) / 7) = 4 := by
      reduce_mod_char
    rw [hpow]
    decide +kernel
  refine prime_of_lucas_list 127 3 [2, 3, 3, 7] ?_ ?_ ?_ ?_
  · norm_num [List.prod_cons, List.prod_nil]
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact Paper7Moduli.prime_2
    · exact Paper7Moduli.prime_3
    · exact Paper7Moduli.prime_3
    · exact Paper7Moduli.prime_7
  · reduce_mod_char
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact hneq_2
    · exact hneq_3
    · exact hneq_3
    · exact hneq_7

#print axioms Paper7CRTPrimes.prime_127

theorem prime_47 : Nat.Prime 47 := by
  have hneq_2 : (5 : ZMod 47) ^ ((47 - 1) / 2) ≠ 1 := by
    have hpow : (5 : ZMod 47) ^ ((47 - 1) / 2) = 46 := by
      reduce_mod_char
    rw [hpow]
    decide +kernel
  have hneq_23 : (5 : ZMod 47) ^ ((47 - 1) / 23) ≠ 1 := by
    have hpow : (5 : ZMod 47) ^ ((47 - 1) / 23) = 25 := by
      reduce_mod_char
    rw [hpow]
    decide +kernel
  refine prime_of_lucas_list 47 5 [2, 23] ?_ ?_ ?_ ?_
  · norm_num [List.prod_cons, List.prod_nil]
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact Paper7Moduli.prime_2
    · exact Paper7Moduli.prime_23
  · reduce_mod_char
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact hneq_2
    · exact hneq_23

#print axioms Paper7CRTPrimes.prime_47

theorem prime_659 : Nat.Prime 659 := by
  have hneq_2 : (2 : ZMod 659) ^ ((659 - 1) / 2) ≠ 1 := by
    have hpow : (2 : ZMod 659) ^ ((659 - 1) / 2) = 658 := by
      reduce_mod_char
    rw [hpow]
    decide +kernel
  have hneq_7 : (2 : ZMod 659) ^ ((659 - 1) / 7) ≠ 1 := by
    have hpow : (2 : ZMod 659) ^ ((659 - 1) / 7) = 307 := by
      reduce_mod_char
    rw [hpow]
    decide +kernel
  have hneq_47 : (2 : ZMod 659) ^ ((659 - 1) / 47) ≠ 1 := by
    have hpow : (2 : ZMod 659) ^ ((659 - 1) / 47) = 568 := by
      reduce_mod_char
    rw [hpow]
    decide +kernel
  refine prime_of_lucas_list 659 2 [2, 7, 47] ?_ ?_ ?_ ?_
  · norm_num [List.prod_cons, List.prod_nil]
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact Paper7Moduli.prime_2
    · exact Paper7Moduli.prime_7
    · exact Paper7CRTPrimes.prime_47
  · reduce_mod_char
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact hneq_2
    · exact hneq_7
    · exact hneq_47

#print axioms Paper7CRTPrimes.prime_659

theorem prime_251 : Nat.Prime 251 := by
  have hneq_2 : (6 : ZMod 251) ^ ((251 - 1) / 2) ≠ 1 := by
    have hpow : (6 : ZMod 251) ^ ((251 - 1) / 2) = 250 := by
      reduce_mod_char
    rw [hpow]
    decide +kernel
  have hneq_5 : (6 : ZMod 251) ^ ((251 - 1) / 5) ≠ 1 := by
    have hpow : (6 : ZMod 251) ^ ((251 - 1) / 5) = 219 := by
      reduce_mod_char
    rw [hpow]
    decide +kernel
  refine prime_of_lucas_list 251 6 [2, 5, 5, 5] ?_ ?_ ?_ ?_
  · norm_num [List.prod_cons, List.prod_nil]
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact Paper7Moduli.prime_2
    · exact Paper7Moduli.prime_5
    · exact Paper7Moduli.prime_5
    · exact Paper7Moduli.prime_5
  · reduce_mod_char
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact hneq_2
    · exact hneq_5
    · exact hneq_5
    · exact hneq_5

#print axioms Paper7CRTPrimes.prime_251

theorem prime_503 : Nat.Prime 503 := by
  have hneq_2 : (5 : ZMod 503) ^ ((503 - 1) / 2) ≠ 1 := by
    have hpow : (5 : ZMod 503) ^ ((503 - 1) / 2) = 502 := by
      reduce_mod_char
    rw [hpow]
    decide +kernel
  have hneq_251 : (5 : ZMod 503) ^ ((503 - 1) / 251) ≠ 1 := by
    have hpow : (5 : ZMod 503) ^ ((503 - 1) / 251) = 25 := by
      reduce_mod_char
    rw [hpow]
    decide +kernel
  refine prime_of_lucas_list 503 5 [2, 251] ?_ ?_ ?_ ?_
  · norm_num [List.prod_cons, List.prod_nil]
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact Paper7Moduli.prime_2
    · exact Paper7CRTPrimes.prime_251
  · reduce_mod_char
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact hneq_2
    · exact hneq_251

#print axioms Paper7CRTPrimes.prime_503

theorem prime_7043 : Nat.Prime 7043 := by
  have hneq_2 : (2 : ZMod 7043) ^ ((7043 - 1) / 2) ≠ 1 := by
    have hpow : (2 : ZMod 7043) ^ ((7043 - 1) / 2) = 7042 := by
      reduce_mod_char
    rw [hpow]
    decide +kernel
  have hneq_7 : (2 : ZMod 7043) ^ ((7043 - 1) / 7) ≠ 1 := by
    have hpow : (2 : ZMod 7043) ^ ((7043 - 1) / 7) = 6890 := by
      reduce_mod_char
    rw [hpow]
    decide +kernel
  have hneq_503 : (2 : ZMod 7043) ^ ((7043 - 1) / 503) ≠ 1 := by
    have hpow : (2 : ZMod 7043) ^ ((7043 - 1) / 503) = 2298 := by
      reduce_mod_char
    rw [hpow]
    decide +kernel
  refine prime_of_lucas_list 7043 2 [2, 7, 503] ?_ ?_ ?_ ?_
  · norm_num [List.prod_cons, List.prod_nil]
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact Paper7Moduli.prime_2
    · exact Paper7Moduli.prime_7
    · exact Paper7CRTPrimes.prime_503
  · reduce_mod_char
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact hneq_2
    · exact hneq_7
    · exact hneq_503

#print axioms Paper7CRTPrimes.prime_7043

theorem prime_14087 : Nat.Prime 14087 := by
  have hneq_2 : (5 : ZMod 14087) ^ ((14087 - 1) / 2) ≠ 1 := by
    have hpow : (5 : ZMod 14087) ^ ((14087 - 1) / 2) = 14086 := by
      reduce_mod_char
    rw [hpow]
    decide +kernel
  have hneq_7043 : (5 : ZMod 14087) ^ ((14087 - 1) / 7043) ≠ 1 := by
    have hpow : (5 : ZMod 14087) ^ ((14087 - 1) / 7043) = 25 := by
      reduce_mod_char
    rw [hpow]
    decide +kernel
  refine prime_of_lucas_list 14087 5 [2, 7043] ?_ ?_ ?_ ?_
  · norm_num [List.prod_cons, List.prod_nil]
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact Paper7Moduli.prime_2
    · exact Paper7CRTPrimes.prime_7043
  · reduce_mod_char
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact hneq_2
    · exact hneq_7043

#print axioms Paper7CRTPrimes.prime_14087

end Paper7CRTPrimes
