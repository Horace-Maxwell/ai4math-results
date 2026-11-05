import Research.Backfill.Paper7.CRTPrimeAux02

/-! Recursive Lucas certificate candidates. Every candidate factor product,
recursive prime reference and binary modular-power equality is checked by Lean.
The JSON numerals are untrusted input, not proof hypotheses. -/
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 800000

namespace Paper7CRTPrimes
open Paper7Moduli

theorem prime_197 : Nat.Prime 197 := by
  have hneq_2 : (2 : ZMod 197) ^ ((197 - 1) / 2) ≠ 1 := by
    have hpow : (2 : ZMod 197) ^ ((197 - 1) / 2) = 196 := by
      reduce_mod_char
    rw [hpow]
    decide +kernel
  have hneq_7 : (2 : ZMod 197) ^ ((197 - 1) / 7) ≠ 1 := by
    have hpow : (2 : ZMod 197) ^ ((197 - 1) / 7) = 104 := by
      reduce_mod_char
    rw [hpow]
    decide +kernel
  refine prime_of_lucas_list 197 2 [2, 2, 7, 7] ?_ ?_ ?_ ?_
  · norm_num [List.prod_cons, List.prod_nil]
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact Paper7Moduli.prime_2
    · exact Paper7Moduli.prime_2
    · exact Paper7Moduli.prime_7
    · exact Paper7Moduli.prime_7
  · reduce_mod_char
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact hneq_2
    · exact hneq_2
    · exact hneq_7
    · exact hneq_7

#print axioms Paper7CRTPrimes.prime_197

theorem prime_487 : Nat.Prime 487 := by
  have hneq_2 : (3 : ZMod 487) ^ ((487 - 1) / 2) ≠ 1 := by
    have hpow : (3 : ZMod 487) ^ ((487 - 1) / 2) = 486 := by
      reduce_mod_char
    rw [hpow]
    decide +kernel
  have hneq_3 : (3 : ZMod 487) ^ ((487 - 1) / 3) ≠ 1 := by
    have hpow : (3 : ZMod 487) ^ ((487 - 1) / 3) = 232 := by
      reduce_mod_char
    rw [hpow]
    decide +kernel
  refine prime_of_lucas_list 487 3 [2, 3, 3, 3, 3, 3] ?_ ?_ ?_ ?_
  · norm_num [List.prod_cons, List.prod_nil]
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact Paper7Moduli.prime_2
    · exact Paper7Moduli.prime_3
    · exact Paper7Moduli.prime_3
    · exact Paper7Moduli.prime_3
    · exact Paper7Moduli.prime_3
    · exact Paper7Moduli.prime_3
  · reduce_mod_char
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hneq_2
    · exact hneq_3
    · exact hneq_3
    · exact hneq_3
    · exact hneq_3
    · exact hneq_3

#print axioms Paper7CRTPrimes.prime_487

theorem prime_11689 : Nat.Prime 11689 := by
  have hneq_2 : (7 : ZMod 11689) ^ ((11689 - 1) / 2) ≠ 1 := by
    have hpow : (7 : ZMod 11689) ^ ((11689 - 1) / 2) = 11688 := by
      reduce_mod_char
    rw [hpow]
    decide +kernel
  have hneq_3 : (7 : ZMod 11689) ^ ((11689 - 1) / 3) ≠ 1 := by
    have hpow : (7 : ZMod 11689) ^ ((11689 - 1) / 3) = 9788 := by
      reduce_mod_char
    rw [hpow]
    decide +kernel
  have hneq_487 : (7 : ZMod 11689) ^ ((11689 - 1) / 487) ≠ 1 := by
    have hpow : (7 : ZMod 11689) ^ ((11689 - 1) / 487) = 11362 := by
      reduce_mod_char
    rw [hpow]
    decide +kernel
  refine prime_of_lucas_list 11689 7 [2, 2, 2, 3, 487] ?_ ?_ ?_ ?_
  · norm_num [List.prod_cons, List.prod_nil]
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact Paper7Moduli.prime_2
    · exact Paper7Moduli.prime_2
    · exact Paper7Moduli.prime_2
    · exact Paper7Moduli.prime_3
    · exact Paper7CRTPrimes.prime_487
  · reduce_mod_char
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact hneq_2
    · exact hneq_2
    · exact hneq_2
    · exact hneq_3
    · exact hneq_487

#print axioms Paper7CRTPrimes.prime_11689

theorem prime_171231225881 : Nat.Prime 171231225881 := by
  have hneq_2 : (3 : ZMod 171231225881) ^ ((171231225881 - 1) / 2) ≠ 1 := by
    have hpow : (3 : ZMod 171231225881) ^ ((171231225881 - 1) / 2) = 171231225880 := by
      reduce_mod_char
    rw [hpow]
    decide +kernel
  have hneq_5 : (3 : ZMod 171231225881) ^ ((171231225881 - 1) / 5) ≠ 1 := by
    have hpow : (3 : ZMod 171231225881) ^ ((171231225881 - 1) / 5) = 140400223321 := by
      reduce_mod_char
    rw [hpow]
    decide +kernel
  have hneq_11 : (3 : ZMod 171231225881) ^ ((171231225881 - 1) / 11) ≠ 1 := by
    have hpow : (3 : ZMod 171231225881) ^ ((171231225881 - 1) / 11) = 162784293804 := by
      reduce_mod_char
    rw [hpow]
    decide +kernel
  have hneq_13 : (3 : ZMod 171231225881) ^ ((171231225881 - 1) / 13) ≠ 1 := by
    have hpow : (3 : ZMod 171231225881) ^ ((171231225881 - 1) / 13) = 17957886662 := by
      reduce_mod_char
    rw [hpow]
    decide +kernel
  have hneq_197 : (3 : ZMod 171231225881) ^ ((171231225881 - 1) / 197) ≠ 1 := by
    have hpow : (3 : ZMod 171231225881) ^ ((171231225881 - 1) / 197) = 53674221860 := by
      reduce_mod_char
    rw [hpow]
    decide +kernel
  have hneq_11689 : (3 : ZMod 171231225881) ^ ((171231225881 - 1) / 11689) ≠ 1 := by
    have hpow : (3 : ZMod 171231225881) ^ ((171231225881 - 1) / 11689) = 162322610211 := by
      reduce_mod_char
    rw [hpow]
    decide +kernel
  refine prime_of_lucas_list 171231225881 3 [2, 2, 2, 5, 11, 13, 13, 197, 11689] ?_ ?_ ?_ ?_
  · norm_num [List.prod_cons, List.prod_nil]
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Paper7Moduli.prime_2
    · exact Paper7Moduli.prime_2
    · exact Paper7Moduli.prime_2
    · exact Paper7Moduli.prime_5
    · exact Paper7Moduli.prime_11
    · exact Paper7Moduli.prime_13
    · exact Paper7Moduli.prime_13
    · exact Paper7CRTPrimes.prime_197
    · exact Paper7CRTPrimes.prime_11689
  · reduce_mod_char
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hneq_2
    · exact hneq_2
    · exact hneq_2
    · exact hneq_5
    · exact hneq_11
    · exact hneq_13
    · exact hneq_13
    · exact hneq_197
    · exact hneq_11689

#print axioms Paper7CRTPrimes.prime_171231225881

theorem prime_1901 : Nat.Prime 1901 := by
  have hneq_2 : (2 : ZMod 1901) ^ ((1901 - 1) / 2) ≠ 1 := by
    have hpow : (2 : ZMod 1901) ^ ((1901 - 1) / 2) = 1900 := by
      reduce_mod_char
    rw [hpow]
    decide +kernel
  have hneq_5 : (2 : ZMod 1901) ^ ((1901 - 1) / 5) ≠ 1 := by
    have hpow : (2 : ZMod 1901) ^ ((1901 - 1) / 5) = 1126 := by
      reduce_mod_char
    rw [hpow]
    decide +kernel
  have hneq_19 : (2 : ZMod 1901) ^ ((1901 - 1) / 19) ≠ 1 := by
    have hpow : (2 : ZMod 1901) ^ ((1901 - 1) / 19) = 1233 := by
      reduce_mod_char
    rw [hpow]
    decide +kernel
  refine prime_of_lucas_list 1901 2 [2, 2, 5, 5, 19] ?_ ?_ ?_ ?_
  · norm_num [List.prod_cons, List.prod_nil]
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact Paper7Moduli.prime_2
    · exact Paper7Moduli.prime_2
    · exact Paper7Moduli.prime_5
    · exact Paper7Moduli.prime_5
    · exact Paper7Moduli.prime_19
  · reduce_mod_char
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact hneq_2
    · exact hneq_2
    · exact hneq_5
    · exact hneq_5
    · exact hneq_19

#print axioms Paper7CRTPrimes.prime_1901

theorem prime_2017 : Nat.Prime 2017 := by
  have hneq_2 : (5 : ZMod 2017) ^ ((2017 - 1) / 2) ≠ 1 := by
    have hpow : (5 : ZMod 2017) ^ ((2017 - 1) / 2) = 2016 := by
      reduce_mod_char
    rw [hpow]
    decide +kernel
  have hneq_3 : (5 : ZMod 2017) ^ ((2017 - 1) / 3) ≠ 1 := by
    have hpow : (5 : ZMod 2017) ^ ((2017 - 1) / 3) = 294 := by
      reduce_mod_char
    rw [hpow]
    decide +kernel
  have hneq_7 : (5 : ZMod 2017) ^ ((2017 - 1) / 7) ≠ 1 := by
    have hpow : (5 : ZMod 2017) ^ ((2017 - 1) / 7) = 1879 := by
      reduce_mod_char
    rw [hpow]
    decide +kernel
  refine prime_of_lucas_list 2017 5 [2, 2, 2, 2, 2, 3, 3, 7] ?_ ?_ ?_ ?_
  · norm_num [List.prod_cons, List.prod_nil]
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Paper7Moduli.prime_2
    · exact Paper7Moduli.prime_2
    · exact Paper7Moduli.prime_2
    · exact Paper7Moduli.prime_2
    · exact Paper7Moduli.prime_2
    · exact Paper7Moduli.prime_3
    · exact Paper7Moduli.prime_3
    · exact Paper7Moduli.prime_7
  · reduce_mod_char
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hneq_2
    · exact hneq_2
    · exact hneq_2
    · exact hneq_2
    · exact hneq_2
    · exact hneq_3
    · exact hneq_3
    · exact hneq_7

#print axioms Paper7CRTPrimes.prime_2017

theorem prime_8069 : Nat.Prime 8069 := by
  have hneq_2 : (2 : ZMod 8069) ^ ((8069 - 1) / 2) ≠ 1 := by
    have hpow : (2 : ZMod 8069) ^ ((8069 - 1) / 2) = 8068 := by
      reduce_mod_char
    rw [hpow]
    decide +kernel
  have hneq_2017 : (2 : ZMod 8069) ^ ((8069 - 1) / 2017) ≠ 1 := by
    have hpow : (2 : ZMod 8069) ^ ((8069 - 1) / 2017) = 16 := by
      reduce_mod_char
    rw [hpow]
    decide +kernel
  refine prime_of_lucas_list 8069 2 [2, 2, 2017] ?_ ?_ ?_ ?_
  · norm_num [List.prod_cons, List.prod_nil]
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact Paper7Moduli.prime_2
    · exact Paper7Moduli.prime_2
    · exact Paper7CRTPrimes.prime_2017
  · reduce_mod_char
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact hneq_2
    · exact hneq_2
    · exact hneq_2017

#print axioms Paper7CRTPrimes.prime_8069

theorem prime_73 : Nat.Prime 73 := by
  have hneq_2 : (5 : ZMod 73) ^ ((73 - 1) / 2) ≠ 1 := by
    have hpow : (5 : ZMod 73) ^ ((73 - 1) / 2) = 72 := by
      reduce_mod_char
    rw [hpow]
    decide +kernel
  have hneq_3 : (5 : ZMod 73) ^ ((73 - 1) / 3) ≠ 1 := by
    have hpow : (5 : ZMod 73) ^ ((73 - 1) / 3) = 8 := by
      reduce_mod_char
    rw [hpow]
    decide +kernel
  refine prime_of_lucas_list 73 5 [2, 2, 2, 3, 3] ?_ ?_ ?_ ?_
  · norm_num [List.prod_cons, List.prod_nil]
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact Paper7Moduli.prime_2
    · exact Paper7Moduli.prime_2
    · exact Paper7Moduli.prime_2
    · exact Paper7Moduli.prime_3
    · exact Paper7Moduli.prime_3
  · reduce_mod_char
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact hneq_2
    · exact hneq_2
    · exact hneq_2
    · exact hneq_3
    · exact hneq_3

#print axioms Paper7CRTPrimes.prime_73

theorem prime_262657 : Nat.Prime 262657 := by
  have hneq_2 : (5 : ZMod 262657) ^ ((262657 - 1) / 2) ≠ 1 := by
    have hpow : (5 : ZMod 262657) ^ ((262657 - 1) / 2) = 262656 := by
      reduce_mod_char
    rw [hpow]
    decide +kernel
  have hneq_3 : (5 : ZMod 262657) ^ ((262657 - 1) / 3) ≠ 1 := by
    have hpow : (5 : ZMod 262657) ^ ((262657 - 1) / 3) = 262144 := by
      reduce_mod_char
    rw [hpow]
    decide +kernel
  have hneq_19 : (5 : ZMod 262657) ^ ((262657 - 1) / 19) ≠ 1 := by
    have hpow : (5 : ZMod 262657) ^ ((262657 - 1) / 19) = 241048 := by
      reduce_mod_char
    rw [hpow]
    decide +kernel
  refine prime_of_lucas_list 262657 5 [2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 19] ?_ ?_ ?_ ?_
  · norm_num [List.prod_cons, List.prod_nil]
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Paper7Moduli.prime_2
    · exact Paper7Moduli.prime_2
    · exact Paper7Moduli.prime_2
    · exact Paper7Moduli.prime_2
    · exact Paper7Moduli.prime_2
    · exact Paper7Moduli.prime_2
    · exact Paper7Moduli.prime_2
    · exact Paper7Moduli.prime_2
    · exact Paper7Moduli.prime_2
    · exact Paper7Moduli.prime_3
    · exact Paper7Moduli.prime_3
    · exact Paper7Moduli.prime_3
    · exact Paper7Moduli.prime_19
  · reduce_mod_char
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hneq_2
    · exact hneq_2
    · exact hneq_2
    · exact hneq_2
    · exact hneq_2
    · exact hneq_2
    · exact hneq_2
    · exact hneq_2
    · exact hneq_2
    · exact hneq_3
    · exact hneq_3
    · exact hneq_3
    · exact hneq_19

#print axioms Paper7CRTPrimes.prime_262657

theorem prime_536870909 : Nat.Prime 536870909 := by
  have hneq_2 : (2 : ZMod 536870909) ^ ((536870909 - 1) / 2) ≠ 1 := by
    have hpow : (2 : ZMod 536870909) ^ ((536870909 - 1) / 2) = 536870908 := by
      reduce_mod_char
    rw [hpow]
    decide +kernel
  have hneq_7 : (2 : ZMod 536870909) ^ ((536870909 - 1) / 7) ≠ 1 := by
    have hpow : (2 : ZMod 536870909) ^ ((536870909 - 1) / 7) = 439173207 := by
      reduce_mod_char
    rw [hpow]
    decide +kernel
  have hneq_73 : (2 : ZMod 536870909) ^ ((536870909 - 1) / 73) ≠ 1 := by
    have hpow : (2 : ZMod 536870909) ^ ((536870909 - 1) / 73) = 199199495 := by
      reduce_mod_char
    rw [hpow]
    decide +kernel
  have hneq_262657 : (2 : ZMod 536870909) ^ ((536870909 - 1) / 262657) ≠ 1 := by
    have hpow : (2 : ZMod 536870909) ^ ((536870909 - 1) / 262657) = 62781759 := by
      reduce_mod_char
    rw [hpow]
    decide +kernel
  refine prime_of_lucas_list 536870909 2 [2, 2, 7, 73, 262657] ?_ ?_ ?_ ?_
  · norm_num [List.prod_cons, List.prod_nil]
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact Paper7Moduli.prime_2
    · exact Paper7Moduli.prime_2
    · exact Paper7Moduli.prime_7
    · exact Paper7CRTPrimes.prime_73
    · exact Paper7CRTPrimes.prime_262657
  · reduce_mod_char
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact hneq_2
    · exact hneq_2
    · exact hneq_7
    · exact hneq_73
    · exact hneq_262657

#print axioms Paper7CRTPrimes.prime_536870909

end Paper7CRTPrimes
