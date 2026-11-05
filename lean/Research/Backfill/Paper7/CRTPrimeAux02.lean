import Research.Backfill.Paper7.CRTPrimeAux01

/-! Recursive Lucas certificate candidates. Every candidate factor product,
recursive prime reference and binary modular-power equality is checked by Lean.
The JSON numerals are untrusted input, not proof hypotheses. -/
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 800000

namespace Paper7CRTPrimes
open Paper7Moduli

theorem prime_49517298223 : Nat.Prime 49517298223 := by
  have hneq_2 : (3 : ZMod 49517298223) ^ ((49517298223 - 1) / 2) ≠ 1 := by
    have hpow : (3 : ZMod 49517298223) ^ ((49517298223 - 1) / 2) = 49517298222 := by
      reduce_mod_char
    rw [hpow]
    decide +kernel
  have hneq_3 : (3 : ZMod 49517298223) ^ ((49517298223 - 1) / 3) ≠ 1 := by
    have hpow : (3 : ZMod 49517298223) ^ ((49517298223 - 1) / 3) = 29695158040 := by
      reduce_mod_char
    rw [hpow]
    decide +kernel
  have hneq_7 : (3 : ZMod 49517298223) ^ ((49517298223 - 1) / 7) ≠ 1 := by
    have hpow : (3 : ZMod 49517298223) ^ ((49517298223 - 1) / 7) = 28777256229 := by
      reduce_mod_char
    rw [hpow]
    decide +kernel
  have hneq_127 : (3 : ZMod 49517298223) ^ ((49517298223 - 1) / 127) ≠ 1 := by
    have hpow : (3 : ZMod 49517298223) ^ ((49517298223 - 1) / 127) = 40434328215 := by
      reduce_mod_char
    rw [hpow]
    decide +kernel
  have hneq_659 : (3 : ZMod 49517298223) ^ ((49517298223 - 1) / 659) ≠ 1 := by
    have hpow : (3 : ZMod 49517298223) ^ ((49517298223 - 1) / 659) = 33106282977 := by
      reduce_mod_char
    rw [hpow]
    decide +kernel
  have hneq_14087 : (3 : ZMod 49517298223) ^ ((49517298223 - 1) / 14087) ≠ 1 := by
    have hpow : (3 : ZMod 49517298223) ^ ((49517298223 - 1) / 14087) = 49146507304 := by
      reduce_mod_char
    rw [hpow]
    decide +kernel
  refine prime_of_lucas_list 49517298223 3 [2, 3, 7, 127, 659, 14087] ?_ ?_ ?_ ?_
  · norm_num [List.prod_cons, List.prod_nil]
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact Paper7Moduli.prime_2
    · exact Paper7Moduli.prime_3
    · exact Paper7Moduli.prime_7
    · exact Paper7CRTPrimes.prime_127
    · exact Paper7CRTPrimes.prime_659
    · exact Paper7CRTPrimes.prime_14087
  · reduce_mod_char
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hneq_2
    · exact hneq_3
    · exact hneq_7
    · exact hneq_127
    · exact hneq_659
    · exact hneq_14087

#print axioms Paper7CRTPrimes.prime_49517298223

theorem prime_198762435067123 : Nat.Prime 198762435067123 := by
  have hneq_2 : (2 : ZMod 198762435067123) ^ ((198762435067123 - 1) / 2) ≠ 1 := by
    have hpow : (2 : ZMod 198762435067123) ^ ((198762435067123 - 1) / 2) = 198762435067122 := by
      reduce_mod_char
    rw [hpow]
    decide +kernel
  have hneq_3 : (2 : ZMod 198762435067123) ^ ((198762435067123 - 1) / 3) ≠ 1 := by
    have hpow : (2 : ZMod 198762435067123) ^ ((198762435067123 - 1) / 3) = 96387337323880 := by
      reduce_mod_char
    rw [hpow]
    decide +kernel
  have hneq_223 : (2 : ZMod 198762435067123) ^ ((198762435067123 - 1) / 223) ≠ 1 := by
    have hpow : (2 : ZMod 198762435067123) ^ ((198762435067123 - 1) / 223) = 149776214879759 := by
      reduce_mod_char
    rw [hpow]
    decide +kernel
  have hneq_49517298223 : (2 : ZMod 198762435067123) ^ ((198762435067123 - 1) / 49517298223) ≠ 1 := by
    have hpow : (2 : ZMod 198762435067123) ^ ((198762435067123 - 1) / 49517298223) = 160801450512059 := by
      reduce_mod_char
    rw [hpow]
    decide +kernel
  refine prime_of_lucas_list 198762435067123 2 [2, 3, 3, 223, 49517298223] ?_ ?_ ?_ ?_
  · norm_num [List.prod_cons, List.prod_nil]
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact Paper7Moduli.prime_2
    · exact Paper7Moduli.prime_3
    · exact Paper7Moduli.prime_3
    · exact Paper7CRTPrimes.prime_223
    · exact Paper7CRTPrimes.prime_49517298223
  · reduce_mod_char
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact hneq_2
    · exact hneq_3
    · exact hneq_3
    · exact hneq_223
    · exact hneq_49517298223

#print axioms Paper7CRTPrimes.prime_198762435067123

theorem prime_67 : Nat.Prime 67 := by
  have hneq_2 : (2 : ZMod 67) ^ ((67 - 1) / 2) ≠ 1 := by
    have hpow : (2 : ZMod 67) ^ ((67 - 1) / 2) = 66 := by
      reduce_mod_char
    rw [hpow]
    decide +kernel
  have hneq_3 : (2 : ZMod 67) ^ ((67 - 1) / 3) ≠ 1 := by
    have hpow : (2 : ZMod 67) ^ ((67 - 1) / 3) = 37 := by
      reduce_mod_char
    rw [hpow]
    decide +kernel
  have hneq_11 : (2 : ZMod 67) ^ ((67 - 1) / 11) ≠ 1 := by
    have hpow : (2 : ZMod 67) ^ ((67 - 1) / 11) = 64 := by
      reduce_mod_char
    rw [hpow]
    decide +kernel
  refine prime_of_lucas_list 67 2 [2, 3, 11] ?_ ?_ ?_ ?_
  · norm_num [List.prod_cons, List.prod_nil]
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact Paper7Moduli.prime_2
    · exact Paper7Moduli.prime_3
    · exact Paper7Moduli.prime_11
  · reduce_mod_char
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact hneq_2
    · exact hneq_3
    · exact hneq_11

#print axioms Paper7CRTPrimes.prime_67

theorem prime_97 : Nat.Prime 97 := by
  have hneq_2 : (5 : ZMod 97) ^ ((97 - 1) / 2) ≠ 1 := by
    have hpow : (5 : ZMod 97) ^ ((97 - 1) / 2) = 96 := by
      reduce_mod_char
    rw [hpow]
    decide +kernel
  have hneq_3 : (5 : ZMod 97) ^ ((97 - 1) / 3) ≠ 1 := by
    have hpow : (5 : ZMod 97) ^ ((97 - 1) / 3) = 35 := by
      reduce_mod_char
    rw [hpow]
    decide +kernel
  refine prime_of_lucas_list 97 5 [2, 2, 2, 2, 2, 3] ?_ ?_ ?_ ?_
  · norm_num [List.prod_cons, List.prod_nil]
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact Paper7Moduli.prime_2
    · exact Paper7Moduli.prime_2
    · exact Paper7Moduli.prime_2
    · exact Paper7Moduli.prime_2
    · exact Paper7Moduli.prime_2
    · exact Paper7Moduli.prime_3
  · reduce_mod_char
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hneq_2
    · exact hneq_2
    · exact hneq_2
    · exact hneq_2
    · exact hneq_2
    · exact hneq_3

#print axioms Paper7CRTPrimes.prime_97

theorem prime_89 : Nat.Prime 89 := by
  have hneq_2 : (3 : ZMod 89) ^ ((89 - 1) / 2) ≠ 1 := by
    have hpow : (3 : ZMod 89) ^ ((89 - 1) / 2) = 88 := by
      reduce_mod_char
    rw [hpow]
    decide +kernel
  have hneq_11 : (3 : ZMod 89) ^ ((89 - 1) / 11) ≠ 1 := by
    have hpow : (3 : ZMod 89) ^ ((89 - 1) / 11) = 64 := by
      reduce_mod_char
    rw [hpow]
    decide +kernel
  refine prime_of_lucas_list 89 3 [2, 2, 2, 11] ?_ ?_ ?_ ?_
  · norm_num [List.prod_cons, List.prod_nil]
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact Paper7Moduli.prime_2
    · exact Paper7Moduli.prime_2
    · exact Paper7Moduli.prime_2
    · exact Paper7Moduli.prime_11
  · reduce_mod_char
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact hneq_2
    · exact hneq_2
    · exact hneq_2
    · exact hneq_11

#print axioms Paper7CRTPrimes.prime_89

theorem prime_4273 : Nat.Prime 4273 := by
  have hneq_2 : (5 : ZMod 4273) ^ ((4273 - 1) / 2) ≠ 1 := by
    have hpow : (5 : ZMod 4273) ^ ((4273 - 1) / 2) = 4272 := by
      reduce_mod_char
    rw [hpow]
    decide +kernel
  have hneq_3 : (5 : ZMod 4273) ^ ((4273 - 1) / 3) ≠ 1 := by
    have hpow : (5 : ZMod 4273) ^ ((4273 - 1) / 3) = 2662 := by
      reduce_mod_char
    rw [hpow]
    decide +kernel
  have hneq_89 : (5 : ZMod 4273) ^ ((4273 - 1) / 89) ≠ 1 := by
    have hpow : (5 : ZMod 4273) ^ ((4273 - 1) / 89) = 4065 := by
      reduce_mod_char
    rw [hpow]
    decide +kernel
  refine prime_of_lucas_list 4273 5 [2, 2, 2, 2, 3, 89] ?_ ?_ ?_ ?_
  · norm_num [List.prod_cons, List.prod_nil]
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact Paper7Moduli.prime_2
    · exact Paper7Moduli.prime_2
    · exact Paper7Moduli.prime_2
    · exact Paper7Moduli.prime_2
    · exact Paper7Moduli.prime_3
    · exact Paper7CRTPrimes.prime_89
  · reduce_mod_char
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hneq_2
    · exact hneq_2
    · exact hneq_2
    · exact hneq_2
    · exact hneq_3
    · exact hneq_89

#print axioms Paper7CRTPrimes.prime_4273

theorem prime_4759 : Nat.Prime 4759 := by
  have hneq_2 : (3 : ZMod 4759) ^ ((4759 - 1) / 2) ≠ 1 := by
    have hpow : (3 : ZMod 4759) ^ ((4759 - 1) / 2) = 4758 := by
      reduce_mod_char
    rw [hpow]
    decide +kernel
  have hneq_3 : (3 : ZMod 4759) ^ ((4759 - 1) / 3) ≠ 1 := by
    have hpow : (3 : ZMod 4759) ^ ((4759 - 1) / 3) = 3233 := by
      reduce_mod_char
    rw [hpow]
    decide +kernel
  have hneq_13 : (3 : ZMod 4759) ^ ((4759 - 1) / 13) ≠ 1 := by
    have hpow : (3 : ZMod 4759) ^ ((4759 - 1) / 13) = 2763 := by
      reduce_mod_char
    rw [hpow]
    decide +kernel
  have hneq_61 : (3 : ZMod 4759) ^ ((4759 - 1) / 61) ≠ 1 := by
    have hpow : (3 : ZMod 4759) ^ ((4759 - 1) / 61) = 49 := by
      reduce_mod_char
    rw [hpow]
    decide +kernel
  refine prime_of_lucas_list 4759 3 [2, 3, 13, 61] ?_ ?_ ?_ ?_
  · norm_num [List.prod_cons, List.prod_nil]
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact Paper7Moduli.prime_2
    · exact Paper7Moduli.prime_3
    · exact Paper7Moduli.prime_13
    · exact Paper7Moduli.prime_61
  · reduce_mod_char
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact hneq_2
    · exact hneq_3
    · exact hneq_13
    · exact hneq_61

#print axioms Paper7CRTPrimes.prime_4759

theorem prime_911 : Nat.Prime 911 := by
  have hneq_2 : (17 : ZMod 911) ^ ((911 - 1) / 2) ≠ 1 := by
    have hpow : (17 : ZMod 911) ^ ((911 - 1) / 2) = 910 := by
      reduce_mod_char
    rw [hpow]
    decide +kernel
  have hneq_5 : (17 : ZMod 911) ^ ((911 - 1) / 5) ≠ 1 := by
    have hpow : (17 : ZMod 911) ^ ((911 - 1) / 5) = 19 := by
      reduce_mod_char
    rw [hpow]
    decide +kernel
  have hneq_7 : (17 : ZMod 911) ^ ((911 - 1) / 7) ≠ 1 := by
    have hpow : (17 : ZMod 911) ^ ((911 - 1) / 7) = 49 := by
      reduce_mod_char
    rw [hpow]
    decide +kernel
  have hneq_13 : (17 : ZMod 911) ^ ((911 - 1) / 13) ≠ 1 := by
    have hpow : (17 : ZMod 911) ^ ((911 - 1) / 13) = 900 := by
      reduce_mod_char
    rw [hpow]
    decide +kernel
  refine prime_of_lucas_list 911 17 [2, 5, 7, 13] ?_ ?_ ?_ ?_
  · norm_num [List.prod_cons, List.prod_nil]
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact Paper7Moduli.prime_2
    · exact Paper7Moduli.prime_5
    · exact Paper7Moduli.prime_7
    · exact Paper7Moduli.prime_13
  · reduce_mod_char
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact hneq_2
    · exact hneq_5
    · exact hneq_7
    · exact hneq_13

#print axioms Paper7CRTPrimes.prime_911

theorem prime_207709 : Nat.Prime 207709 := by
  have hneq_2 : (2 : ZMod 207709) ^ ((207709 - 1) / 2) ≠ 1 := by
    have hpow : (2 : ZMod 207709) ^ ((207709 - 1) / 2) = 207708 := by
      reduce_mod_char
    rw [hpow]
    decide +kernel
  have hneq_3 : (2 : ZMod 207709) ^ ((207709 - 1) / 3) ≠ 1 := by
    have hpow : (2 : ZMod 207709) ^ ((207709 - 1) / 3) = 149239 := by
      reduce_mod_char
    rw [hpow]
    decide +kernel
  have hneq_19 : (2 : ZMod 207709) ^ ((207709 - 1) / 19) ≠ 1 := by
    have hpow : (2 : ZMod 207709) ^ ((207709 - 1) / 19) = 142908 := by
      reduce_mod_char
    rw [hpow]
    decide +kernel
  have hneq_911 : (2 : ZMod 207709) ^ ((207709 - 1) / 911) ≠ 1 := by
    have hpow : (2 : ZMod 207709) ^ ((207709 - 1) / 911) = 21964 := by
      reduce_mod_char
    rw [hpow]
    decide +kernel
  refine prime_of_lucas_list 207709 2 [2, 2, 3, 19, 911] ?_ ?_ ?_ ?_
  · norm_num [List.prod_cons, List.prod_nil]
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact Paper7Moduli.prime_2
    · exact Paper7Moduli.prime_2
    · exact Paper7Moduli.prime_3
    · exact Paper7Moduli.prime_19
    · exact Paper7CRTPrimes.prime_911
  · reduce_mod_char
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact hneq_2
    · exact hneq_2
    · exact hneq_3
    · exact hneq_19
    · exact hneq_911

#print axioms Paper7CRTPrimes.prime_207709

theorem prime_4488751 : Nat.Prime 4488751 := by
  have hneq_2 : (3 : ZMod 4488751) ^ ((4488751 - 1) / 2) ≠ 1 := by
    have hpow : (3 : ZMod 4488751) ^ ((4488751 - 1) / 2) = 4488750 := by
      reduce_mod_char
    rw [hpow]
    decide +kernel
  have hneq_3 : (3 : ZMod 4488751) ^ ((4488751 - 1) / 3) ≠ 1 := by
    have hpow : (3 : ZMod 4488751) ^ ((4488751 - 1) / 3) = 4044522 := by
      reduce_mod_char
    rw [hpow]
    decide +kernel
  have hneq_5 : (3 : ZMod 4488751) ^ ((4488751 - 1) / 5) ≠ 1 := by
    have hpow : (3 : ZMod 4488751) ^ ((4488751 - 1) / 5) = 3275742 := by
      reduce_mod_char
    rw [hpow]
    decide +kernel
  have hneq_7 : (3 : ZMod 4488751) ^ ((4488751 - 1) / 7) ≠ 1 := by
    have hpow : (3 : ZMod 4488751) ^ ((4488751 - 1) / 7) = 2994563 := by
      reduce_mod_char
    rw [hpow]
    decide +kernel
  have hneq_19 : (3 : ZMod 4488751) ^ ((4488751 - 1) / 19) ≠ 1 := by
    have hpow : (3 : ZMod 4488751) ^ ((4488751 - 1) / 19) = 1782532 := by
      reduce_mod_char
    rw [hpow]
    decide +kernel
  refine prime_of_lucas_list 4488751 3 [2, 3, 3, 3, 5, 5, 5, 5, 7, 19] ?_ ?_ ?_ ?_
  · norm_num [List.prod_cons, List.prod_nil]
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Paper7Moduli.prime_2
    · exact Paper7Moduli.prime_3
    · exact Paper7Moduli.prime_3
    · exact Paper7Moduli.prime_3
    · exact Paper7Moduli.prime_5
    · exact Paper7Moduli.prime_5
    · exact Paper7Moduli.prime_5
    · exact Paper7Moduli.prime_5
    · exact Paper7Moduli.prime_7
    · exact Paper7Moduli.prime_19
  · reduce_mod_char
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hneq_2
    · exact hneq_3
    · exact hneq_3
    · exact hneq_3
    · exact hneq_5
    · exact hneq_5
    · exact hneq_5
    · exact hneq_5
    · exact hneq_7
    · exact hneq_19

#print axioms Paper7CRTPrimes.prime_4488751

end Paper7CRTPrimes
