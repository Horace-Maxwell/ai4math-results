import Research.Backfill.Paper7.ModuliCertificateTools

/-! Recursive Lucas certificates; all supplied finite data are checked by Lean.
The source JSON is a source of candidate numerals, never a hypothesis. -/

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 800000

namespace Paper7Moduli

theorem prime_2 : Nat.Prime 2 := by
  exact Nat.prime_two

#print axioms Paper7Moduli.prime_2

theorem prime_3 : Nat.Prime 3 := by
  have hneq_2 : (2 : ZMod 3) ^ ((3 - 1) / 2) ≠ 1 := by
    have hpow : (2 : ZMod 3) ^ ((3 - 1) / 2) = 2 := by
      reduce_mod_char
    rw [hpow]
    decide +kernel
  refine prime_of_lucas_list 3 2 [2] ?_ ?_ ?_ ?_
  · norm_num [List.prod_cons, List.prod_nil]
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl
    · exact prime_2
  · reduce_mod_char
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl
    · exact hneq_2

#print axioms Paper7Moduli.prime_3

theorem prime_5 : Nat.Prime 5 := by
  have hneq_2 : (2 : ZMod 5) ^ ((5 - 1) / 2) ≠ 1 := by
    have hpow : (2 : ZMod 5) ^ ((5 - 1) / 2) = 4 := by
      reduce_mod_char
    rw [hpow]
    decide +kernel
  refine prime_of_lucas_list 5 2 [2, 2] ?_ ?_ ?_ ?_
  · norm_num [List.prod_cons, List.prod_nil]
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_2
  · reduce_mod_char
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact hneq_2
    · exact hneq_2

#print axioms Paper7Moduli.prime_5

theorem prime_7 : Nat.Prime 7 := by
  have hneq_2 : (3 : ZMod 7) ^ ((7 - 1) / 2) ≠ 1 := by
    have hpow : (3 : ZMod 7) ^ ((7 - 1) / 2) = 6 := by
      reduce_mod_char
    rw [hpow]
    decide +kernel
  have hneq_3 : (3 : ZMod 7) ^ ((7 - 1) / 3) ≠ 1 := by
    have hpow : (3 : ZMod 7) ^ ((7 - 1) / 3) = 2 := by
      reduce_mod_char
    rw [hpow]
    decide +kernel
  refine prime_of_lucas_list 7 3 [2, 3] ?_ ?_ ?_ ?_
  · norm_num [List.prod_cons, List.prod_nil]
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_3
  · reduce_mod_char
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact hneq_2
    · exact hneq_3

#print axioms Paper7Moduli.prime_7

theorem prime_11 : Nat.Prime 11 := by
  have hneq_2 : (2 : ZMod 11) ^ ((11 - 1) / 2) ≠ 1 := by
    have hpow : (2 : ZMod 11) ^ ((11 - 1) / 2) = 10 := by
      reduce_mod_char
    rw [hpow]
    decide +kernel
  have hneq_5 : (2 : ZMod 11) ^ ((11 - 1) / 5) ≠ 1 := by
    have hpow : (2 : ZMod 11) ^ ((11 - 1) / 5) = 4 := by
      reduce_mod_char
    rw [hpow]
    decide +kernel
  refine prime_of_lucas_list 11 2 [2, 5] ?_ ?_ ?_ ?_
  · norm_num [List.prod_cons, List.prod_nil]
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_5
  · reduce_mod_char
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact hneq_2
    · exact hneq_5

#print axioms Paper7Moduli.prime_11

theorem prime_13 : Nat.Prime 13 := by
  have hneq_2 : (2 : ZMod 13) ^ ((13 - 1) / 2) ≠ 1 := by
    have hpow : (2 : ZMod 13) ^ ((13 - 1) / 2) = 12 := by
      reduce_mod_char
    rw [hpow]
    decide +kernel
  have hneq_3 : (2 : ZMod 13) ^ ((13 - 1) / 3) ≠ 1 := by
    have hpow : (2 : ZMod 13) ^ ((13 - 1) / 3) = 3 := by
      reduce_mod_char
    rw [hpow]
    decide +kernel
  refine prime_of_lucas_list 13 2 [2, 2, 3] ?_ ?_ ?_ ?_
  · norm_num [List.prod_cons, List.prod_nil]
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_3
  · reduce_mod_char
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact hneq_2
    · exact hneq_2
    · exact hneq_3

#print axioms Paper7Moduli.prime_13

theorem prime_17 : Nat.Prime 17 := by
  have hneq_2 : (3 : ZMod 17) ^ ((17 - 1) / 2) ≠ 1 := by
    have hpow : (3 : ZMod 17) ^ ((17 - 1) / 2) = 16 := by
      reduce_mod_char
    rw [hpow]
    decide +kernel
  refine prime_of_lucas_list 17 3 [2, 2, 2, 2] ?_ ?_ ?_ ?_
  · norm_num [List.prod_cons, List.prod_nil]
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_2
  · reduce_mod_char
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact hneq_2
    · exact hneq_2
    · exact hneq_2
    · exact hneq_2

#print axioms Paper7Moduli.prime_17

theorem prime_19 : Nat.Prime 19 := by
  have hneq_2 : (2 : ZMod 19) ^ ((19 - 1) / 2) ≠ 1 := by
    have hpow : (2 : ZMod 19) ^ ((19 - 1) / 2) = 18 := by
      reduce_mod_char
    rw [hpow]
    decide +kernel
  have hneq_3 : (2 : ZMod 19) ^ ((19 - 1) / 3) ≠ 1 := by
    have hpow : (2 : ZMod 19) ^ ((19 - 1) / 3) = 7 := by
      reduce_mod_char
    rw [hpow]
    decide +kernel
  refine prime_of_lucas_list 19 2 [2, 3, 3] ?_ ?_ ?_ ?_
  · norm_num [List.prod_cons, List.prod_nil]
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_3
  · reduce_mod_char
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact hneq_2
    · exact hneq_3
    · exact hneq_3

#print axioms Paper7Moduli.prime_19

theorem prime_23 : Nat.Prime 23 := by
  have hneq_2 : (5 : ZMod 23) ^ ((23 - 1) / 2) ≠ 1 := by
    have hpow : (5 : ZMod 23) ^ ((23 - 1) / 2) = 22 := by
      reduce_mod_char
    rw [hpow]
    decide +kernel
  have hneq_11 : (5 : ZMod 23) ^ ((23 - 1) / 11) ≠ 1 := by
    have hpow : (5 : ZMod 23) ^ ((23 - 1) / 11) = 2 := by
      reduce_mod_char
    rw [hpow]
    decide +kernel
  refine prime_of_lucas_list 23 5 [2, 11] ?_ ?_ ?_ ?_
  · norm_num [List.prod_cons, List.prod_nil]
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_11
  · reduce_mod_char
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact hneq_2
    · exact hneq_11

#print axioms Paper7Moduli.prime_23

theorem prime_31 : Nat.Prime 31 := by
  have hneq_2 : (3 : ZMod 31) ^ ((31 - 1) / 2) ≠ 1 := by
    have hpow : (3 : ZMod 31) ^ ((31 - 1) / 2) = 30 := by
      reduce_mod_char
    rw [hpow]
    decide +kernel
  have hneq_3 : (3 : ZMod 31) ^ ((31 - 1) / 3) ≠ 1 := by
    have hpow : (3 : ZMod 31) ^ ((31 - 1) / 3) = 25 := by
      reduce_mod_char
    rw [hpow]
    decide +kernel
  have hneq_5 : (3 : ZMod 31) ^ ((31 - 1) / 5) ≠ 1 := by
    have hpow : (3 : ZMod 31) ^ ((31 - 1) / 5) = 16 := by
      reduce_mod_char
    rw [hpow]
    decide +kernel
  refine prime_of_lucas_list 31 3 [2, 3, 5] ?_ ?_ ?_ ?_
  · norm_num [List.prod_cons, List.prod_nil]
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
  · reduce_mod_char
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact hneq_2
    · exact hneq_3
    · exact hneq_5

#print axioms Paper7Moduli.prime_31

theorem prime_41 : Nat.Prime 41 := by
  have hneq_2 : (6 : ZMod 41) ^ ((41 - 1) / 2) ≠ 1 := by
    have hpow : (6 : ZMod 41) ^ ((41 - 1) / 2) = 40 := by
      reduce_mod_char
    rw [hpow]
    decide +kernel
  have hneq_5 : (6 : ZMod 41) ^ ((41 - 1) / 5) ≠ 1 := by
    have hpow : (6 : ZMod 41) ^ ((41 - 1) / 5) = 10 := by
      reduce_mod_char
    rw [hpow]
    decide +kernel
  refine prime_of_lucas_list 41 6 [2, 2, 2, 5] ?_ ?_ ?_ ?_
  · norm_num [List.prod_cons, List.prod_nil]
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_5
  · reduce_mod_char
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact hneq_2
    · exact hneq_2
    · exact hneq_2
    · exact hneq_5

#print axioms Paper7Moduli.prime_41

theorem prime_53 : Nat.Prime 53 := by
  have hneq_2 : (2 : ZMod 53) ^ ((53 - 1) / 2) ≠ 1 := by
    have hpow : (2 : ZMod 53) ^ ((53 - 1) / 2) = 52 := by
      reduce_mod_char
    rw [hpow]
    decide +kernel
  have hneq_13 : (2 : ZMod 53) ^ ((53 - 1) / 13) ≠ 1 := by
    have hpow : (2 : ZMod 53) ^ ((53 - 1) / 13) = 16 := by
      reduce_mod_char
    rw [hpow]
    decide +kernel
  refine prime_of_lucas_list 53 2 [2, 2, 13] ?_ ?_ ?_ ?_
  · norm_num [List.prod_cons, List.prod_nil]
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_13
  · reduce_mod_char
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact hneq_2
    · exact hneq_2
    · exact hneq_13

#print axioms Paper7Moduli.prime_53

theorem prime_61 : Nat.Prime 61 := by
  have hneq_2 : (2 : ZMod 61) ^ ((61 - 1) / 2) ≠ 1 := by
    have hpow : (2 : ZMod 61) ^ ((61 - 1) / 2) = 60 := by
      reduce_mod_char
    rw [hpow]
    decide +kernel
  have hneq_3 : (2 : ZMod 61) ^ ((61 - 1) / 3) ≠ 1 := by
    have hpow : (2 : ZMod 61) ^ ((61 - 1) / 3) = 47 := by
      reduce_mod_char
    rw [hpow]
    decide +kernel
  have hneq_5 : (2 : ZMod 61) ^ ((61 - 1) / 5) ≠ 1 := by
    have hpow : (2 : ZMod 61) ^ ((61 - 1) / 5) = 9 := by
      reduce_mod_char
    rw [hpow]
    decide +kernel
  refine prime_of_lucas_list 61 2 [2, 2, 3, 5] ?_ ?_ ?_ ?_
  · norm_num [List.prod_cons, List.prod_nil]
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_3
    · exact prime_5
  · reduce_mod_char
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact hneq_2
    · exact hneq_2
    · exact hneq_3
    · exact hneq_5

#print axioms Paper7Moduli.prime_61

theorem prime_131 : Nat.Prime 131 := by
  have hneq_2 : (2 : ZMod 131) ^ ((131 - 1) / 2) ≠ 1 := by
    have hpow : (2 : ZMod 131) ^ ((131 - 1) / 2) = 130 := by
      reduce_mod_char
    rw [hpow]
    decide +kernel
  have hneq_5 : (2 : ZMod 131) ^ ((131 - 1) / 5) ≠ 1 := by
    have hpow : (2 : ZMod 131) ^ ((131 - 1) / 5) = 53 := by
      reduce_mod_char
    rw [hpow]
    decide +kernel
  have hneq_13 : (2 : ZMod 131) ^ ((131 - 1) / 13) ≠ 1 := by
    have hpow : (2 : ZMod 131) ^ ((131 - 1) / 13) = 107 := by
      reduce_mod_char
    rw [hpow]
    decide +kernel
  refine prime_of_lucas_list 131 2 [2, 5, 13] ?_ ?_ ?_ ?_
  · norm_num [List.prod_cons, List.prod_nil]
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_13
  · reduce_mod_char
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact hneq_2
    · exact hneq_5
    · exact hneq_13

#print axioms Paper7Moduli.prime_131

theorem prime_151 : Nat.Prime 151 := by
  have hneq_2 : (6 : ZMod 151) ^ ((151 - 1) / 2) ≠ 1 := by
    have hpow : (6 : ZMod 151) ^ ((151 - 1) / 2) = 150 := by
      reduce_mod_char
    rw [hpow]
    decide +kernel
  have hneq_3 : (6 : ZMod 151) ^ ((151 - 1) / 3) ≠ 1 := by
    have hpow : (6 : ZMod 151) ^ ((151 - 1) / 3) = 32 := by
      reduce_mod_char
    rw [hpow]
    decide +kernel
  have hneq_5 : (6 : ZMod 151) ^ ((151 - 1) / 5) ≠ 1 := by
    have hpow : (6 : ZMod 151) ^ ((151 - 1) / 5) = 59 := by
      reduce_mod_char
    rw [hpow]
    decide +kernel
  refine prime_of_lucas_list 151 6 [2, 3, 5, 5] ?_ ?_ ?_ ?_
  · norm_num [List.prod_cons, List.prod_nil]
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_5
  · reduce_mod_char
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact hneq_2
    · exact hneq_3
    · exact hneq_5
    · exact hneq_5

#print axioms Paper7Moduli.prime_151

theorem prime_191 : Nat.Prime 191 := by
  have hneq_2 : (19 : ZMod 191) ^ ((191 - 1) / 2) ≠ 1 := by
    have hpow : (19 : ZMod 191) ^ ((191 - 1) / 2) = 190 := by
      reduce_mod_char
    rw [hpow]
    decide +kernel
  have hneq_5 : (19 : ZMod 191) ^ ((191 - 1) / 5) ≠ 1 := by
    have hpow : (19 : ZMod 191) ^ ((191 - 1) / 5) = 39 := by
      reduce_mod_char
    rw [hpow]
    decide +kernel
  have hneq_19 : (19 : ZMod 191) ^ ((191 - 1) / 19) ≠ 1 := by
    have hpow : (19 : ZMod 191) ^ ((191 - 1) / 19) = 52 := by
      reduce_mod_char
    rw [hpow]
    decide +kernel
  refine prime_of_lucas_list 191 19 [2, 5, 19] ?_ ?_ ?_ ?_
  · norm_num [List.prod_cons, List.prod_nil]
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_5
    · exact prime_19
  · reduce_mod_char
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact hneq_2
    · exact hneq_5
    · exact hneq_19

#print axioms Paper7Moduli.prime_191

theorem prime_331 : Nat.Prime 331 := by
  have hneq_2 : (3 : ZMod 331) ^ ((331 - 1) / 2) ≠ 1 := by
    have hpow : (3 : ZMod 331) ^ ((331 - 1) / 2) = 330 := by
      reduce_mod_char
    rw [hpow]
    decide +kernel
  have hneq_3 : (3 : ZMod 331) ^ ((331 - 1) / 3) ≠ 1 := by
    have hpow : (3 : ZMod 331) ^ ((331 - 1) / 3) = 299 := by
      reduce_mod_char
    rw [hpow]
    decide +kernel
  have hneq_5 : (3 : ZMod 331) ^ ((331 - 1) / 5) ≠ 1 := by
    have hpow : (3 : ZMod 331) ^ ((331 - 1) / 5) = 64 := by
      reduce_mod_char
    rw [hpow]
    decide +kernel
  have hneq_11 : (3 : ZMod 331) ^ ((331 - 1) / 11) ≠ 1 := by
    have hpow : (3 : ZMod 331) ^ ((331 - 1) / 11) = 270 := by
      reduce_mod_char
    rw [hpow]
    decide +kernel
  refine prime_of_lucas_list 331 3 [2, 3, 5, 11] ?_ ?_ ?_ ?_
  · norm_num [List.prod_cons, List.prod_nil]
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
  · reduce_mod_char
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact hneq_2
    · exact hneq_3
    · exact hneq_5
    · exact hneq_11

#print axioms Paper7Moduli.prime_331

theorem prime_1321 : Nat.Prime 1321 := by
  have hneq_2 : (13 : ZMod 1321) ^ ((1321 - 1) / 2) ≠ 1 := by
    have hpow : (13 : ZMod 1321) ^ ((1321 - 1) / 2) = 1320 := by
      reduce_mod_char
    rw [hpow]
    decide +kernel
  have hneq_3 : (13 : ZMod 1321) ^ ((1321 - 1) / 3) ≠ 1 := by
    have hpow : (13 : ZMod 1321) ^ ((1321 - 1) / 3) = 297 := by
      reduce_mod_char
    rw [hpow]
    decide +kernel
  have hneq_5 : (13 : ZMod 1321) ^ ((1321 - 1) / 5) ≠ 1 := by
    have hpow : (13 : ZMod 1321) ^ ((1321 - 1) / 5) = 133 := by
      reduce_mod_char
    rw [hpow]
    decide +kernel
  have hneq_11 : (13 : ZMod 1321) ^ ((1321 - 1) / 11) ≠ 1 := by
    have hpow : (13 : ZMod 1321) ^ ((1321 - 1) / 11) = 925 := by
      reduce_mod_char
    rw [hpow]
    decide +kernel
  refine prime_of_lucas_list 1321 13 [2, 2, 2, 3, 5, 11] ?_ ?_ ?_ ?_
  · norm_num [List.prod_cons, List.prod_nil]
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_11
  · reduce_mod_char
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hneq_2
    · exact hneq_2
    · exact hneq_2
    · exact hneq_3
    · exact hneq_5
    · exact hneq_11

#print axioms Paper7Moduli.prime_1321

theorem prime_1427 : Nat.Prime 1427 := by
  have hneq_2 : (2 : ZMod 1427) ^ ((1427 - 1) / 2) ≠ 1 := by
    have hpow : (2 : ZMod 1427) ^ ((1427 - 1) / 2) = 1426 := by
      reduce_mod_char
    rw [hpow]
    decide +kernel
  have hneq_23 : (2 : ZMod 1427) ^ ((1427 - 1) / 23) ≠ 1 := by
    have hpow : (2 : ZMod 1427) ^ ((1427 - 1) / 23) = 965 := by
      reduce_mod_char
    rw [hpow]
    decide +kernel
  have hneq_31 : (2 : ZMod 1427) ^ ((1427 - 1) / 31) ≠ 1 := by
    have hpow : (2 : ZMod 1427) ^ ((1427 - 1) / 31) = 489 := by
      reduce_mod_char
    rw [hpow]
    decide +kernel
  refine prime_of_lucas_list 1427 2 [2, 23, 31] ?_ ?_ ?_ ?_
  · norm_num [List.prod_cons, List.prod_nil]
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_23
    · exact prime_31
  · reduce_mod_char
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact hneq_2
    · exact hneq_23
    · exact hneq_31

#print axioms Paper7Moduli.prime_1427

theorem prime_148721 : Nat.Prime 148721 := by
  have hneq_2 : (6 : ZMod 148721) ^ ((148721 - 1) / 2) ≠ 1 := by
    have hpow : (6 : ZMod 148721) ^ ((148721 - 1) / 2) = 148720 := by
      reduce_mod_char
    rw [hpow]
    decide +kernel
  have hneq_5 : (6 : ZMod 148721) ^ ((148721 - 1) / 5) ≠ 1 := by
    have hpow : (6 : ZMod 148721) ^ ((148721 - 1) / 5) = 75923 := by
      reduce_mod_char
    rw [hpow]
    decide +kernel
  have hneq_11 : (6 : ZMod 148721) ^ ((148721 - 1) / 11) ≠ 1 := by
    have hpow : (6 : ZMod 148721) ^ ((148721 - 1) / 11) = 74939 := by
      reduce_mod_char
    rw [hpow]
    decide +kernel
  have hneq_13 : (6 : ZMod 148721) ^ ((148721 - 1) / 13) ≠ 1 := by
    have hpow : (6 : ZMod 148721) ^ ((148721 - 1) / 13) = 18050 := by
      reduce_mod_char
    rw [hpow]
    decide +kernel
  refine prime_of_lucas_list 148721 6 [2, 2, 2, 2, 5, 11, 13, 13] ?_ ?_ ?_ ?_
  · norm_num [List.prod_cons, List.prod_nil]
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_5
    · exact prime_11
    · exact prime_13
    · exact prime_13
  · reduce_mod_char
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hneq_2
    · exact hneq_2
    · exact hneq_2
    · exact hneq_2
    · exact hneq_5
    · exact hneq_11
    · exact hneq_13
    · exact hneq_13

#print axioms Paper7Moduli.prime_148721

theorem prime_234931 : Nat.Prime 234931 := by
  have hneq_2 : (3 : ZMod 234931) ^ ((234931 - 1) / 2) ≠ 1 := by
    have hpow : (3 : ZMod 234931) ^ ((234931 - 1) / 2) = 234930 := by
      reduce_mod_char
    rw [hpow]
    decide +kernel
  have hneq_3 : (3 : ZMod 234931) ^ ((234931 - 1) / 3) ≠ 1 := by
    have hpow : (3 : ZMod 234931) ^ ((234931 - 1) / 3) = 148773 := by
      reduce_mod_char
    rw [hpow]
    decide +kernel
  have hneq_5 : (3 : ZMod 234931) ^ ((234931 - 1) / 5) ≠ 1 := by
    have hpow : (3 : ZMod 234931) ^ ((234931 - 1) / 5) = 12198 := by
      reduce_mod_char
    rw [hpow]
    decide +kernel
  have hneq_41 : (3 : ZMod 234931) ^ ((234931 - 1) / 41) ≠ 1 := by
    have hpow : (3 : ZMod 234931) ^ ((234931 - 1) / 41) = 86016 := by
      reduce_mod_char
    rw [hpow]
    decide +kernel
  have hneq_191 : (3 : ZMod 234931) ^ ((234931 - 1) / 191) ≠ 1 := by
    have hpow : (3 : ZMod 234931) ^ ((234931 - 1) / 191) = 55438 := by
      reduce_mod_char
    rw [hpow]
    decide +kernel
  refine prime_of_lucas_list 234931 3 [2, 3, 5, 41, 191] ?_ ?_ ?_ ?_
  · norm_num [List.prod_cons, List.prod_nil]
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_5
    · exact prime_41
    · exact prime_191
  · reduce_mod_char
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact hneq_2
    · exact hneq_3
    · exact hneq_5
    · exact hneq_41
    · exact hneq_191

#print axioms Paper7Moduli.prime_234931

theorem prime_500000003 : Nat.Prime 500000003 := by
  have hneq_2 : (2 : ZMod 500000003) ^ ((500000003 - 1) / 2) ≠ 1 := by
    have hpow : (2 : ZMod 500000003) ^ ((500000003 - 1) / 2) = 500000002 := by
      reduce_mod_char
    rw [hpow]
    decide +kernel
  have hneq_41 : (2 : ZMod 500000003) ^ ((500000003 - 1) / 41) ≠ 1 := by
    have hpow : (2 : ZMod 500000003) ^ ((500000003 - 1) / 41) = 278358512 := by
      reduce_mod_char
    rw [hpow]
    decide +kernel
  have hneq_148721 : (2 : ZMod 500000003) ^ ((500000003 - 1) / 148721) ≠ 1 := by
    have hpow : (2 : ZMod 500000003) ^ ((500000003 - 1) / 148721) = 233858057 := by
      reduce_mod_char
    rw [hpow]
    decide +kernel
  refine prime_of_lucas_list 500000003 2 [2, 41, 41, 148721] ?_ ?_ ?_ ?_
  · norm_num [List.prod_cons, List.prod_nil]
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_41
    · exact prime_41
    · exact prime_148721
  · reduce_mod_char
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact hneq_2
    · exact hneq_41
    · exact hneq_41
    · exact hneq_148721

#print axioms Paper7Moduli.prime_500000003

theorem prime_998244353 : Nat.Prime 998244353 := by
  have hneq_2 : (3 : ZMod 998244353) ^ ((998244353 - 1) / 2) ≠ 1 := by
    have hpow : (3 : ZMod 998244353) ^ ((998244353 - 1) / 2) = 998244352 := by
      reduce_mod_char
    rw [hpow]
    decide +kernel
  have hneq_7 : (3 : ZMod 998244353) ^ ((998244353 - 1) / 7) ≠ 1 := by
    have hpow : (3 : ZMod 998244353) ^ ((998244353 - 1) / 7) = 779057549 := by
      reduce_mod_char
    rw [hpow]
    decide +kernel
  have hneq_17 : (3 : ZMod 998244353) ^ ((998244353 - 1) / 17) ≠ 1 := by
    have hpow : (3 : ZMod 998244353) ^ ((998244353 - 1) / 17) = 337827833 := by
      reduce_mod_char
    rw [hpow]
    decide +kernel
  refine prime_of_lucas_list 998244353 3 [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 7, 17] ?_ ?_ ?_ ?_
  · norm_num [List.prod_cons, List.prod_nil]
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_2
    · exact prime_7
    · exact prime_17
  · reduce_mod_char
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hneq_2
    · exact hneq_2
    · exact hneq_2
    · exact hneq_2
    · exact hneq_2
    · exact hneq_2
    · exact hneq_2
    · exact hneq_2
    · exact hneq_2
    · exact hneq_2
    · exact hneq_2
    · exact hneq_2
    · exact hneq_2
    · exact hneq_2
    · exact hneq_2
    · exact hneq_2
    · exact hneq_2
    · exact hneq_2
    · exact hneq_2
    · exact hneq_2
    · exact hneq_2
    · exact hneq_2
    · exact hneq_2
    · exact hneq_7
    · exact hneq_17

#print axioms Paper7Moduli.prime_998244353

theorem prime_1000000007 : Nat.Prime 1000000007 := by
  have hneq_2 : (5 : ZMod 1000000007) ^ ((1000000007 - 1) / 2) ≠ 1 := by
    have hpow : (5 : ZMod 1000000007) ^ ((1000000007 - 1) / 2) = 1000000006 := by
      reduce_mod_char
    rw [hpow]
    decide +kernel
  have hneq_500000003 : (5 : ZMod 1000000007) ^ ((1000000007 - 1) / 500000003) ≠ 1 := by
    have hpow : (5 : ZMod 1000000007) ^ ((1000000007 - 1) / 500000003) = 25 := by
      reduce_mod_char
    rw [hpow]
    decide +kernel
  refine prime_of_lucas_list 1000000007 5 [2, 500000003] ?_ ?_ ?_ ?_
  · norm_num [List.prod_cons, List.prod_nil]
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact prime_2
    · exact prime_500000003
  · reduce_mod_char
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact hneq_2
    · exact hneq_500000003

#print axioms Paper7Moduli.prime_1000000007

theorem prime_2147483647 : Nat.Prime 2147483647 := by
  have hneq_2 : (7 : ZMod 2147483647) ^ ((2147483647 - 1) / 2) ≠ 1 := by
    have hpow : (7 : ZMod 2147483647) ^ ((2147483647 - 1) / 2) = 2147483646 := by
      reduce_mod_char
    rw [hpow]
    decide +kernel
  have hneq_3 : (7 : ZMod 2147483647) ^ ((2147483647 - 1) / 3) ≠ 1 := by
    have hpow : (7 : ZMod 2147483647) ^ ((2147483647 - 1) / 3) = 1513477735 := by
      reduce_mod_char
    rw [hpow]
    decide +kernel
  have hneq_7 : (7 : ZMod 2147483647) ^ ((2147483647 - 1) / 7) ≠ 1 := by
    have hpow : (7 : ZMod 2147483647) ^ ((2147483647 - 1) / 7) = 1205362885 := by
      reduce_mod_char
    rw [hpow]
    decide +kernel
  have hneq_11 : (7 : ZMod 2147483647) ^ ((2147483647 - 1) / 11) ≠ 1 := by
    have hpow : (7 : ZMod 2147483647) ^ ((2147483647 - 1) / 11) = 1969212174 := by
      reduce_mod_char
    rw [hpow]
    decide +kernel
  have hneq_31 : (7 : ZMod 2147483647) ^ ((2147483647 - 1) / 31) ≠ 1 := by
    have hpow : (7 : ZMod 2147483647) ^ ((2147483647 - 1) / 31) = 512 := by
      reduce_mod_char
    rw [hpow]
    decide +kernel
  have hneq_151 : (7 : ZMod 2147483647) ^ ((2147483647 - 1) / 151) ≠ 1 := by
    have hpow : (7 : ZMod 2147483647) ^ ((2147483647 - 1) / 151) = 535044134 := by
      reduce_mod_char
    rw [hpow]
    decide +kernel
  have hneq_331 : (7 : ZMod 2147483647) ^ ((2147483647 - 1) / 331) ≠ 1 := by
    have hpow : (7 : ZMod 2147483647) ^ ((2147483647 - 1) / 331) = 1761855083 := by
      reduce_mod_char
    rw [hpow]
    decide +kernel
  refine prime_of_lucas_list 2147483647 7 [2, 3, 3, 7, 11, 31, 151, 331] ?_ ?_ ?_ ?_
  · norm_num [List.prod_cons, List.prod_nil]
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_3
    · exact prime_7
    · exact prime_11
    · exact prime_31
    · exact prime_151
    · exact prime_331
  · reduce_mod_char
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hneq_2
    · exact hneq_3
    · exact hneq_3
    · exact hneq_7
    · exact hneq_11
    · exact hneq_31
    · exact hneq_151
    · exact hneq_331

#print axioms Paper7Moduli.prime_2147483647

theorem prime_8740842787 : Nat.Prime 8740842787 := by
  have hneq_2 : (2 : ZMod 8740842787) ^ ((8740842787 - 1) / 2) ≠ 1 := by
    have hpow : (2 : ZMod 8740842787) ^ ((8740842787 - 1) / 2) = 8740842786 := by
      reduce_mod_char
    rw [hpow]
    decide +kernel
  have hneq_3 : (2 : ZMod 8740842787) ^ ((8740842787 - 1) / 3) ≠ 1 := by
    have hpow : (2 : ZMod 8740842787) ^ ((8740842787 - 1) / 3) = 767969283 := by
      reduce_mod_char
    rw [hpow]
    decide +kernel
  have hneq_13 : (2 : ZMod 8740842787) ^ ((8740842787 - 1) / 13) ≠ 1 := by
    have hpow : (2 : ZMod 8740842787) ^ ((8740842787 - 1) / 13) = 5981893498 := by
      reduce_mod_char
    rw [hpow]
    decide +kernel
  have hneq_53 : (2 : ZMod 8740842787) ^ ((8740842787 - 1) / 53) ≠ 1 := by
    have hpow : (2 : ZMod 8740842787) ^ ((8740842787 - 1) / 53) = 2018357810 := by
      reduce_mod_char
    rw [hpow]
    decide +kernel
  have hneq_234931 : (2 : ZMod 8740842787) ^ ((8740842787 - 1) / 234931) ≠ 1 := by
    have hpow : (2 : ZMod 8740842787) ^ ((8740842787 - 1) / 234931) = 6692626204 := by
      reduce_mod_char
    rw [hpow]
    decide +kernel
  refine prime_of_lucas_list 8740842787 2 [2, 3, 3, 3, 13, 53, 234931] ?_ ?_ ?_ ?_
  · norm_num [List.prod_cons, List.prod_nil]
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_3
    · exact prime_3
    · exact prime_13
    · exact prime_53
    · exact prime_234931
  · reduce_mod_char
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hneq_2
    · exact hneq_3
    · exact hneq_3
    · exact hneq_3
    · exact hneq_13
    · exact hneq_53
    · exact hneq_234931

#print axioms Paper7Moduli.prime_8740842787

theorem prime_52445056723 : Nat.Prime 52445056723 := by
  have hneq_2 : (11 : ZMod 52445056723) ^ ((52445056723 - 1) / 2) ≠ 1 := by
    have hpow : (11 : ZMod 52445056723) ^ ((52445056723 - 1) / 2) = 52445056722 := by
      reduce_mod_char
    rw [hpow]
    decide +kernel
  have hneq_3 : (11 : ZMod 52445056723) ^ ((52445056723 - 1) / 3) ≠ 1 := by
    have hpow : (11 : ZMod 52445056723) ^ ((52445056723 - 1) / 3) = 10394799839 := by
      reduce_mod_char
    rw [hpow]
    decide +kernel
  have hneq_8740842787 : (11 : ZMod 52445056723) ^ ((52445056723 - 1) / 8740842787) ≠ 1 := by
    have hpow : (11 : ZMod 52445056723) ^ ((52445056723 - 1) / 8740842787) = 1771561 := by
      reduce_mod_char
    rw [hpow]
    decide +kernel
  refine prime_of_lucas_list 52445056723 11 [2, 3, 8740842787] ?_ ?_ ?_ ?_
  · norm_num [List.prod_cons, List.prod_nil]
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_8740842787
  · reduce_mod_char
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact hneq_2
    · exact hneq_3
    · exact hneq_8740842787

#print axioms Paper7Moduli.prime_52445056723

theorem prime_1000000000000000003 : Nat.Prime 1000000000000000003 := by
  have hneq_2 : (2 : ZMod 1000000000000000003) ^ ((1000000000000000003 - 1) / 2) ≠ 1 := by
    have hpow : (2 : ZMod 1000000000000000003) ^ ((1000000000000000003 - 1) / 2) = 1000000000000000002 := by
      reduce_mod_char
    rw [hpow]
    decide +kernel
  have hneq_3 : (2 : ZMod 1000000000000000003) ^ ((1000000000000000003 - 1) / 3) ≠ 1 := by
    have hpow : (2 : ZMod 1000000000000000003) ^ ((1000000000000000003 - 1) / 3) = 499999999500000001 := by
      reduce_mod_char
    rw [hpow]
    decide +kernel
  have hneq_17 : (2 : ZMod 1000000000000000003) ^ ((1000000000000000003 - 1) / 17) ≠ 1 := by
    have hpow : (2 : ZMod 1000000000000000003) ^ ((1000000000000000003 - 1) / 17) = 594162475312840939 := by
      reduce_mod_char
    rw [hpow]
    decide +kernel
  have hneq_131 : (2 : ZMod 1000000000000000003) ^ ((1000000000000000003 - 1) / 131) ≠ 1 := by
    have hpow : (2 : ZMod 1000000000000000003) ^ ((1000000000000000003 - 1) / 131) = 612361696629028658 := by
      reduce_mod_char
    rw [hpow]
    decide +kernel
  have hneq_1427 : (2 : ZMod 1000000000000000003) ^ ((1000000000000000003 - 1) / 1427) ≠ 1 := by
    have hpow : (2 : ZMod 1000000000000000003) ^ ((1000000000000000003 - 1) / 1427) = 513951916627139555 := by
      reduce_mod_char
    rw [hpow]
    decide +kernel
  have hneq_52445056723 : (2 : ZMod 1000000000000000003) ^ ((1000000000000000003 - 1) / 52445056723) ≠ 1 := by
    have hpow : (2 : ZMod 1000000000000000003) ^ ((1000000000000000003 - 1) / 52445056723) = 988224617572240685 := by
      reduce_mod_char
    rw [hpow]
    decide +kernel
  refine prime_of_lucas_list 1000000000000000003 2 [2, 3, 17, 131, 1427, 52445056723] ?_ ?_ ?_ ?_
  · norm_num [List.prod_cons, List.prod_nil]
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_17
    · exact prime_131
    · exact prime_1427
    · exact prime_52445056723
  · reduce_mod_char
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hneq_2
    · exact hneq_3
    · exact hneq_17
    · exact hneq_131
    · exact hneq_1427
    · exact hneq_52445056723

#print axioms Paper7Moduli.prime_1000000000000000003

theorem prime_2305843009213693951 : Nat.Prime 2305843009213693951 := by
  have hneq_2 : (37 : ZMod 2305843009213693951) ^ ((2305843009213693951 - 1) / 2) ≠ 1 := by
    have hpow : (37 : ZMod 2305843009213693951) ^ ((2305843009213693951 - 1) / 2) = 2305843009213693950 := by
      reduce_mod_char
    rw [hpow]
    decide +kernel
  have hneq_3 : (37 : ZMod 2305843009213693951) ^ ((2305843009213693951 - 1) / 3) ≠ 1 := by
    have hpow : (37 : ZMod 2305843009213693951) ^ ((2305843009213693951 - 1) / 3) = 1669582390241348315 := by
      reduce_mod_char
    rw [hpow]
    decide +kernel
  have hneq_5 : (37 : ZMod 2305843009213693951) ^ ((2305843009213693951 - 1) / 5) ≠ 1 := by
    have hpow : (37 : ZMod 2305843009213693951) ^ ((2305843009213693951 - 1) / 5) = 725554454131936870 := by
      reduce_mod_char
    rw [hpow]
    decide +kernel
  have hneq_7 : (37 : ZMod 2305843009213693951) ^ ((2305843009213693951 - 1) / 7) ≠ 1 := by
    have hpow : (37 : ZMod 2305843009213693951) ^ ((2305843009213693951 - 1) / 7) = 1165310750493918737 := by
      reduce_mod_char
    rw [hpow]
    decide +kernel
  have hneq_11 : (37 : ZMod 2305843009213693951) ^ ((2305843009213693951 - 1) / 11) ≠ 1 := by
    have hpow : (37 : ZMod 2305843009213693951) ^ ((2305843009213693951 - 1) / 11) = 2266698407988980144 := by
      reduce_mod_char
    rw [hpow]
    decide +kernel
  have hneq_13 : (37 : ZMod 2305843009213693951) ^ ((2305843009213693951 - 1) / 13) ≠ 1 := by
    have hpow : (37 : ZMod 2305843009213693951) ^ ((2305843009213693951 - 1) / 13) = 1032504562576723207 := by
      reduce_mod_char
    rw [hpow]
    decide +kernel
  have hneq_31 : (37 : ZMod 2305843009213693951) ^ ((2305843009213693951 - 1) / 31) ≠ 1 := by
    have hpow : (37 : ZMod 2305843009213693951) ^ ((2305843009213693951 - 1) / 31) = 484083891529811867 := by
      reduce_mod_char
    rw [hpow]
    decide +kernel
  have hneq_41 : (37 : ZMod 2305843009213693951) ^ ((2305843009213693951 - 1) / 41) ≠ 1 := by
    have hpow : (37 : ZMod 2305843009213693951) ^ ((2305843009213693951 - 1) / 41) = 1562651311446036838 := by
      reduce_mod_char
    rw [hpow]
    decide +kernel
  have hneq_61 : (37 : ZMod 2305843009213693951) ^ ((2305843009213693951 - 1) / 61) ≠ 1 := by
    have hpow : (37 : ZMod 2305843009213693951) ^ ((2305843009213693951 - 1) / 61) = 35184372088832 := by
      reduce_mod_char
    rw [hpow]
    decide +kernel
  have hneq_151 : (37 : ZMod 2305843009213693951) ^ ((2305843009213693951 - 1) / 151) ≠ 1 := by
    have hpow : (37 : ZMod 2305843009213693951) ^ ((2305843009213693951 - 1) / 151) = 1433721343585656393 := by
      reduce_mod_char
    rw [hpow]
    decide +kernel
  have hneq_331 : (37 : ZMod 2305843009213693951) ^ ((2305843009213693951 - 1) / 331) ≠ 1 := by
    have hpow : (37 : ZMod 2305843009213693951) ^ ((2305843009213693951 - 1) / 331) = 185945230422323302 := by
      reduce_mod_char
    rw [hpow]
    decide +kernel
  have hneq_1321 : (37 : ZMod 2305843009213693951) ^ ((2305843009213693951 - 1) / 1321) ≠ 1 := by
    have hpow : (37 : ZMod 2305843009213693951) ^ ((2305843009213693951 - 1) / 1321) = 30210013857155493 := by
      reduce_mod_char
    rw [hpow]
    decide +kernel
  refine prime_of_lucas_list 2305843009213693951 37 [2, 3, 3, 5, 5, 7, 11, 13, 31, 41, 61, 151, 331, 1321] ?_ ?_ ?_ ?_
  · norm_num [List.prod_cons, List.prod_nil]
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_2
    · exact prime_3
    · exact prime_3
    · exact prime_5
    · exact prime_5
    · exact prime_7
    · exact prime_11
    · exact prime_13
    · exact prime_31
    · exact prime_41
    · exact prime_61
    · exact prime_151
    · exact prime_331
    · exact prime_1321
  · reduce_mod_char
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hneq_2
    · exact hneq_3
    · exact hneq_3
    · exact hneq_5
    · exact hneq_5
    · exact hneq_7
    · exact hneq_11
    · exact hneq_13
    · exact hneq_31
    · exact hneq_41
    · exact hneq_61
    · exact hneq_151
    · exact hneq_331
    · exact hneq_1321

#print axioms Paper7Moduli.prime_2305843009213693951

end Paper7Moduli
