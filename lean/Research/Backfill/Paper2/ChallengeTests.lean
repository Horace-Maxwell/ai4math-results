import Research.Backfill.Paper2.Challenge

/-!
# Paper 2 back-fill: known-answer tests for the challenge definitions

Every custom definition of `Challenge.lean` is exercised on small cases taken from the paper
or from the OEIS entries (local b-files in `certificates/oeis-hanna/bfiles/`), with at least one
instance that must come out false. Only kernel-checked tactics are used (`decide`, `norm_num`,
`simp`, `ring`, `rfl`); no `native_decide`.
-/

set_option autoImplicit false

namespace BackfillPaper2.ChallengeTests

open PowerSeries BackfillPaper2.Challenge

/-! ## Mathlib semantics used by the statements -/

/-- `A.subst h` is `A(h)` (h substituted INTO A), as in `SubstSemanticsCheck.lean`. -/
theorem original_test_01 : (X ^ 2 : PowerSeries ℤ).subst (X + X ^ 2 : PowerSeries ℤ) = (X + X ^ 2) ^ 2 := by
  have ha : HasSubst (X + X ^ 2 : PowerSeries ℤ) := HasSubst.of_constantCoeff_zero' (by simp)
  rw [← coe_substAlgHom ha, map_pow, coe_substAlgHom ha, subst_X ha]

/-- False instance: the other direction `h(A)` would give `X² + X⁴`, which differs at `x³`. -/
theorem original_test_02 : (X ^ 2 : PowerSeries ℤ).subst (X + X ^ 2 : PowerSeries ℤ) ≠ X ^ 2 + X ^ 4 := by
  have ha : HasSubst (X + X ^ 2 : PowerSeries ℤ) := HasSubst.of_constantCoeff_zero' (by simp)
  rw [← coe_substAlgHom ha, map_pow, coe_substAlgHom ha, subst_X ha]
  intro h
  have h3 := congrArg (coeff 3) h
  have e : ((X : PowerSeries ℤ) + X ^ 2) ^ 2 = X ^ 2 + X ^ 3 + X ^ 3 + X ^ 4 := by ring
  rw [e] at h3
  simp [coeff_X_pow] at h3

/-- `invOfUnit` really inverts: `h = x²/(1 − 2x − 4x²)` satisfies `h (1 − 2x − 4x²) = x²`. -/
theorem original_test_03 : h274479 * (1 - 2 * X - 4 * X ^ 2) = X ^ 2 := by
  rw [h274479, mul_assoc, mul_comm (PowerSeries.invOfUnit _ _), PowerSeries.mul_invOfUnit,
    mul_one]
  simp

/-- `φ = x(1 − x − x²)/(1 − x³)` satisfies `φ (1 − x³) = x(1 − x − x²)`. -/
theorem original_test_04 : phi388734 * (1 - X ^ 3) = X * (1 - X - X ^ 2) := by
  rw [phi388734, mul_assoc, mul_comm (PowerSeries.invOfUnit _ _), PowerSeries.mul_invOfUnit,
    mul_one]
  simp

/-- `B = (1 − x³)/(1 − x − x²)` satisfies `B (1 − x − x²) = 1 − x³`. -/
theorem original_test_05 : B388734 * (1 - X - X ^ 2) = 1 - X ^ 3 := by
  rw [B388734, mul_assoc, mul_comm (PowerSeries.invOfUnit _ _), PowerSeries.mul_invOfUnit,
    mul_one]
  simp

/-- The Mathlib cast `ℚ → ZMod 3` of `1/2` is `2` (`2·2 = 4 ≡ 1`). -/
theorem original_test_06 : ((1 / 2 : ℚ) : ZMod 3) = 2 := by
  rw [Rat.cast_div_of_ne_zero (by norm_num) (by decide)]
  norm_num
  exact inv_eq_of_mul_eq_one_right (by decide)

/-! ## `catalanC` (the paper's `C = ∑_{n≥1} C_{n−1} xⁿ`, built from Mathlib's `catalanSeries`) -/

theorem original_test_07 : coeff 1 catalanC = 1 := by
  rw [catalanC, show (1 : ℕ) = 0 + 1 from rfl, coeff_succ_X_mul, coeff_map,
    PowerSeries.catalanSeries_coeff]
  simp [catalan_zero]
theorem original_test_08 : coeff 3 catalanC = 2 := by
  rw [catalanC, show (3 : ℕ) = 2 + 1 from rfl, coeff_succ_X_mul, coeff_map,
    PowerSeries.catalanSeries_coeff, catalan_two]
  simp
theorem original_test_09 : coeff 4 catalanC = 5 := by
  rw [catalanC, show (4 : ℕ) = 3 + 1 from rfl, coeff_succ_X_mul, coeff_map,
    PowerSeries.catalanSeries_coeff, catalan_three]
  simp
/-- False instance: the paper's `C` has no constant term (unlike Mathlib's `catalanSeries`). -/
theorem original_test_10 : coeff 0 catalanC ≠ 1 := by simp [catalanC]
/-- `catalanC` satisfies the paper's defining relation `C = x + C²` (l. 125), from Mathlib's
`catalanSeries_sq_mul_X_add_one`. -/
theorem original_test_11 : catalanC = X + catalanC ^ 2 := by
  have h := congrArg (PowerSeries.map (Nat.castRingHom ℤ)) PowerSeries.catalanSeries_sq_mul_X_add_one
  simp only [map_add, map_mul, map_pow, map_one, map_X] at h
  rw [catalanC]
  linear_combination (-(X : PowerSeries ℤ)) * h
/-- `C₅ = 42` (paper, l. 437). -/
theorem original_test_12 : catalan 5 = 42 := by
  rw [catalan_eq_centralBinom_div]
  decide

/-! ## `ternary`, `ternarySeries` (A001764: 1, 1, 3, 12, 55, 273) -/

theorem original_test_13 : ternary 0 = 1 ∧ ternary 1 = 1 ∧ ternary 2 = 3 ∧ ternary 3 = 12 ∧ ternary 4 = 55 ∧
    ternary 5 = 273 := by decide
/-- The division in `ternary` is exact on these cases. -/
theorem original_test_14 : ∀ k < 8, (2 * k + 1) ∣ Nat.choose (3 * k) k := by decide
/-- False instance. -/
theorem original_test_15 : ternary 2 ≠ 2 := by decide
theorem original_test_16 : coeff 5 ternarySeries = 3 := by simp [ternarySeries]; decide
theorem original_test_17 : coeff 7 ternarySeries = 12 := by simp [ternarySeries]; decide
/-- `V` is odd: even coefficients vanish. -/
theorem original_test_18 : coeff 4 ternarySeries = 0 := by simp [ternarySeries]

/-! ## `Additive3` -/

theorem original_test_19 : Additive3 (X : PowerSeries (ZMod 3)) := by
  intro m hm
  rw [coeff_X, ite_eq_right]
  rintro rfl
  exact hm ⟨0, rfl⟩

/-- False instance: `x²` is not additive. -/
theorem original_test_20 : ¬ Additive3 (X ^ 2 : PowerSeries (ZMod 3)) := by
  intro h
  have := h 2 (by
    rintro ⟨j, hj⟩
    rcases j with _ | _ | j
    · norm_num at hj
    · norm_num at hj
    · have : 9 ≤ 3 ^ (j + 2) := by
        calc 9 = 3 ^ 2 := by norm_num
          _ ≤ 3 ^ (j + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega)
  simp [coeff_X_pow] at this

/-! ## `P184894`, `a184894` (b-file: 1, 2, 9, 78, 1045) -/

theorem original_test_21 : P184894 1 = Polynomial.X + Polynomial.X ^ 3 := by simp [P184894]

theorem P2_eq : P184894 2 = Polynomial.X + Polynomial.C 2 * Polynomial.X ^ 3 +
    Polynomial.C 3 * Polynomial.X ^ 5 + Polynomial.C 3 * Polynomial.X ^ 7 + Polynomial.X ^ 9 := by
  simp only [P184894]
  simp only [map_ofNat]
  ring

theorem original_test_22 : a184894 1 = 1 := by
  simp [a184894, P184894]

theorem original_test_23 : a184894 2 = 2 := by
  rw [a184894, P2_eq]
  simp [Polynomial.coeff_X_pow, Polynomial.coeff_X]

/-- False instance. -/
theorem original_test_24 : a184894 2 ≠ 1 := by
  rw [a184894, P2_eq]
  simp [Polynomial.coeff_X_pow, Polynomial.coeff_X]

/-- The exceptional indices `(3ⁿ+1)/2` for `n = 0, …, 6`: 1, 2, 5, 14, 41, 122, 365 (the
entry's example lists the non-zero terms at the first six). -/
theorem original_test_25 : (List.range 7).map (fun n => (3 ^ n + 1) / 2) = [1, 2, 5, 14, 41, 122, 365] := by
  decide

/-- Lucas at `365 = (111112)₃`, `6 = (20)₃` (l. 386–387): `binom(365, 6) ≡ 0 (mod 3)`, while
`binom(122, 5) ≢ 0`. -/
theorem original_test_26 : Nat.choose 365 6 % 3 = 0 ∧ Nat.choose 122 5 % 3 = 1 := by
  refine ⟨?_, ?_⟩ <;> norm_num [Nat.choose_eq_descFactorial_div_factorial, Nat.descFactorial,
    Nat.factorial]

/-- The recursion in the proof of Theorem 13 (l. 407–409), `c₀ = 1` and
`2c_k + ∑_{0<i<k} c_i c_{k−i} = [k = 1]` in `𝔽₃`, is solved by the paper's values
`(c₁, …, c₆) = (2, 1, 1, 2, 1, 0)`; they agree with `(−1)^j C_{j−1} mod 3` for
`C₀, …, C₅ = 1, 1, 2, 5, 14, 42` (final remark, l. 434). -/
theorem original_test_27 : let c : ℕ → ZMod 3 := fun k => [1, 2, 1, 1, 2, 1, 0].getD k 0
    (∀ k ∈ Finset.Icc 1 6, 2 * c k + ∑ i ∈ Finset.Ioo 0 k, c i * c (k - i) =
      if k = 1 then 1 else 0) ∧
    (∀ j ∈ Finset.Icc 1 6, c j = (-1) ^ j * (([1, 1, 2, 5, 14, 42].getD (j - 1) 0 : ℕ) : ZMod 3)) := by
  decide

/-! ## `digitsExceptLastLeOne` -/

theorem original_test_28 : Nat.digits 3 365 = [2, 1, 1, 1, 1, 1] := by norm_num
theorem original_test_29 : Nat.digits 3 6 = [0, 2] := by norm_num
theorem original_test_30 : digitsExceptLastLeOne 5 := by
  unfold digitsExceptLastLeOne; norm_num
theorem original_test_31 : digitsExceptLastLeOne 0 := by
  unfold digitsExceptLastLeOne; simp
/-- False instance: `6 = (20)₃` (the failure of Theorem 12(3)). -/
theorem original_test_32 : ¬ digitsExceptLastLeOne 6 := by
  unfold digitsExceptLastLeOne; norm_num

/-! ## `sqrtSeries3` -/

theorem original_test_33 : coeff 1 sqrtSeries3 = 1 := by
  simp [sqrtSeries3, Finset.sum_range_succ]

theorem original_test_34 : coeff 2 sqrtSeries3 = 0 := by
  simp [sqrtSeries3, Finset.sum_range_succ]

/-! ## The equations: false instances and non-uniqueness without the normalizations -/

/-- The zero series does not satisfy the A388734 equation. -/
theorem original_test_35 : ¬ Eq388734 0 := by
  intro h
  have := congrArg constantCoeff h
  simp at this

/-- The zero series satisfies the A120566 equation: the normalization `a(1) = 1` of Theorem 9
is necessary (all coefficients of `0` are even). -/
theorem original_test_36 : Eq120566 0 := by
  have h0 : HasSubst (0 : PowerSeries ℤ) := HasSubst.of_constantCoeff_zero' (by simp)
  have e : (0 : PowerSeries ℤ).subst (0 : PowerSeries ℤ) = 0 := by
    rw [← coe_substAlgHom h0, map_zero]
  simp [Eq120566, e]

/-- The zero series satisfies `B = B∘B + x B∘B∘B` (remark after Theorem 9): the normalization
`B = x + O(x²)` of its uniqueness claim is necessary. -/
theorem original_test_37 : EqInv120566 0 := by
  have h0 : HasSubst (0 : PowerSeries ℤ) := HasSubst.of_constantCoeff_zero' (by simp)
  have e : (0 : PowerSeries ℤ).subst (0 : PowerSeries ℤ) = 0 := by
    rw [← coe_substAlgHom h0, map_zero]
  simp [EqInv120566, e]

/-- The zero series (with `U = 0`) satisfies the A377100 equation: `a(1) = 1` is necessary. -/
theorem original_test_38 : Eq377100 0 0 := by
  have h3 : HasSubst ((X : PowerSeries ℤ) ^ 3) := HasSubst.X_pow three_ne_zero
  refine ⟨?_, by simp⟩
  rw [← coe_substAlgHom h3, map_zero, mul_zero]

/-- The zero series does not satisfy the continued fraction (`T₀ = −x` has constant term 0). -/
theorem original_test_39 (e : ℕ) (T : ℕ → PowerSeries ℤ) : ¬ CF e 0 T := by
  rintro ⟨hT, h0, -⟩
  have := congrArg constantCoeff h0
  simp at this
  rcases hT 0 with h | h <;> simp_all

/-! ## Data gate: the OEIS first terms satisfy the transcribed equations to the stated order

These are polynomial identities in `ℤ[[x]]` (proved by `ring`), not statements about the
solutions: they check that the transcription of each equation fits the entry's data. -/

/-- A388734, b-file `1, 1, 3, 9, 33, 127`: the equation holds modulo `x⁶`. -/
theorem original_test_40 : let p : PowerSeries ℤ := 1 + X + 3 * X ^ 2 + 9 * X ^ 3 + 33 * X ^ 4 + 127 * X ^ 5
    X ^ 6 ∣ p - (1 + X * p ^ 2 + X ^ 2 * (1 - X) * p ^ 3) := by
  intro p
  refine ⟨-517 - 1139 * X - 2448 * X ^ 2 - 7017 * X ^ 3 - 18666 * X ^ 4 - 45091 * X ^ 5 -
    67152 * X ^ 6 - 72162 * X ^ 7 - 223323 * X ^ 8 - 442980 * X ^ 9 - 746379 * X ^ 10 -
    451612 * X ^ 11 + 2048383 * X ^ 12, ?_⟩
  simp only [p]
  ring

/-- False instance: with `(1 + x)` in place of `(1 − x)` the same data fail modulo `x⁶`
(the `x³` coefficient changes by 2). -/
theorem original_test_41 : let p : PowerSeries ℤ := 1 + X + 3 * X ^ 2 + 9 * X ^ 3 + 33 * X ^ 4 + 127 * X ^ 5
    coeff 3 (p - (1 + X * p ^ 2 + X ^ 2 * (1 + X) * p ^ 3)) ≠ 0 := by
  intro p
  have e : p - (1 + X * p ^ 2 + X ^ 2 * (1 + X) * p ^ 3) =
      -(X ^ 3) - X ^ 3 + X ^ 4 * (-(6 : PowerSeries ℤ) - 24 * X ^ 1 - 609 * X ^ 2 - 1517 * X ^ 3 -
        4038 * X ^ 4 - 10791 * X ^ 5 - 29724 * X ^ 6 - 76717 * X ^ 7 - 156702 * X ^ 8 -
        296016 * X ^ 9 - 591501 * X ^ 10 - 1257804 * X ^ 11 - 2447163 * X ^ 12 -
        3645154 * X ^ 13 - 2048383 * X ^ 14) := by
    simp only [p]; ring
  rw [e]
  simp [coeff_X_pow, coeff_X_pow_mul']

/-- A273958 with the Catalan numbers `0, 1, 1, 2, 5, 14` and the b-file `0, 1, 2, 4, 10, 30`:
`C = x + C²` holds modulo `x⁶` and `xA + x²A² = C²` modulo `x⁷`. -/
theorem original_test_42 : let c : PowerSeries ℤ := X + X ^ 2 + 2 * X ^ 3 + 5 * X ^ 4 + 14 * X ^ 5
    let a : PowerSeries ℤ := X + 2 * X ^ 2 + 4 * X ^ 3 + 10 * X ^ 4 + 30 * X ^ 5
    X ^ 6 ∣ c - (X + c ^ 2) ∧ X ^ 7 ∣ X * a + X ^ 2 * a ^ 2 - c ^ 2 := by
  intro c a
  refine ⟨⟨-42 - 48 * X - 81 * X ^ 2 - 140 * X ^ 3 - 196 * X ^ 4, ?_⟩,
    ⟨-12 + 35 * X + 60 * X ^ 2 + 144 * X ^ 3 + 600 * X ^ 4 + 900 * X ^ 5, ?_⟩⟩
  · simp only [c]; ring
  · simp only [c, a]; ring

end BackfillPaper2.ChallengeTests

#print axioms BackfillPaper2.ChallengeTests.original_test_01
#print axioms BackfillPaper2.ChallengeTests.original_test_02
#print axioms BackfillPaper2.ChallengeTests.original_test_03
#print axioms BackfillPaper2.ChallengeTests.original_test_04
#print axioms BackfillPaper2.ChallengeTests.original_test_05
#print axioms BackfillPaper2.ChallengeTests.original_test_06
#print axioms BackfillPaper2.ChallengeTests.original_test_07
#print axioms BackfillPaper2.ChallengeTests.original_test_08
#print axioms BackfillPaper2.ChallengeTests.original_test_09
#print axioms BackfillPaper2.ChallengeTests.original_test_10
#print axioms BackfillPaper2.ChallengeTests.original_test_11
#print axioms BackfillPaper2.ChallengeTests.original_test_12
#print axioms BackfillPaper2.ChallengeTests.original_test_13
#print axioms BackfillPaper2.ChallengeTests.original_test_14
#print axioms BackfillPaper2.ChallengeTests.original_test_15
#print axioms BackfillPaper2.ChallengeTests.original_test_16
#print axioms BackfillPaper2.ChallengeTests.original_test_17
#print axioms BackfillPaper2.ChallengeTests.original_test_18
#print axioms BackfillPaper2.ChallengeTests.original_test_19
#print axioms BackfillPaper2.ChallengeTests.original_test_20
#print axioms BackfillPaper2.ChallengeTests.original_test_21
#print axioms BackfillPaper2.ChallengeTests.P2_eq
#print axioms BackfillPaper2.ChallengeTests.original_test_22
#print axioms BackfillPaper2.ChallengeTests.original_test_23
#print axioms BackfillPaper2.ChallengeTests.original_test_24
#print axioms BackfillPaper2.ChallengeTests.original_test_25
#print axioms BackfillPaper2.ChallengeTests.original_test_26
#print axioms BackfillPaper2.ChallengeTests.original_test_27
#print axioms BackfillPaper2.ChallengeTests.original_test_28
#print axioms BackfillPaper2.ChallengeTests.original_test_29
#print axioms BackfillPaper2.ChallengeTests.original_test_30
#print axioms BackfillPaper2.ChallengeTests.original_test_31
#print axioms BackfillPaper2.ChallengeTests.original_test_32
#print axioms BackfillPaper2.ChallengeTests.original_test_33
#print axioms BackfillPaper2.ChallengeTests.original_test_34
#print axioms BackfillPaper2.ChallengeTests.original_test_35
#print axioms BackfillPaper2.ChallengeTests.original_test_36
#print axioms BackfillPaper2.ChallengeTests.original_test_37
#print axioms BackfillPaper2.ChallengeTests.original_test_38
#print axioms BackfillPaper2.ChallengeTests.original_test_39
#print axioms BackfillPaper2.ChallengeTests.original_test_40
#print axioms BackfillPaper2.ChallengeTests.original_test_41
#print axioms BackfillPaper2.ChallengeTests.original_test_42
