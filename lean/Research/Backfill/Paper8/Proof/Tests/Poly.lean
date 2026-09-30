import Research.Backfill.Paper8.Proof.Orb.Main

/-!
# Paper 8, known-answer tests (agent `tests`): the secular polynomial and the orbits

Tests of `secular`, `R2`, `IsOrbitFactor`, `IsEvenPoly`, `mirror` and `nonEvenPairs` on the small
multisets named in the paper and in the two reviews (including the data of `Sharp_T15`,
`Sharp_T18` and the tightness of `Lemma_U1`, as in `review-v2/Scratch/Sanity.lean`), with
instances that must come out false. All values are computed from the definitions; irreducibility
of a quadratic `x² + bx + c` is shown by `b² - 4c` not being a square.
-/

set_option autoImplicit false

open BackfillPaper8.Challenge
open Polynomial hiding mirror

namespace P8Tests

/-! ## Helpers -/

/-- An integer strictly between two consecutive squares is not a square. -/
theorem not_isSquare_of_lt {z r : ℤ} (hr : 0 ≤ r) (h1 : r * r < z) (h2 : z < (r + 1) * (r + 1)) :
    ¬ IsSquare z := by
  rintro ⟨s, rfl⟩
  have h3 : |s| * |s| = s * s := abs_mul_abs_self s
  have h4 : 0 ≤ |s| := abs_nonneg s
  rcases le_or_gt |s| r with h | h
  · nlinarith
  · have h5 : r + 1 ≤ |s| := h
    nlinarith

theorem not_isSquare_2 : ¬ IsSquare (2 : ℤ) :=
  not_isSquare_of_lt (r := 1) (by norm_num) (by norm_num) (by norm_num)

theorem not_isSquare_3 : ¬ IsSquare (3 : ℤ) :=
  not_isSquare_of_lt (r := 1) (by norm_num) (by norm_num) (by norm_num)

theorem not_isSquare_6 : ¬ IsSquare (6 : ℤ) :=
  not_isSquare_of_lt (r := 2) (by norm_num) (by norm_num) (by norm_num)

theorem not_isSquare_13 : ¬ IsSquare (13 : ℤ) :=
  not_isSquare_of_lt (r := 3) (by norm_num) (by norm_num) (by norm_num)

/-- No rational `c` has `c² = z` when the integer `z` is not a square. -/
theorem rat_sq_ne {z : ℤ} (hz : ¬ IsSquare z) (c : ℚ) : c ^ 2 ≠ (z : ℚ) := by
  intro h
  apply hz
  rw [← Rat.isSquare_intCast_iff]
  exact ⟨c, by rw [← h]; ring⟩

/-- No integer `w` has `w² = z` when `z` is not a square. -/
theorem int_sq_ne {z : ℤ} (hz : ¬ IsSquare z) (w : ℤ) : w ^ 2 ≠ z := by
  intro h
  exact hz ⟨w, by rw [← h]; ring⟩

theorem natCast_sq_eq_sq {q c : ℕ} : (q : ℤ) ^ 2 = (c : ℤ) ^ 2 ↔ q = c := by
  constructor
  · intro h
    have h' : q ^ 2 = c ^ 2 := by exact_mod_cast h
    exact Nat.pow_left_injective (by norm_num) h'
  · rintro rfl
    rfl

/-- `R = t - (b + k_b)` when `B = {b}`. -/
theorem secular_of_Bset_eq_singleton {m : Multiset ℕ} {b : ℕ} (hB : Bset m = {b}) :
    secular m = X - C ((b : ℤ) + (kb m b : ℤ)) := by
  unfold secular
  rw [hB, Finset.prod_singleton, Finset.sum_singleton, Finset.erase_singleton, Finset.prod_empty,
    mul_one, map_add]
  ring

/-- `R = (t - b)(t - b') - k_b (t - b') - k_{b'} (t - b)` when `B = {b, b'}`. -/
theorem secular_of_Bset_eq_pair {m : Multiset ℕ} {b b' : ℕ} (hne : b ≠ b')
    (hB : Bset m = {b, b'}) :
    secular m = (X - C (b : ℤ)) * (X - C (b' : ℤ)) - C (kb m b : ℤ) * (X - C (b' : ℤ)) -
      C (kb m b' : ℤ) * (X - C (b : ℤ)) := by
  have e1 : ({b, b'} : Finset ℕ).erase b = {b'} :=
    Finset.erase_insert (by simpa using hne)
  have e2 : ({b, b'} : Finset ℕ).erase b' = {b} := by
    rw [Finset.erase_insert_of_ne hne, Finset.erase_singleton]
    rfl
  unfold secular
  rw [hB, Finset.prod_pair hne, Finset.sum_pair hne, e1, e2, Finset.prod_singleton,
    Finset.prod_singleton]
  ring

/-! ## `secular`: the secular polynomial `R` -/

-- Prop 5.6(c) and (a), proofs: "R(t) = t - 4" for `T(3)` and for `T(2,2)`
theorem test_secular_3 : secular {3} = X - C 4 := by
  rw [secular_of_Bset_eq_singleton (b := 3) (by decide), show kb {3} 3 = 1 by decide]
  norm_num

theorem test_secular_22 : secular {2, 2} = X - C 4 := by
  rw [secular_of_Bset_eq_singleton (b := 2) (by decide), show kb {2, 2} 2 = 2 by decide]
  norm_num

-- review T3: "R = t - 6" for `(5)` and "R = t - 2" for `(1)`; also `R = t - 3` for `(2)`
theorem test_secular_5 : secular {5} = X - C 6 := by
  rw [secular_of_Bset_eq_singleton (b := 5) (by decide), show kb {5} 5 = 1 by decide]
  norm_num

theorem test_secular_1 : secular {1} = X - C 2 := by
  rw [secular_of_Bset_eq_singleton (b := 1) (by decide), show kb {1} 1 = 1 by decide]
  norm_num

theorem test_secular_2 : secular {2} = X - C 3 := by
  rw [secular_of_Bset_eq_singleton (b := 2) (by decide), show kb {2} 2 = 1 by decide]
  norm_num

-- §6 (`Sharp_T15`): "R(t) = t - 16" for `T(15)` (review v2, `Scratch/Sanity.lean`)
theorem test_secular_15 : secular {15} = X - C 16 := by
  rw [secular_of_Bset_eq_singleton (b := 15) (by decide), show kb {15} 15 = 1 by decide]
  norm_num

-- Prop 5.6(b), proof: "R(t) = (t - 1)(t - 4)" for `T(2,0,0)`
theorem test_secular_200 : secular {2, 0, 0} = (X - C 1) * (X - C 4) := by
  rw [secular_of_Bset_eq_pair (b := 0) (b' := 2) (by norm_num) (by decide),
    show kb {2, 0, 0} 0 = 2 by decide, show kb {2, 0, 0} 2 = 1 by decide]
  apply Polynomial.funext
  intro r
  simp
  ring

-- `T(3,0,0,0)`: `R(t) = t(t - 3) - 3(t - 3) - t = t² - 7t + 9`
theorem test_secular_3000 : secular {3, 0, 0, 0} = X ^ 2 - C 7 * X + C 9 := by
  rw [secular_of_Bset_eq_pair (b := 0) (b' := 3) (by norm_num) (by decide),
    show kb {3, 0, 0, 0} 0 = 3 by decide, show kb {3, 0, 0, 0} 3 = 1 by decide]
  apply Polynomial.funext
  intro r
  simp
  ring

-- `T(2,0)`: `R(t) = t(t - 2) - (t - 2) - t = t² - 4t + 2`
theorem test_secular_20 : secular {2, 0} = X ^ 2 - C 4 * X + C 2 := by
  rw [secular_of_Bset_eq_pair (b := 0) (b' := 2) (by norm_num) (by decide),
    show kb {2, 0} 0 = 1 by decide, show kb {2, 0} 2 = 1 by decide]
  apply Polynomial.funext
  intro r
  simp
  ring

-- §6 (`Sharp_T18`): "R(t) = t² - 21t + 36" for `T(18,0,0)` (review v2, `Scratch/Sanity.lean`)
theorem test_secular_1800 : secular {18, 0, 0} = X ^ 2 - C 21 * X + C 36 := by
  rw [secular_of_Bset_eq_pair (b := 0) (b' := 18) (by norm_num) (by decide),
    show kb {18, 0, 0} 0 = 2 by decide, show kb {18, 0, 0} 18 = 1 by decide]
  apply Polynomial.funext
  intro r
  simp
  ring

-- FALSE instance: the sign of the sum matters (with `+` the value for `(5)` would be `t - 4`)
theorem test_secular_5_ne : secular {5} ≠ X - C 4 := by
  rw [test_secular_5]
  intro h
  have := congrArg (Polynomial.eval 0) h
  norm_num at this

/-! ## `R2 = R(x²)` -/

-- review v2, `Scratch/Sanity.lean`: `R(x²) = x² - 16` for `T(15)`
theorem test_R2_15 : R2 {15} = X ^ 2 - C 16 := by
  unfold R2
  rw [test_secular_15]
  simp only [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, map_sub,
    Polynomial.expand_X, Polynomial.expand_C]
  norm_num

-- review v2, `Scratch/Sanity.lean`: `R(x²) = (x² + 3x - 6)(x² - 3x - 6)` for `T(18,0,0)`
theorem test_R2_1800 : R2 {18, 0, 0} = (X ^ 2 + C 3 * X - C 6) * (X ^ 2 - C 3 * X - C 6) := by
  apply Polynomial.funext
  intro r
  unfold R2
  rw [test_secular_1800]
  simp [Polynomial.expand_eval]
  ring

-- review T3: "N_II = 1 for (3,0,0,0) (pair x² ∓ x - 3)": `R(x²) = (x² - x - 3)(x² + x - 3)`
theorem test_R2_3000 : R2 {3, 0, 0, 0} = (X ^ 2 - X - C 3) * (X ^ 2 + X - C 3) := by
  apply Polynomial.funext
  intro r
  unfold R2
  rw [test_secular_3000]
  simp [Polynomial.expand_eval]
  ring

-- Lemma 3.3(c) for `T(1)`: `R(x²) = x² - 2`
theorem test_R2_1 : R2 {1} = X ^ 2 - C 2 := by
  unfold R2
  rw [test_secular_1]
  simp only [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, map_sub,
    Polynomial.expand_X, Polynomial.expand_C]
  norm_num

/-! ## `IsOrbitFactor`, `IsEvenPoly`, `mirror`, `nonEvenPairs` -/

-- `Sharp_T15`, first two conjuncts: `x - 4` is an orbit factor of `T(15)` and is not even
theorem test_orbit_15 : IsOrbitFactor (branchMS (![15] : Fin 1 → ℕ)) (X - C 4) := by
  rw [show branchMS (![15] : Fin 1 → ℕ) = {15} by decide]
  refine ⟨Polynomial.monic_X_sub_C 4,
    Polynomial.irreducible_of_degree_eq_one (Polynomial.degree_X_sub_C 4), ?_⟩
  rw [test_R2_15]
  refine ⟨X + C 4, ?_⟩
  rw [show (C 16 : ℚ[X]) = C 4 * C 4 by rw [← C_mul]; norm_num]
  ring

theorem test_noneven_15 : ¬ IsEvenPoly (X - C (4 : ℚ)) := by
  unfold IsEvenPoly
  intro h
  have := congrArg (Polynomial.eval (1 : ℚ)) h
  simp at this
  norm_num at this

-- Lemma 3.3(b): the orbit of `±f(-x)` is the negative one: `mirror (x - 4) = x + 4`
theorem test_mirror_15 : mirror (X - C (4 : ℚ)) = X + C 4 := P8Orb.mirror_X_sub_C 4

-- FALSE instance: `x² - 16` divides `R(x²)` for `T(15)` but is not irreducible
theorem test_not_orbit_15_sq : ¬ IsOrbitFactor {15} (X ^ 2 - C 16) := by
  rintro ⟨-, hirr, -⟩
  have h : (X ^ 2 - C 16 : ℚ[X]) = (X - C 4) * (X + C 4) := by
    rw [show (C 16 : ℚ[X]) = C 4 * C 4 by rw [← C_mul]; norm_num]
    ring
  rw [h] at hirr
  rcases hirr.isUnit_or_isUnit rfl with hu | hu
  · have := natDegree_eq_zero_of_isUnit hu
    rw [natDegree_X_sub_C] at this
    exact one_ne_zero this
  · have := natDegree_eq_zero_of_isUnit hu
    rw [natDegree_X_add_C] at this
    exact one_ne_zero this

-- Lemma 3.3(c): for `T(1)` the integer root `2` of `R = t - 2` is not a square, so `x² - 2` is an
-- even orbit factor
theorem test_orbit_1 : IsOrbitFactor {1} (X ^ 2 - C 2) := by
  refine ⟨monic_X_pow_sub_C 2 (by norm_num), ?_, ⟨1, by rw [test_R2_1, mul_one]⟩⟩
  apply X_pow_sub_C_irreducible_of_prime Nat.prime_two
  intro c hc
  exact rat_sq_ne not_isSquare_2 c (by rw [hc]; norm_num)

theorem test_even_1 : IsEvenPoly (X ^ 2 - C (2 : ℚ)) := by
  unfold IsEvenPoly
  simp

-- `T(3,0,0,0)`: `x² - x - 3` (discriminant 13) is a monic irreducible, non-even factor of `R(x²)`
theorem natDegree_3000 : (X ^ 2 - X - C 3 : ℚ[X]).natDegree = 2 := by compute_degree!

theorem irreducible_3000 : Irreducible (X ^ 2 - X - C 3 : ℚ[X]) := by
  refine irreducible_of_degree_le_three_of_not_isRoot (by rw [natDegree_3000]; decide)
    (fun c hc => ?_)
  have h : c ^ 2 - c - 3 = 0 := by simpa using hc
  exact rat_sq_ne not_isSquare_13 (2 * c - 1) (by push_cast; linear_combination 4 * h)

theorem test_orbit_3000 : IsOrbitFactor {3, 0, 0, 0} (X ^ 2 - X - C 3) := by
  refine ⟨by monicity!, irreducible_3000, ?_⟩
  rw [test_R2_3000]
  exact dvd_mul_right _ _

theorem test_mirror_3000 : mirror (X ^ 2 - X - C 3 : ℚ[X]) = X ^ 2 + X - C 3 := by
  rw [P8Orb.mirror_def', natDegree_3000]
  apply Polynomial.funext
  intro r
  simp

theorem test_noneven_3000 : ¬ IsEvenPoly (X ^ 2 - X - C 3 : ℚ[X]) := by
  unfold IsEvenPoly
  intro h
  have := congrArg (Polynomial.eval (1 : ℚ)) h
  norm_num at this

-- Lemma 3.3(b): `{x² - x - 3, x² + x - 3}` is a non-even pair of `T(3,0,0,0)`
theorem test_pair_3000 :
    ({X ^ 2 - X - C 3, X ^ 2 + X - C 3} : Set ℚ[X]) ∈ nonEvenPairs {3, 0, 0, 0} :=
  ⟨X ^ 2 - X - C 3, test_orbit_3000, test_noneven_3000, by rw [test_mirror_3000]⟩

-- `Sharp_T18` data (review v2, `Scratch/Sanity.lean`): `mirror`, degree, non-evenness
theorem test_mirror_18 : mirror (X ^ 2 + C 3 * X - C 6 : ℚ[X]) = X ^ 2 - C 3 * X - C 6 := by
  have hd : (X ^ 2 + C 3 * X - C 6 : ℚ[X]).natDegree = 2 := by compute_degree!
  rw [P8Orb.mirror_def', hd]
  apply Polynomial.funext
  intro r
  simp
  ring

theorem test_natDegree_18 : (X ^ 2 + C 3 * X - C 6 : ℚ[X]).natDegree ≠ 1 := by
  have hd : (X ^ 2 + C 3 * X - C 6 : ℚ[X]).natDegree = 2 := by compute_degree!
  omega

theorem test_noneven_18 : ¬ IsEvenPoly (X ^ 2 + C 3 * X - C 6 : ℚ[X]) := by
  unfold IsEvenPoly
  intro h
  have := congrArg (Polynomial.eval (1 : ℚ)) h
  simp at this
  norm_num at this

-- `Sharp_T18`, first conjunct: `x² + 3x - 6` (discriminant 33) is an orbit factor of `T(18,0,0)`
theorem irreducible_18 : Irreducible (X ^ 2 + C 3 * X - C 6 : ℚ[X]) := by
  have hd : (X ^ 2 + C 3 * X - C 6 : ℚ[X]).natDegree = 2 := by compute_degree!
  refine irreducible_of_degree_le_three_of_not_isRoot (by rw [hd]; decide) (fun c hc => ?_)
  have h : c ^ 2 + 3 * c - 6 = 0 := by simpa using hc
  exact rat_sq_ne (not_isSquare_of_lt (z := 33) (r := 5) (by norm_num) (by norm_num) (by norm_num))
    (2 * c + 3) (by push_cast; linear_combination 4 * h)

theorem test_orbit_18 :
    IsOrbitFactor (branchMS (![18, 0, 0] : Fin 3 → ℕ)) (X ^ 2 + C 3 * X - C 6) := by
  rw [show branchMS (![18, 0, 0] : Fin 3 → ℕ) = {18, 0, 0} by decide]
  refine ⟨by monicity!, irreducible_18, ?_⟩
  rw [test_R2_1800]
  exact dvd_mul_right _ _

-- review v2 on `Sharp_T18`: "This is one irrational pair": `{x² + 3x - 6, x² - 3x - 6}`
theorem test_pair_18 : ({X ^ 2 + C 3 * X - C 6, X ^ 2 - C 3 * X - C 6} : Set ℚ[X]) ∈
    nonEvenPairs {18, 0, 0} := by
  refine ⟨X ^ 2 + C 3 * X - C 6, ?_, test_noneven_18, by rw [test_mirror_18]⟩
  have h := test_orbit_18
  rwa [show branchMS (![18, 0, 0] : Fin 3 → ℕ) = {18, 0, 0} by decide] at h

-- `Lemma_U1` is tight (review v2, `Scratch/Sanity.lean`): for `T(15)` the root `16` of `R` equals
-- `b* + k = 15 + 1`
theorem test_U1_tight_15 : aeval ((bstar (branchMS (![15] : Fin 1 → ℕ)) : ℝ) + (1 : ℕ))
    (secular (branchMS (![15] : Fin 1 → ℕ))) = 0 := by
  rw [show branchMS (![15] : Fin 1 → ℕ) = {15} by decide, test_secular_15,
    show bstar {15} = 15 by decide]
  simp only [map_sub, Polynomial.aeval_X, Polynomial.aeval_C]
  norm_num

end P8Tests
