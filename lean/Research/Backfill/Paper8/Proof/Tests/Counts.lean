import Research.Backfill.Paper8.Proof.Tests.Poly

/-!
# Paper 8, known-answer tests (agent `tests`): the pair counts `N_I`, `N_II`, `N_ei`

`N_I` is computed with `P8Orb.NI_eq` (`N_I = #{q ≥ 1 : R(q²) = 0}`, module `Research.Backfill.Paper8.Proof.Orb.Counts` of agent
`orb`); upper bounds for `N_II` come from `P8Orb.two_NII_add_Nrat_le` (`2 N_II + #{integer roots of
R} ≤ r`) and `P8Orb.two_NII_lt_of_not_isSquare` (`2 N_II < r` if `|R(0)|` is not a square), lower
bounds from explicit non-even pairs (`Research.Backfill.Paper8.Proof.Tests.Poly`); `N_ei` is computed from its definition.
-/

set_option autoImplicit false

open BackfillPaper8.Challenge
open Polynomial hiding mirror

namespace P8Tests

/-! ## `NI`: the number of integer pairs -/

theorem NI_eq' (m : Multiset ℕ) (hm : m ≠ 0) :
    NI m = {q : ℕ | 1 ≤ q ∧ (secular m).eval ((q : ℤ) ^ 2) = 0}.ncard :=
  (P8Orb.NI_eq P8Orb.secularMonic m hm).2

theorem NI_of_secular_eq {m : Multiset ℕ} (hm : m ≠ 0) {c : ℤ} (h : secular m = X - C c) :
    NI m = {q : ℕ | 1 ≤ q ∧ (q : ℤ) ^ 2 = c}.ncard := by
  rw [NI_eq' m hm, h]
  congr 1
  ext q
  simp [sub_eq_zero]

-- review T3: "N_I {3} = 1" (the integer pair `x ∓ 2` of `R = t - 4`); the same for `(2,2)`
theorem test_NI_3 : NI {3} = 1 := by
  rw [NI_of_secular_eq (by decide) test_secular_3]
  have : {q : ℕ | 1 ≤ q ∧ (q : ℤ) ^ 2 = 4} = {2} := by
    ext q
    simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
    rw [show (4 : ℤ) = ((2 : ℕ) : ℤ) ^ 2 by norm_num, natCast_sq_eq_sq]
    constructor
    · exact fun h => h.2
    · rintro rfl
      exact ⟨by norm_num, rfl⟩
  rw [this, Set.ncard_singleton]

-- the same value directly from the definition of `nonEvenPairs` (without `P8Orb.NI_eq`): a factor
-- `x + c` of `x² - 4` has `c² = 4`, so the only pair of degree-1 factors is `{x - 2, x + 2}`
theorem test_NI_3_direct : NI {3} = 1 := by
  have hR2 : R2 {3} = X ^ 2 - C 4 := by
    unfold R2
    rw [test_secular_3]
    simp only [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, map_sub,
      Polynomial.expand_X, Polynomial.expand_C]
    norm_num
  have hdvd2 : (X - C (2 : ℚ)) ∣ R2 {3} := by
    rw [hR2]
    refine ⟨X + C 2, ?_⟩
    rw [show (C 4 : ℚ[X]) = C 2 * C 2 by rw [← C_mul]; norm_num]
    ring
  have hset : {P ∈ nonEvenPairs {3} | ∀ f ∈ P, f.natDegree = 1} =
      {({X - C 2, X + C 2} : Set ℚ[X])} := by
    ext P
    simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨⟨f, ⟨hmon, -, hdvd⟩, -, rfl⟩, hdeg⟩
      have hX := hmon.eq_X_add_C (hdeg f (Set.mem_insert _ _))
      have hroot : f.coeff 0 ^ 2 = 4 := by
        rw [hR2, hX] at hdvd
        have := Polynomial.eval_dvd (x := -f.coeff 0) hdvd
        simp only [eval_add, eval_X, eval_C, neg_add_cancel, eval_sub, eval_pow, zero_dvd_iff]
          at this
        linarith
      have hc : f.coeff 0 = 2 ∨ f.coeff 0 = -2 := by
        have h2 : (f.coeff 0 - 2) * (f.coeff 0 + 2) = 0 := by linear_combination hroot
        rcases mul_eq_zero.1 h2 with h | h
        · exact Or.inl (by linarith)
        · exact Or.inr (by linarith)
      rw [hX]
      rcases hc with hc | hc
      · rw [hc, P8Orb.mirror_X_add_C]
        exact Set.pair_comm _ _
      · rw [hc, map_neg, ← sub_eq_add_neg, P8Orb.mirror_X_sub_C]
    · rintro rfl
      refine ⟨⟨X - C 2, ⟨monic_X_sub_C 2, irreducible_of_degree_eq_one (degree_X_sub_C 2),
        hdvd2⟩, P8Orb.not_even_X_sub_C 2, by rw [P8Orb.mirror_X_sub_C]⟩, fun f hf => ?_⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hf
      rcases hf with rfl | rfl
      · exact natDegree_X_sub_C 2
      · exact natDegree_X_add_C 2
  unfold NI
  rw [hset, Set.ncard_singleton]

theorem test_NI_22 : NI {2, 2} = 1 := by
  rw [NI_of_secular_eq (by decide) test_secular_22]
  have : {q : ℕ | 1 ≤ q ∧ (q : ℤ) ^ 2 = 4} = {2} := by
    ext q
    simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
    rw [show (4 : ℤ) = ((2 : ℕ) : ℤ) ^ 2 by norm_num, natCast_sq_eq_sq]
    constructor
    · exact fun h => h.2
    · rintro rfl
      exact ⟨by norm_num, rfl⟩
  rw [this, Set.ncard_singleton]

-- `Sharp_T15`: the integer pair of `T(15)` is the only one
theorem test_NI_15 : NI {15} = 1 := by
  rw [NI_of_secular_eq (by decide) test_secular_15]
  have : {q : ℕ | 1 ≤ q ∧ (q : ℤ) ^ 2 = 16} = {4} := by
    ext q
    simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
    rw [show (16 : ℤ) = ((4 : ℕ) : ℤ) ^ 2 by norm_num, natCast_sq_eq_sq]
    constructor
    · exact fun h => h.2
    · rintro rfl
      exact ⟨by norm_num, rfl⟩
  rw [this, Set.ncard_singleton]

-- review T3: "N_I {2,0,0} = 2" (`R = (t - 1)(t - 4)`: the integer pairs `x ∓ 1`, `x ∓ 2`)
theorem test_NI_200 : NI {2, 0, 0} = 2 := by
  rw [NI_eq' _ (by decide), test_secular_200]
  have : {q : ℕ | 1 ≤ q ∧ ((X - C 1) * (X - C 4) : ℤ[X]).eval ((q : ℤ) ^ 2) = 0} = {1, 2} := by
    ext q
    simp only [eval_mul, eval_sub, eval_X, eval_C, Set.mem_ofPred_eq, Set.mem_insert_iff,
      Set.mem_singleton_iff, mul_eq_zero, sub_eq_zero]
    rw [show (1 : ℤ) = ((1 : ℕ) : ℤ) ^ 2 by norm_num, show (4 : ℤ) = ((2 : ℕ) : ℤ) ^ 2 by norm_num,
      natCast_sq_eq_sq, natCast_sq_eq_sq]
    constructor
    · exact fun h => h.2
    · rintro (rfl | rfl)
      · exact ⟨le_rfl, Or.inl rfl⟩
      · exact ⟨by norm_num, Or.inr rfl⟩
  rw [this, Set.ncard_pair (by norm_num)]

-- review T3, "one multiset with N_II = 0 and N_I = 0": `(5)` (`R = t - 6`); also `(2)`
theorem test_NI_5 : NI {5} = 0 := by
  rw [NI_of_secular_eq (by decide) test_secular_5]
  have : {q : ℕ | 1 ≤ q ∧ (q : ℤ) ^ 2 = 6} = ∅ := by
    ext q
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and]
    exact fun _ => int_sq_ne not_isSquare_6 q
  rw [this, Set.ncard_empty]

theorem test_NI_2 : NI {2} = 0 := by
  rw [NI_of_secular_eq (by decide) test_secular_2]
  have : {q : ℕ | 1 ≤ q ∧ (q : ℤ) ^ 2 = 3} = ∅ := by
    ext q
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and]
    exact fun _ => int_sq_ne not_isSquare_3 q
  rw [this, Set.ncard_empty]

-- `T(3,0,0,0)`: `R(q²) = q⁴ - 7q² + 9 ≠ 0` (else `(2q² - 7)² = 13`)
theorem test_NI_3000 : NI {3, 0, 0, 0} = 0 := by
  rw [NI_eq' _ (by decide), test_secular_3000]
  have : {q : ℕ | 1 ≤ q ∧ (X ^ 2 - C 7 * X + C 9 : ℤ[X]).eval ((q : ℤ) ^ 2) = 0} = ∅ := by
    ext q
    simp only [eval_add, eval_sub, eval_mul, eval_pow, eval_X, eval_C, Set.mem_ofPred_eq,
      Set.mem_empty_iff_false, iff_false, not_and]
    intro _ h
    exact int_sq_ne not_isSquare_13 (2 * (q : ℤ) ^ 2 - 7) (by linear_combination 4 * h)
  rw [this, Set.ncard_empty]

-- `T(2,0)`: `R(q²) = q⁴ - 4q² + 2 ≠ 0` (else `(q² - 2)² = 2`)
theorem test_NI_20 : NI {2, 0} = 0 := by
  rw [NI_eq' _ (by decide), test_secular_20]
  have : {q : ℕ | 1 ≤ q ∧ (X ^ 2 - C 4 * X + C 2 : ℤ[X]).eval ((q : ℤ) ^ 2) = 0} = ∅ := by
    ext q
    simp only [eval_add, eval_sub, eval_mul, eval_pow, eval_X, eval_C, Set.mem_ofPred_eq,
      Set.mem_empty_iff_false, iff_false, not_and]
    intro _ h
    exact int_sq_ne not_isSquare_2 ((q : ℤ) ^ 2 - 2) (by linear_combination h)
  rw [this, Set.ncard_empty]

/-! ## `NII`: the number of irrational pairs -/

theorem two_NII_add_Nrat (m : Multiset ℕ) (hm : m ≠ 0) :
    2 * NII m + {z : ℤ | (secular m).eval z = 0}.ncard ≤ (Bset m).card :=
  P8Orb.two_NII_add_Nrat_le P8Orb.secularMonic m hm

theorem NII_eq_zero_of_card_le_one {m : Multiset ℕ} (hm : m ≠ 0) (h : (Bset m).card ≤ 1) :
    NII m = 0 := by
  have := two_NII_add_Nrat m hm
  omega

theorem test_NII_3 : NII {3} = 0 := NII_eq_zero_of_card_le_one (by decide) (by decide)
theorem test_NII_22 : NII {2, 2} = 0 := NII_eq_zero_of_card_le_one (by decide) (by decide)
theorem test_NII_15 : NII {15} = 0 := NII_eq_zero_of_card_le_one (by decide) (by decide)
theorem test_NII_5 : NII {5} = 0 := NII_eq_zero_of_card_le_one (by decide) (by decide)
theorem test_NII_2 : NII {2} = 0 := NII_eq_zero_of_card_le_one (by decide) (by decide)
theorem test_NII_1 : NII {1} = 0 := NII_eq_zero_of_card_le_one (by decide) (by decide)

-- `T(2,0,0)`: `r = 2` and `R` has the two integer roots `1`, `4`, so `N_II = 0`
theorem test_NII_200 : NII {2, 0, 0} = 0 := by
  have h := two_NII_add_Nrat {2, 0, 0} (by decide)
  have hsub : ({1, 4} : Set ℤ) ⊆ {z : ℤ | (secular {2, 0, 0}).eval z = 0} := by
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl
    · show (secular {2, 0, 0}).eval 1 = 0
      rw [test_secular_200]
      simp
    · show (secular {2, 0, 0}).eval 4 = 0
      rw [test_secular_200]
      simp
  have h2 := Set.ncard_le_ncard hsub (P8Orb.intRoots_finite _)
  rw [Set.ncard_pair (by norm_num)] at h2
  have hB : (Bset {2, 0, 0}).card = 2 := by decide
  omega

-- `T(2,0)`: `|R(0)| = 2` is not a square, so `2 N_II < r = 2`
theorem test_NII_20 : NII {2, 0} = 0 := by
  have h := P8Orb.two_NII_lt_of_not_isSquare P8Orb.secularMonic {2, 0} (by decide)
    (by rw [test_secular_20]; simpa using not_isSquare_2)
  have hB : (Bset {2, 0}).card = 2 := by decide
  omega

-- review T3: "N_II {3,0,0,0} = 1 (pair x² ∓ x - 3)"
theorem test_NII_3000 : NII {3, 0, 0, 0} = 1 := by
  have h := two_NII_add_Nrat {3, 0, 0, 0} (by decide)
  have hB : (Bset {3, 0, 0, 0}).card = 2 := by decide
  have hfin : {P ∈ nonEvenPairs {3, 0, 0, 0} | ∀ f ∈ P, f.natDegree ≠ 1}.Finite :=
    (P8Orb.orbit_count P8Orb.secularMonic _ (by decide)).1.subset (fun P hP => hP.1)
  have hmem : ({X ^ 2 - X - C 3, X ^ 2 + X - C 3} : Set ℚ[X]) ∈
      {P ∈ nonEvenPairs {3, 0, 0, 0} | ∀ f ∈ P, f.natDegree ≠ 1} := by
    refine ⟨test_pair_3000, fun f hf => ?_⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hf
    rcases hf with rfl | rfl
    · rw [natDegree_3000]
      norm_num
    · rw [← test_mirror_3000, P8Orb.natDegree_mirror, natDegree_3000]
      norm_num
  have h1 : 0 < NII {3, 0, 0, 0} := by
    unfold NII
    exact (Set.ncard_pos hfin).2 ⟨_, hmem⟩
  omega

-- review v2 on `Sharp_T18`: `T(18,0,0)` has one irrational pair and no integer pair: `N_I = 0`
-- (`R(q²) = q⁴ - 21q² + 36 ≠ 0`, else `(2q² - 21)² = 297`) and `N_II = 1`
theorem test_NI_1800 : NI {18, 0, 0} = 0 := by
  rw [NI_eq' _ (by decide), test_secular_1800]
  have : {q : ℕ | 1 ≤ q ∧ (X ^ 2 - C 21 * X + C 36 : ℤ[X]).eval ((q : ℤ) ^ 2) = 0} = ∅ := by
    ext q
    simp only [eval_add, eval_sub, eval_mul, eval_pow, eval_X, eval_C, Set.mem_ofPred_eq,
      Set.mem_empty_iff_false, iff_false, not_and]
    intro _ h
    exact int_sq_ne (not_isSquare_of_lt (z := 297) (r := 17) (by norm_num) (by norm_num)
      (by norm_num)) (2 * (q : ℤ) ^ 2 - 21) (by linear_combination 4 * h)
  rw [this, Set.ncard_empty]

theorem test_NII_1800 : NII {18, 0, 0} = 1 := by
  have h := two_NII_add_Nrat {18, 0, 0} (by decide)
  have hB : (Bset {18, 0, 0}).card = 2 := by decide
  have hfin : {P ∈ nonEvenPairs {18, 0, 0} | ∀ f ∈ P, f.natDegree ≠ 1}.Finite :=
    (P8Orb.orbit_count P8Orb.secularMonic _ (by decide)).1.subset (fun P hP => hP.1)
  have hmem : ({X ^ 2 + C 3 * X - C 6, X ^ 2 - C 3 * X - C 6} : Set ℚ[X]) ∈
      {P ∈ nonEvenPairs {18, 0, 0} | ∀ f ∈ P, f.natDegree ≠ 1} := by
    refine ⟨test_pair_18, fun f hf => ?_⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hf
    rcases hf with rfl | rfl
    · exact test_natDegree_18
    · have hd : (X ^ 2 - C 3 * X - C 6 : ℚ[X]).natDegree = 2 := by compute_degree!
      omega
  have h1 : 0 < NII {18, 0, 0} := by
    unfold NII
    exact (Set.ncard_pos hfin).2 ⟨_, hmem⟩
  omega

-- review T3: "one multiset with N_II = 0 and N_I = 0": `(5)`
theorem test_NI_NII_5 : NI {5} = 0 ∧ NII {5} = 0 := ⟨test_NI_5, test_NII_5⟩

-- FALSE instance: `(3,0,0,0)` has a non-even pair, but no integer pair
theorem test_NI_ne_NII_3000 : NI {3, 0, 0, 0} ≠ NII {3, 0, 0, 0} := by
  rw [test_NI_3000, test_NII_3000]
  norm_num

/-! ## `Nei`: even integer roots of `R` that are not squares -/

-- review T3: "N_ei {5} = 1 (R = t - 6)"
theorem test_Nei_5 : Nei {5} = 1 := by
  unfold Nei
  rw [test_secular_5]
  have : {z : ℤ | (X - C 6 : ℤ[X]).eval z = 0 ∧ Even z ∧ ¬ IsSquare z} = {6} := by
    ext z
    simp only [eval_sub, eval_X, eval_C, sub_eq_zero, Set.mem_ofPred_eq, Set.mem_singleton_iff]
    constructor
    · exact fun h => h.1
    · rintro rfl
      exact ⟨rfl, by decide, not_isSquare_6⟩
  rw [this, Set.ncard_singleton]

-- review T3: "N_ei {1} = 1 (R = t - 2)"
theorem test_Nei_1 : Nei {1} = 1 := by
  unfold Nei
  rw [test_secular_1]
  have : {z : ℤ | (X - C 2 : ℤ[X]).eval z = 0 ∧ Even z ∧ ¬ IsSquare z} = {2} := by
    ext z
    simp only [eval_sub, eval_X, eval_C, sub_eq_zero, Set.mem_ofPred_eq, Set.mem_singleton_iff]
    constructor
    · exact fun h => h.1
    · rintro rfl
      exact ⟨rfl, by decide, not_isSquare_2⟩
  rw [this, Set.ncard_singleton]

-- FALSE instances: the root `4` of `R = t - 4` (`(3)`, `(2,2)`) is a square, the root `3` of
-- `R = t - 3` (`(2)`) is odd
theorem test_Nei_3 : Nei {3} = 0 := by
  unfold Nei
  rw [test_secular_3]
  have : {z : ℤ | (X - C 4 : ℤ[X]).eval z = 0 ∧ Even z ∧ ¬ IsSquare z} = ∅ := by
    ext z
    simp only [eval_sub, eval_X, eval_C, sub_eq_zero, Set.mem_ofPred_eq, Set.mem_empty_iff_false,
      iff_false, not_and]
    rintro rfl _ h
    exact h ⟨2, by norm_num⟩
  rw [this, Set.ncard_empty]

theorem test_Nei_22 : Nei {2, 2} = 0 := by
  unfold Nei
  rw [test_secular_22]
  have : {z : ℤ | (X - C 4 : ℤ[X]).eval z = 0 ∧ Even z ∧ ¬ IsSquare z} = ∅ := by
    ext z
    simp only [eval_sub, eval_X, eval_C, sub_eq_zero, Set.mem_ofPred_eq, Set.mem_empty_iff_false,
      iff_false, not_and]
    rintro rfl _ h
    exact h ⟨2, by norm_num⟩
  rw [this, Set.ncard_empty]

theorem test_Nei_2 : Nei {2} = 0 := by
  unfold Nei
  rw [test_secular_2]
  have : {z : ℤ | (X - C 3 : ℤ[X]).eval z = 0 ∧ Even z ∧ ¬ IsSquare z} = ∅ := by
    ext z
    simp only [eval_sub, eval_X, eval_C, sub_eq_zero, Set.mem_ofPred_eq, Set.mem_empty_iff_false,
      iff_false, not_and]
    rintro rfl h
    exact absurd h (by decide)
  rw [this, Set.ncard_empty]

-- `T(2,0,0)`: the roots `1`, `4` of `R` are squares
theorem test_Nei_200 : Nei {2, 0, 0} = 0 := by
  unfold Nei
  rw [test_secular_200]
  have : {z : ℤ | ((X - C 1) * (X - C 4) : ℤ[X]).eval z = 0 ∧ Even z ∧ ¬ IsSquare z} = ∅ := by
    ext z
    simp only [eval_mul, eval_sub, eval_X, eval_C, mul_eq_zero, sub_eq_zero, Set.mem_ofPred_eq,
      Set.mem_empty_iff_false, iff_false, not_and]
    rintro (rfl | rfl) _ h
    · exact h ⟨1, by norm_num⟩
    · exact h ⟨2, by norm_num⟩
  rw [this, Set.ncard_empty]

-- `T(2,0)`: `R = t² - 4t + 2` has no integer root (else `(z - 2)² = 2`)
theorem test_Nei_20 : Nei {2, 0} = 0 := by
  unfold Nei
  rw [test_secular_20]
  have : {z : ℤ | (X ^ 2 - C 4 * X + C 2 : ℤ[X]).eval z = 0 ∧ Even z ∧ ¬ IsSquare z} = ∅ := by
    ext z
    simp only [eval_add, eval_sub, eval_mul, eval_pow, eval_X, eval_C, Set.mem_ofPred_eq,
      Set.mem_empty_iff_false, iff_false, not_and]
    intro h
    exact absurd (by linear_combination h) (int_sq_ne not_isSquare_2 (z - 2))
  rw [this, Set.ncard_empty]

-- `T(3,0,0,0)`: `R = t² - 7t + 9` has no integer root (else `(2z - 7)² = 13`)
theorem test_Nei_3000 : Nei {3, 0, 0, 0} = 0 := by
  unfold Nei
  rw [test_secular_3000]
  have : {z : ℤ | (X ^ 2 - C 7 * X + C 9 : ℤ[X]).eval z = 0 ∧ Even z ∧ ¬ IsSquare z} = ∅ := by
    ext z
    simp only [eval_add, eval_sub, eval_mul, eval_pow, eval_X, eval_C, Set.mem_ofPred_eq,
      Set.mem_empty_iff_false, iff_false, not_and]
    intro h
    exact absurd (by linear_combination 4 * h) (int_sq_ne not_isSquare_13 (2 * z - 7))
  rw [this, Set.ncard_empty]

-- Lemma 3.3(d), `N_I + 2 N_II + N_ei ≤ r`, is attained by `(3,0,0,0)`, `(2,0,0)` and `(1)`
theorem test_count_3000 :
    NI {3, 0, 0, 0} + 2 * NII {3, 0, 0, 0} + Nei {3, 0, 0, 0} = (Bset {3, 0, 0, 0}).card := by
  rw [test_NI_3000, test_NII_3000, test_Nei_3000]
  decide

theorem test_count_200 :
    NI {2, 0, 0} + 2 * NII {2, 0, 0} + Nei {2, 0, 0} = (Bset {2, 0, 0}).card := by
  rw [test_NI_200, test_NII_200, test_Nei_200]
  decide

theorem test_count_1 : NI {1} + 2 * NII {1} + Nei {1} = (Bset {1}).card := by
  rw [NI_of_secular_eq (by decide) test_secular_1, test_NII_1, test_Nei_1]
  have : {q : ℕ | 1 ≤ q ∧ (q : ℤ) ^ 2 = 2} = ∅ := by
    ext q
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and]
    exact fun _ => int_sq_ne not_isSquare_2 q
  rw [this, Set.ncard_empty]
  decide

end P8Tests
