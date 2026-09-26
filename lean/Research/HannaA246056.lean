import Mathlib.RingTheory.PowerSeries.Expand
import Mathlib.RingTheory.PowerSeries.Substitution
import Mathlib.Data.Nat.Choose.Lucas
import Mathlib.Data.Nat.Digits.Defs
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Tactic

set_option autoImplicit false

/-!
# OEIS A246056: the residues modulo 3 (Hanna's conjecture)

A246056 (Paul D. Hanna, Aug 23 2014), NAME:
"G.f.: Sum_{n>=0} x^n/(1-2*x)^(2*n+1) * [Sum_{k=0..n} C(n,k)^2 * 2^k*x^k] *
[Sum_{k=0..n} C(n,k)^2 * 3^k*x^k]."
Conjecture: `a(n) ≡ 1 (mod 3)` when `n = 2 * A005836(k)` (twice a number with no base-3 digit
`2`), and `a(n) ≡ 0 (mod 3)` otherwise.

We define `P r c = Σ_{k ≤ r} C(r,k)^2 c^k x^k` (so `P r c = P_r(c x)`),
`inv12 = 1/(1-2x)`, the `r`-th summand `T r = x^r P_r(2x) P_r(3x) / (1-2x)^(2r+1)` and
`a n = Σ_{r ≤ n} [x^n] T r`; `T_coeff_eq_zero` shows that the terms `r > n` do not contribute,
so `a n` is the `n`-th coefficient of the g.f.

Proof (modulo 3, in `(ZMod 3)[[x]]`):
1. `T r ↦ t r = x^r Q_r U^(2r+1)` with `Q_r = P_r(-x)`, `U = 1/(1+x)`.
2. Lucas: `Q_(3m+d) = Q_m(x^3) Q_d(x)` for `d < 3`.
3. Frobenius: `U^3 = U(x^3)`, `(1+x)^3 = 1+x^3`.
4. Hence `t_(3m+d) = t_m(x^3) (1+x^3) x^d Q_d U^(2d+1)`.
5. `(1+x^3) Σ_{d<3} x^d Q_d U^(2d+1) = 1+x^2`.
6. So `Σ_{r<3N} t_r = (1+x^2) Σ_{m<N} t_m(x^3)` (finite identity).
7. Coefficients: `f(3m) = f(m)`, `f(3m+1) = 0`, `f(3m+2) = f(m)`, `f(0) = 1`.
8. Digit induction.
-/

noncomputable section
namespace HannaA246056
open PowerSeries

/-! ## The sequence over `ℤ` -/

/-- `P r c = Σ_{k=0}^{r} C(r,k)^2 c^k x^k`, i.e. `P_r(c x)`. -/
def P (r : ℕ) (c : ℤ) : PowerSeries ℤ :=
  ∑ k ∈ Finset.range (r + 1), C ((r.choose k : ℤ) ^ 2 * c ^ k) * X ^ k

/-- `inv12 = Σ 2^k x^k = 1/(1-2x)`. -/
def inv12 : PowerSeries ℤ := PowerSeries.mk fun k => (2 : ℤ) ^ k

/-- `inv12` is the inverse of `1 - 2x`. -/
theorem inv12_spec : (1 - 2 * X) * inv12 = 1 := by
  ext k
  rcases k with _ | k
  · simp [inv12, coeff_one, two_mul, sub_mul, add_mul]
  · rw [two_mul, sub_mul, add_mul, one_mul, map_sub, map_add, coeff_succ_X_mul, inv12, coeff_mk,
      coeff_mk, coeff_one, if_neg (Nat.succ_ne_zero k), pow_succ]
    ring

/-- The `r`-th summand of the OEIS NAME: `x^r P_r(2x) P_r(3x) / (1-2x)^(2r+1)`. -/
def T (r : ℕ) : PowerSeries ℤ := X ^ r * P r 2 * P r 3 * inv12 ^ (2 * r + 1)

/-- `a(n)`: the `n`-th coefficient of `Σ_r T r` (only `r ≤ n` contribute, see
`T_coeff_eq_zero`). -/
def a (n : ℕ) : ℤ := ∑ r ∈ Finset.range (n + 1), coeff n (T r)

/-- `T r` has order at least `r`. -/
theorem T_coeff_eq_zero (n r : ℕ) (h : n < r) : coeff n (T r) = 0 := by
  rw [T, mul_assoc, mul_assoc, coeff_X_pow_mul', if_neg (by omega)]

/-- The truncation is harmless: `a n` is the `n`-th coefficient of `Σ_{r<M} T r` for every
`M > n`. -/
theorem a_eq_coeff_sum (n M : ℕ) (h : n < M) :
    a n = coeff n (∑ r ∈ Finset.range M, T r) := by
  obtain ⟨j, rfl⟩ : ∃ j, M = n + 1 + j := ⟨M - (n + 1), by omega⟩
  induction j with
  | zero => rw [a, map_sum]
  | succ j ih =>
    rw [← add_assoc, Finset.sum_range_succ, map_add, ← ih (by omega),
      T_coeff_eq_zero n _ (by omega), add_zero]

lemma P_eq_mk (r : ℕ) (c : ℤ) : P r c = PowerSeries.mk fun k => (r.choose k : ℤ) ^ 2 * c ^ k := by
  ext k
  rw [coeff_mk, P, map_sum]
  simp only [coeff_C_mul, coeff_X_pow, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq]
  split_ifs with h
  · rfl
  · rw [Finset.mem_range, not_lt] at h
    rw [Nat.choose_eq_zero_of_lt (by omega)]
    simp

lemma coeff_inv12 (k : ℕ) : coeff k inv12 = 2 ^ k := coeff_mk _ _

lemma constantCoeff_inv12 : constantCoeff inv12 = 1 := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_inv12, pow_zero]

/-- Sanity check of the definition against the OEIS data `1, 3, 16, 99, ...`. -/
theorem a_initial : a 0 = 1 ∧ a 1 = 3 ∧ a 2 = 16 ∧ a 3 = 99 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  simp [a, T, P_eq_mk, Finset.sum_range_succ, coeff_mul, Finset.Nat.antidiagonal_succ, pow_succ,
    coeff_inv12, constantCoeff_inv12, coeff_X_pow]

/-! ## Reduction modulo 3 -/

local notation "K" => ZMod 3

lemma three_eq_zero : (3 : PowerSeries K) = 0 := by
  simpa only [map_ofNat, map_zero] using
    congrArg (C : K →+* PowerSeries K) (show (3 : K) = 0 by decide)

/-- The image of `inv12`: `U = Σ (-1)^k x^k = 1/(1+x)`. -/
def U : PowerSeries K := PowerSeries.mk fun k => (-1 : K) ^ k

/-- The image of `P r 2`: `Q r = P_r(-x)`. -/
def Q (r : ℕ) : PowerSeries K := PowerSeries.mk fun k => (r.choose k : K) ^ 2 * (-1) ^ k

/-- The image of `T r`. -/
def t (r : ℕ) : PowerSeries K := X ^ r * Q r * U ^ (2 * r + 1)

lemma coeff_Q (r k : ℕ) : coeff k (Q r) = (r.choose k : K) ^ 2 * (-1) ^ k := coeff_mk _ _

lemma map_P_two (r : ℕ) : PowerSeries.map (Int.castRingHom K) (P r 2) = Q r := by
  ext k
  rw [P_eq_mk, coeff_map, coeff_mk, coeff_Q, eq_intCast]
  push_cast
  rw [show (2 : K) = -1 by decide]

lemma map_P_three (r : ℕ) : PowerSeries.map (Int.castRingHom K) (P r 3) = 1 := by
  ext k
  rw [P_eq_mk, coeff_map, coeff_mk, coeff_one, eq_intCast]
  push_cast
  rw [show (3 : K) = 0 by decide]
  rcases k with _ | k
  · simp
  · simp

lemma map_inv12 : PowerSeries.map (Int.castRingHom K) inv12 = U := by
  ext k
  rw [inv12, coeff_map, coeff_mk, U, coeff_mk, eq_intCast]
  push_cast
  rw [show (2 : K) = -1 by decide]

lemma map_T (r : ℕ) : PowerSeries.map (Int.castRingHom K) (T r) = t r := by
  rw [T, t, map_mul, map_mul, map_mul, map_pow, map_pow, map_X, map_P_two, map_P_three,
    map_inv12, mul_one]

/-! ## Step 3: `U = 1/(1+x)` and Frobenius -/

lemma U_mul : (1 + X) * U = 1 := by
  ext k
  rcases k with _ | k
  · rw [add_mul, one_mul, map_add, coeff_zero_X_mul, U, coeff_mk, coeff_one]
    simp
  · rw [add_mul, one_mul, map_add, coeff_succ_X_mul, U, coeff_mk, coeff_mk, coeff_one,
      if_neg (Nat.succ_ne_zero k), pow_succ]
    ring

/-- Frobenius in `(ZMod 3)[[X]]`: cubing is the substitution `X ↦ X^3`. -/
lemma cube_eq_expand (F : PowerSeries K) : F ^ 3 = expand 3 three_ne_zero F := by
  have h := MvPowerSeries.map_frobenius_expand (R := K) (σ := Unit) 3 three_ne_zero (f := F)
  rw [ZMod.frobenius_zmod] at h
  rw [← h]
  simp [MvPowerSeries.map_id]
  rfl

lemma one_add_X_cube : (1 + X : PowerSeries K) ^ 3 = 1 + X ^ 3 := by
  rw [cube_eq_expand, map_add, map_one, expand_X]

/-! ## Step 2: Lucas -/

lemma choose_lucas (m d k : ℕ) (hd : d < 3) :
    ((3 * m + d).choose k : K) = (d.choose (k % 3) : K) * (m.choose (k / 3) : K) := by
  have h := Choose.choose_modEq_choose_mod_mul_choose_div (n := 3 * m + d) (k := k) (p := 3)
  rw [show (3 * m + d) % 3 = d by omega, show (3 * m + d) / 3 = m by omega] at h
  have h' := (ZMod.intCast_eq_intCast_iff _ _ 3).mpr h
  push_cast at h'
  exact h'

/-- If `B` has degree `< 3`, then `[x^k] (A(x^3) B(x)) = [x^(k/3)] A * [x^(k%3)] B`. -/
lemma coeff_expand_mul_of_lt (A B : PowerSeries K) (hB : ∀ j, 3 ≤ j → coeff j B = 0) (k : ℕ) :
    coeff k (expand 3 three_ne_zero A * B) = coeff (k / 3) A * coeff (k % 3) B := by
  rw [coeff_mul, Finset.sum_eq_single (3 * (k / 3), k % 3)]
  · dsimp only
    rw [coeff_expand_mul]
  · rintro ⟨i, j⟩ hij hne
    rw [Finset.mem_antidiagonal] at hij
    dsimp only at hij ⊢
    by_cases hj : 3 ≤ j
    · rw [hB j hj, mul_zero]
    · rw [coeff_expand, if_neg, zero_mul]
      rintro ⟨q, rfl⟩
      apply hne
      rw [Prod.mk.injEq]
      omega
  · intro h
    exfalso
    apply h
    rw [Finset.mem_antidiagonal]
    dsimp only
    omega

lemma Q_lucas (m d : ℕ) (hd : d < 3) : Q (3 * m + d) = expand 3 three_ne_zero (Q m) * Q d := by
  ext k
  rw [coeff_expand_mul_of_lt (Q m) (Q d) ?_ k, coeff_Q, coeff_Q, coeff_Q, choose_lucas m d k hd]
  · have hk : (-1 : K) ^ k = (-1) ^ (k / 3) * (-1) ^ (k % 3) := by
      conv_lhs => rw [← Nat.div_add_mod k 3]
      rw [pow_add, pow_mul]
      norm_num
    rw [hk]
    ring
  · intro j hj
    rw [coeff_Q, Nat.choose_eq_zero_of_lt (by omega : d < j)]
    simp

lemma Q_zero : Q 0 = 1 := by
  ext k
  rw [coeff_Q, coeff_one]
  rcases k with _ | k
  · simp
  · simp

lemma Q_one : Q 1 = 1 - X := by
  ext k
  rw [coeff_Q, map_sub, coeff_one, coeff_X]
  rcases k with _ | _ | k
  · simp
  · simp
  · rw [Nat.choose_eq_zero_of_lt (by omega)]
    simp

lemma Q_two : Q 2 = 1 - X + X ^ 2 := by
  ext k
  rw [coeff_Q, map_add, map_sub, coeff_one, coeff_X, coeff_X_pow]
  rcases k with _ | _ | _ | k
  · simp
  · simp
    decide
  · simp
  · rw [Nat.choose_eq_zero_of_lt (by omega)]
    simp

/-! ## Steps 4 and 5 -/

/-- Step 4: the term `t (3m+d)` factors through `t m (x^3)`. -/
lemma t_block (m d : ℕ) (hd : d < 3) :
    t (3 * m + d) =
      expand 3 three_ne_zero (t m) * (1 + X ^ 3) * (X ^ d * Q d * U ^ (2 * d + 1)) := by
  have hU := U_mul
  have hE : expand 3 three_ne_zero U = U ^ 3 := (cube_eq_expand U).symm
  simp only [t]
  rw [Q_lucas m d hd]
  simp only [map_mul, map_pow, expand_X, hE]
  rw [← one_add_X_cube]
  linear_combination (-(X ^ 3) ^ m * X ^ d * expand 3 three_ne_zero (Q m) * Q d * U ^ (6 * m) *
    U ^ (2 * d + 1) * (((1 + X) * U) ^ 2 + (1 + X) * U + 1)) * hU

/-- Step 5: `(1+x^3) Σ_{d<3} x^d Q_d U^(2d+1) = 1 + x^2`. -/
lemma S_identity :
    (1 + X ^ 3 : PowerSeries K) * (X ^ 0 * Q 0 * U ^ (2 * 0 + 1) + X ^ 1 * Q 1 * U ^ (2 * 1 + 1) +
      X ^ 2 * Q 2 * U ^ (2 * 2 + 1)) = 1 + X ^ 2 := by
  rw [Q_zero, Q_one, Q_two, ← one_add_X_cube]
  have hU := U_mul
  have h3 := three_eq_zero
  linear_combination ((1 + X) ^ 2 + X * (1 - X) * (((1 + X) * U) ^ 2 + (1 + X) * U + 1) +
    X ^ 2 * (((1 + X) * U) ^ 4 + ((1 + X) * U) ^ 3 + ((1 + X) * U) ^ 2 + (1 + X) * U + 1)) * hU +
    (X - X ^ 3 * U ^ 2 * ((1 + X) * U) ^ 3) * h3

/-! ## Step 6: the finite identity -/

theorem sum_t (N : ℕ) : ∑ r ∈ Finset.range (3 * N), t r =
    (1 + X ^ 2) * expand 3 three_ne_zero (∑ m ∈ Finset.range N, t m) := by
  induction N with
  | zero => simp
  | succ N ih =>
    have h0 : t (3 * N) = expand 3 three_ne_zero (t N) * (1 + X ^ 3) *
        (X ^ 0 * Q 0 * U ^ (2 * 0 + 1)) := t_block N 0 (by norm_num)
    have h1 : t (3 * N + 1) = expand 3 three_ne_zero (t N) * (1 + X ^ 3) *
        (X ^ 1 * Q 1 * U ^ (2 * 1 + 1)) := t_block N 1 (by norm_num)
    have h2 : t (3 * N + 1 + 1) = expand 3 three_ne_zero (t N) * (1 + X ^ 3) *
        (X ^ 2 * Q 2 * U ^ (2 * 2 + 1)) := t_block N 2 (by norm_num)
    rw [show 3 * (N + 1) = 3 * N + 1 + 1 + 1 by ring, Finset.sum_range_succ,
      Finset.sum_range_succ, Finset.sum_range_succ, ih, Finset.sum_range_succ, map_add, h0, h1, h2]
    linear_combination expand 3 three_ne_zero (t N) * S_identity

/-! ## Step 7: the coefficient recursion -/

/-- `fa n` is `a(n)` modulo 3. -/
def fa (n : ℕ) : K := coeff n (∑ r ∈ Finset.range (n + 1), t r)

lemma coeff_t_eq_zero {n r : ℕ} (h : n < r) : coeff n (t r) = 0 := by
  rw [t, mul_assoc, coeff_X_pow_mul', if_neg (by omega)]

lemma fa_eq (n M : ℕ) (h : n < M) : coeff n (∑ r ∈ Finset.range M, t r) = fa n := by
  obtain ⟨j, rfl⟩ : ∃ j, M = n + 1 + j := ⟨M - (n + 1), by omega⟩
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [← add_assoc, Finset.sum_range_succ, map_add, ih (by omega),
      coeff_t_eq_zero (by omega), add_zero]

lemma a_cast (n : ℕ) : ((a n : ℤ) : K) = fa n := by
  rw [a, Int.cast_sum, fa, map_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [← map_T, coeff_map, eq_intCast]

lemma coeff_expand_sum (N j : ℕ) (h : j / 3 < N) :
    coeff j (expand 3 three_ne_zero (∑ m ∈ Finset.range N, t m)) =
      if 3 ∣ j then fa (j / 3) else 0 := by
  rw [coeff_expand]
  split_ifs
  · exact fa_eq _ _ h
  · rfl

lemma fa_rec (n : ℕ) : fa n = (if 3 ∣ n then fa (n / 3) else 0) +
    (if 2 ≤ n then (if 3 ∣ n - 2 then fa ((n - 2) / 3) else 0) else 0) := by
  have h := congrArg (coeff n) (sum_t (n + 1))
  rw [fa_eq n (3 * (n + 1)) (by omega), add_mul, one_mul, map_add, coeff_X_pow_mul',
    coeff_expand_sum (n + 1) n (by omega)] at h
  rw [h]
  congr 1
  by_cases h2 : 2 ≤ n
  · rw [if_pos h2, if_pos h2, coeff_expand_sum (n + 1) (n - 2) (by omega)]
  · rw [if_neg h2, if_neg h2]

lemma fa_zero : fa 0 = 1 := by
  simp [fa, t, Q_zero, U]

lemma fa_three_mul (m : ℕ) : fa (3 * m) = fa m := by
  rw [fa_rec (3 * m), if_pos (dvd_mul_right 3 m), Nat.mul_div_cancel_left m (by norm_num)]
  by_cases h2 : 2 ≤ 3 * m
  · rw [if_pos h2, if_neg (show ¬ 3 ∣ 3 * m - 2 by omega), add_zero]
  · rw [if_neg h2, add_zero]

lemma fa_three_mul_add_one (m : ℕ) : fa (3 * m + 1) = 0 := by
  rw [fa_rec (3 * m + 1), if_neg (show ¬ 3 ∣ 3 * m + 1 by omega), zero_add]
  by_cases h2 : 2 ≤ 3 * m + 1
  · rw [if_pos h2, if_neg (show ¬ 3 ∣ 3 * m + 1 - 2 by omega)]
  · rw [if_neg h2]

lemma fa_three_mul_add_two (m : ℕ) : fa (3 * m + 2) = fa m := by
  rw [fa_rec (3 * m + 2), if_neg (show ¬ 3 ∣ 3 * m + 2 by omega),
    if_pos (show 2 ≤ 3 * m + 2 by omega), if_pos (show 3 ∣ 3 * m + 2 - 2 by omega), zero_add,
    show (3 * m + 2 - 2) / 3 = m by omega]

/-! ## Step 8: base-3 digits -/

/-- `m` has no base-3 digit equal to `2`. -/
def NoTwo (m : ℕ) : Prop := ∀ d ∈ Nat.digits 3 m, d ≠ 2

/-- The conjectured support: `n = 2m` with `m` free of the digit `2`. -/
def Good (n : ℕ) : Prop := ∃ m, n = 2 * m ∧ NoTwo m

lemma noTwo_iff (q e : ℕ) (he : e < 3) : NoTwo (3 * q + e) ↔ e ≠ 2 ∧ NoTwo q := by
  by_cases h : e = 0 ∧ q = 0
  · obtain ⟨rfl, rfl⟩ := h
    simp [NoTwo]
  · have hd : Nat.digits 3 (e + 3 * q) = e :: Nat.digits 3 q :=
      Nat.digits_add 3 (by norm_num) e q he (by omega)
    unfold NoTwo
    rw [add_comm (3 * q) e, hd, List.forall_mem_cons]

lemma good_zero : Good 0 := ⟨0, rfl, by simp [NoTwo]⟩

lemma good_three_mul (q : ℕ) : Good (3 * q) ↔ Good q := by
  constructor
  · rintro ⟨m, hm, hno⟩
    have hm3 : m = 3 * (m / 3) + 0 := by omega
    rw [hm3, noTwo_iff _ _ (by norm_num)] at hno
    exact ⟨m / 3, by omega, hno.2⟩
  · rintro ⟨m, hm, hno⟩
    refine ⟨3 * m, by omega, ?_⟩
    have := (noTwo_iff m 0 (by norm_num)).mpr ⟨by norm_num, hno⟩
    simpa using this

lemma not_good_three_mul_add_one (q : ℕ) : ¬ Good (3 * q + 1) := by
  rintro ⟨m, hm, hno⟩
  have hm3 : m = 3 * (m / 3) + m % 3 := by omega
  rw [hm3, noTwo_iff _ _ (Nat.mod_lt _ (by norm_num))] at hno
  obtain ⟨h1, _⟩ := hno
  omega

lemma good_three_mul_add_two (q : ℕ) : Good (3 * q + 2) ↔ Good q := by
  constructor
  · rintro ⟨m, hm, hno⟩
    have hm3 : m = 3 * (m / 3) + m % 3 := by omega
    rw [hm3, noTwo_iff _ _ (Nat.mod_lt _ (by norm_num))] at hno
    obtain ⟨h1, h2⟩ := hno
    exact ⟨m / 3, by omega, h2⟩
  · rintro ⟨m, hm, hno⟩
    exact ⟨3 * m + 1, by omega, (noTwo_iff m 1 (by norm_num)).mpr ⟨by norm_num, hno⟩⟩

/-- `a(n) mod 3` is the indicator of `Good n`. -/
lemma fa_spec (n : ℕ) : (Good n → fa n = 1) ∧ (¬ Good n → fa n = 0) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hpos
    · exact ⟨fun _ => fa_zero, fun h => absurd good_zero h⟩
    obtain ⟨ih1, ih2⟩ := ih (n / 3) (Nat.div_lt_self hpos (by norm_num))
    rcases (by omega : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2) with h | h | h
    · rw [show n = 3 * (n / 3) by omega, fa_three_mul, good_three_mul]
      exact ⟨ih1, ih2⟩
    · rw [show n = 3 * (n / 3) + 1 by omega, fa_three_mul_add_one]
      exact ⟨fun hg => absurd hg (not_good_three_mul_add_one _), fun _ => rfl⟩
    · rw [show n = 3 * (n / 3) + 2 by omega, fa_three_mul_add_two, good_three_mul_add_two]
      exact ⟨ih1, ih2⟩

/-! ## Main theorems -/

/-- **A246056, residue 1.** If `n = 2m` and `m` has no base-3 digit `2`, then
`a(n) ≡ 1 (mod 3)`. -/
theorem hanna_a246056_one (n m : ℕ) (hn : n = 2 * m) (hm : ∀ d ∈ Nat.digits 3 m, d ≠ 2) :
    a n ≡ 1 [ZMOD 3] := by
  have h := (fa_spec n).1 ⟨m, hn, hm⟩
  rw [← a_cast] at h
  exact (ZMod.intCast_eq_intCast_iff (a n) 1 3).mp (by rw [h, Int.cast_one])

/-- **A246056, residue 0.** Otherwise `a(n) ≡ 0 (mod 3)`. -/
theorem hanna_a246056_zero (n : ℕ) (h : ¬ ∃ m, n = 2 * m ∧ ∀ d ∈ Nat.digits 3 m, d ≠ 2) :
    a n ≡ 0 [ZMOD 3] := by
  have h' := (fa_spec n).2 h
  rw [← a_cast] at h'
  exact (ZMod.intCast_eq_intCast_iff (a n) 0 3).mp (by rw [h', Int.cast_zero])

end HannaA246056

#print axioms HannaA246056.inv12_spec
#print axioms HannaA246056.T_coeff_eq_zero
#print axioms HannaA246056.a_eq_coeff_sum
#print axioms HannaA246056.hanna_a246056_one
#print axioms HannaA246056.hanna_a246056_zero
