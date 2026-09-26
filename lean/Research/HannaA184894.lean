import Mathlib.Algebra.Polynomial.Expand
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Tactic

/-!
# OEIS A184894: the mod-3 pattern, proved in one direction and refuted in the other

A184894 (Paul D. Hanna, Feb 01 2011), NAME:
"a(n) equals the coefficient of x^(2n-1) in the n-th iteration of x+x^3 for n>=1."
FORMULA: "Conjecture: a(m) = 0 (mod 3) everywhere except at m = (3^n+1)/2, n>=0."
(The example lists the "nonzero terms (mod 3)" a(1), a(2), a(5), a(14), a(41), a(122).)

Let `g = x + x^3` and `P m = g^{∘m}`.  Over `ZMod 3`, `P (m+1) = P m + (P m)^3` and
`(P m)^3 = expand 3 (P m)` (Frobenius), so the coefficients `c m k` satisfy
`c (m+1) k = c m k + [3 ∣ k] c m (k/3)`, `c 0 k = [k = 1]`.  Hence
* `c m k = 0` unless `k` is a power of 3, and
* `c m (3^j) = C(m, j) mod 3`.

Consequences (all proved below):
1. `3 ∣ a(m)` whenever `2m - 1` is not a power of 3 (the "zero" part of the conjecture);
2. `a((3^j+1)/2) ≡ C((3^j+1)/2, j) (mod 3)` (complete description);
3. `3 ∣ a(365)` although `365 = (3^6+1)/2`: the claimed non-vanishing at `m = (3^n+1)/2`
   fails at `n = 6` (because `C(365, 6) = 3151277509380 ≡ 0 (mod 3)`).
-/

noncomputable section
namespace HannaA184894
open Polynomial

/-- The `m`-th iterate of `x + x^3` over a commutative ring. -/
def iter (R : Type*) [CommRing R] (m : ℕ) : R[X] := (fun p : R[X] => (X + X ^ 3).comp p)^[m] X

/-- The OEIS sequence: the coefficient of `x^(2m-1)` in the `m`-th iterate. -/
def a (m : ℕ) : ℤ := (iter ℤ m).coeff (2 * m - 1)

lemma iter_succ (R : Type*) [CommRing R] (m : ℕ) :
    iter R (m + 1) = iter R m + (iter R m) ^ 3 := by
  rw [iter, Function.iterate_succ_apply', ← iter]
  simp [add_comp]

lemma map_iter (m : ℕ) : (iter ℤ m).map (Int.castRingHom (ZMod 3)) = iter (ZMod 3) m := by
  induction m with
  | zero => simp [iter]
  | succ m ih => rw [iter_succ, iter_succ, Polynomial.map_add, Polynomial.map_pow, ih]

local notation "K" => ZMod 3

/-- The coefficient recursion modulo 3. -/
lemma coeff_rec (m k : ℕ) : (iter K (m + 1)).coeff k =
    (iter K m).coeff k + (if 3 ∣ k then (iter K m).coeff (k / 3) else 0) := by
  rw [iter_succ, coeff_add, ← ZMod.expand_card, coeff_expand (by norm_num)]

lemma coeff_zero_iter (k : ℕ) : (iter K 0).coeff k = if k = 1 then 1 else 0 := by
  simp [iter, coeff_X, eq_comm]

/-- Coefficients at non-powers of 3 vanish modulo 3. -/
lemma coeff_nonpow (m : ℕ) : ∀ k, (∀ j, k ≠ 3 ^ j) → (iter K m).coeff k = 0 := by
  induction m with
  | zero =>
    intro k hk
    rw [coeff_zero_iter, if_neg (by simpa using hk 0)]
  | succ m ih =>
    intro k hk
    rw [coeff_rec, ih k hk, zero_add]
    split_ifs with h3
    · apply ih
      intro j hj
      apply hk (j + 1)
      obtain ⟨t, rfl⟩ := h3
      rw [Nat.mul_div_cancel_left t (by norm_num)] at hj
      rw [hj, pow_succ]; ring
    · rfl

/-- Coefficients at `3^j` are binomial coefficients modulo 3. -/
lemma coeff_pow (m : ℕ) : ∀ j, (iter K m).coeff (3 ^ j) = (m.choose j : K) := by
  induction m with
  | zero =>
    intro j
    rw [coeff_zero_iter]
    rcases j with _ | j
    · simp
    · have : 3 ^ (j + 1) ≠ 1 := by
        have := Nat.one_lt_pow (Nat.succ_ne_zero j) (by norm_num : 1 < 3)
        omega
      simp only [pow_succ] at this ⊢
      simp [this]
  | succ m ih =>
    intro j
    rw [coeff_rec, ih j]
    rcases j with _ | j
    · rw [if_neg (by norm_num), add_zero]; simp
    · rw [if_pos (dvd_pow_self 3 (Nat.succ_ne_zero j)),
        show 3 ^ (j + 1) / 3 = 3 ^ j by rw [pow_succ, Nat.mul_div_cancel _ (by norm_num)], ih j,
        Nat.choose_succ_succ', Nat.cast_add, add_comm]

lemma a_cast (m : ℕ) : ((a m : ℤ) : K) = (iter K m).coeff (2 * m - 1) := by
  rw [a, ← map_iter, coeff_map]
  rfl

/-- **Part 1 (the conjectured vanishing, proved).**  If `2m - 1` is not a power of 3 then
`3 ∣ a(m)`. -/
theorem zero_part (m : ℕ) (hm : ¬ ∃ j, 2 * m - 1 = 3 ^ j) : (3 : ℤ) ∣ a m := by
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).mp
  rw [a_cast]
  exact coeff_nonpow m _ (fun j hj => hm ⟨j, hj⟩)

/-- **Part 2 (complete description at the special indices).**  If `2m - 1 = 3^j` then
`a(m) ≡ C(m, j) (mod 3)`. -/
theorem value_at_pow (m j : ℕ) (h : 2 * m - 1 = 3 ^ j) :
    ((a m : ℤ) : K) = (m.choose j : K) := by
  rw [a_cast, h, coeff_pow]

lemma choose_365_6 : Nat.choose 365 6 = 3151277509380 := by
  rw [Nat.choose_eq_descFactorial_div_factorial]
  norm_num [Nat.descFactorial, Nat.factorial]

/-- **Part 3 (counterexample).**  `365 = (3^6 + 1)/2`, yet `3 ∣ a(365)`: the conjectured
non-vanishing modulo 3 at `m = (3^n+1)/2` fails for `n = 6`. -/
theorem counterexample : 2 * 365 - 1 = 3 ^ 6 ∧ (3 ^ 6 + 1) / 2 = 365 ∧ (3 : ℤ) ∣ a 365 := by
  refine ⟨by norm_num, by norm_num, ?_⟩
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).mp
  rw [value_at_pow 365 6 (by norm_num), choose_365_6, ZMod.natCast_eq_zero_iff]
  norm_num

end HannaA184894

#print axioms HannaA184894.zero_part
#print axioms HannaA184894.value_at_pow
#print axioms HannaA184894.counterexample
