import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.RingTheory.PowerSeries.Expand
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Tactic

/-!
# OEIS A301933: the parity conjecture

A301933 (Paul D. Hanna, Mar 28 2018), offset 1, NAME:
"G.f. A(x) satisfies: A(x) = x*(1 + 4*A(x)*A'(x)) / (1 + A(x)*A'(x))."
COMMENT: "a(n = 2^k) is odd for k>=0, and a(n) is even elsewhere (conjecture)."

Since `A(0) = 0` (offset 1), `1 + A*A'` has constant term `1`, so it is a unit and the
equation is equivalent to the cleared form `A * (1 + A*A') = x * (1 + 4*A*A')`, which we use
as the hypothesis.  We prove: for every integer power series `A` with `A(0) = 0` satisfying
it, `a(n)` is odd iff `n` is a power of two.

Proof: modulo 2 the equation is `F + F^2 F' = x`.  In characteristic 2 the second derivative
vanishes (`n(n-1)` is even), so differentiating gives `F' + 2FF'^2 + F^2 F'' = F' = 1`.
Hence `F + F^2 = x`, i.e. `F = x + F^2 = x + F(x^2)`, whose coefficients are the indicator of
the powers of two.
-/

noncomputable section
namespace HannaA301933
open PowerSeries

local notation "K" => ZMod 2
local notation "D" => PowerSeries.derivative (R := K)

/-- Frobenius in `(ZMod 2)[[X]]`: squaring is the substitution `X ↦ X^2`. -/
lemma sq_eq_expand (F : PowerSeries K) : F ^ 2 = expand 2 two_ne_zero F := by
  have h := MvPowerSeries.map_frobenius_expand (R := K) (σ := Unit) 2 two_ne_zero (f := F)
  rw [ZMod.frobenius_zmod] at h
  rw [← h]
  simp [MvPowerSeries.map_id]
  rfl

lemma two_eq_zero : (2 : K) = 0 := by decide

lemma two_eq_zero' : (2 : PowerSeries K) = 0 := by
  simpa only [map_ofNat, map_zero] using congrArg (C : K →+* PowerSeries K) two_eq_zero

/-- In characteristic two the second formal derivative vanishes. -/
lemma dd_eq_zero (F : PowerSeries K) : D (D F) = 0 := by
  ext n
  rw [coeff_derivative, coeff_derivative, map_zero]
  have h : (((n + 1) * (n + 1 + 1) : ℕ) : K) = 0 :=
    ZMod.natCast_eq_zero_iff_even.mpr (Nat.even_mul_succ_self (n + 1))
  push_cast at h ⊢
  linear_combination (coeff (n + 1 + 1) F) * h

/-- `c = X + c^2` with `c(0) = 0` forces `c` to be the indicator of the powers of two. -/
lemma catalan_mod_two (c : PowerSeries K) (hc0 : constantCoeff c = 0) (hc : c = X + c ^ 2) :
    ∀ n, coeff n c = 1 ↔ ∃ k, n = 2 ^ k := by
  have hrec : ∀ n, coeff n c = (if n = 1 then 1 else 0) +
      (if 2 ∣ n then coeff (n / 2) c else 0) := by
    intro n
    have h := congrArg (coeff n) hc
    rw [sq_eq_expand, map_add, coeff_X, coeff_expand] at h
    exact h
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.even_or_odd' n with ⟨m, rfl | rfl⟩
    · by_cases hm : m = 0
      · subst hm
        rw [Nat.mul_zero, coeff_zero_eq_constantCoeff_apply, hc0]
        constructor
        · intro h; exact absurd h (by decide)
        · rintro ⟨k, hk⟩
          have : 0 < 2 ^ k := pow_pos two_pos k
          omega
      · rw [hrec, if_neg (show ¬ 2 * m = 1 by omega), if_pos (dvd_mul_right 2 m),
          Nat.mul_div_cancel_left m two_pos, zero_add, ih m (by omega)]
        constructor
        · rintro ⟨k, rfl⟩
          exact ⟨k + 1, by ring⟩
        · rintro ⟨k, hk⟩
          cases k with
          | zero => rw [pow_zero] at hk; omega
          | succ k =>
            refine ⟨k, ?_⟩
            rw [pow_succ] at hk
            omega
    · rw [hrec, if_neg (show ¬ 2 ∣ 2 * m + 1 by omega)]
      by_cases hm : m = 0
      · subst hm
        refine ⟨fun _ => ⟨0, by norm_num⟩, fun _ => by norm_num⟩
      · rw [if_neg (show ¬ 2 * m + 1 = 1 by omega), add_zero]
        constructor
        · intro h
          exact absurd h (by decide)
        · rintro ⟨k, hk⟩
          cases k with
          | zero => rw [pow_zero] at hk; omega
          | succ k =>
            rw [pow_succ] at hk
            omega

/-- The reduced equation forces `F = X + F^2`. -/
theorem residue (F : PowerSeries K)
    (hF : F * (1 + F * D F) = X * (1 + 4 * F * D F)) : F = X + F ^ 2 := by
  have h4 : (4 : PowerSeries K) = 0 := by
    rw [show (4 : PowerSeries K) = 2 * 2 by norm_num, two_eq_zero', zero_mul]
  have e1 : F + F ^ 2 * D F = X := by
    rw [h4] at hF
    linear_combination hF
  have e2 := congrArg D e1
  rw [map_add, Derivation.leibniz, Derivation.leibniz_pow, dd_eq_zero, derivative_X] at e2
  simp only [smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat] at e2
  have hDF : D F = 1 := by
    linear_combination e2 - (D F * (F ^ (2 - 1) * D F)) * two_eq_zero'
  rw [hDF, mul_one] at e1
  linear_combination e1 - F ^ 2 * two_eq_zero'

/-- Formal differentiation commutes with reduction of coefficients. -/
lemma map_derivative (f : ℤ →+* K) (A : PowerSeries ℤ) :
    PowerSeries.map f (derivative (R := ℤ) A) = D (PowerSeries.map f A) := by
  ext n
  simp only [coeff_map, coeff_derivative, map_mul, map_add, map_natCast, map_one]

/-- **A301933 parity conjecture.**  For every integer power series `A` with `A(0) = 0` and
`A * (1 + A*A') = x * (1 + 4*A*A')` (the OEIS equation with the unit denominator cleared),
`a(n)` is odd iff `n` is a power of two. -/
theorem hanna_a301933 (A : PowerSeries ℤ) (h0 : constantCoeff A = 0)
    (hA : A * (1 + A * derivative (R := ℤ) A) = X * (1 + 4 * A * derivative (R := ℤ) A)) (n : ℕ) :
    Odd (coeff n A) ↔ ∃ k, n = 2 ^ k := by
  let f : ℤ →+* K := Int.castRingHom K
  have hm : A.map f * (1 + A.map f * D (A.map f)) = X * (1 + 4 * A.map f * D (A.map f)) := by
    have h := congrArg (PowerSeries.map f) hA
    simp only [map_mul, map_add, map_one, map_X, map_ofNat, map_derivative] at h
    exact h
  have hF := residue (A.map f) hm
  have hc0 : constantCoeff (A.map f) = 0 := by
    rw [← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff_apply, h0,
      map_zero]
  have hr := catalan_mod_two (A.map f) hc0 hF n
  rw [coeff_map] at hr
  rw [← ZMod.intCast_eq_one_iff_odd]
  exact hr

end HannaA301933

#print axioms HannaA301933.hanna_a301933
