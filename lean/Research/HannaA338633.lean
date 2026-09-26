import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.PowerSeries.Expand
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Tactic

/-!
# OEIS A338633 and A338634: parity of two continued-fraction series

A338633 (Paul D. Hanna, Nov 2020), offset 0, NAME:
"G.f. A(x) satisfies: 1 = A(x) - x/(A(x) - 2^3*x/(A(x) - 3^3*x/(A(x) - 4^3*x/(A(x) -
5^3*x/(A(x) - 6^3*x/(A(x) - ...)))))), a continued fraction relation."
A338634: the same with fourth powers `2^4, 3^4, 4^4, ...`.
Both entries: "For n > 0, a(n) is odd iff n is a power of 2 (conjecture)."

Formalization of the infinite continued fraction.  Write `T k` (`k = 0, 1, 2, ...`) for the
tail beginning with the partial numerator `(k+2)^e * x`, i.e.
`T k = A - (k+2)^e x / T (k+1)`, and `1 = A - x / T 0`.  All tails are power series with
invertible (unit) values, so the relations are equivalent to the cleared equations
`(A - 1) * T 0 = x` and `(A - T k) * T (k+1) = (k+2)^e * x`.  The theorem assumes a family of
unit tails satisfying all these relations (this is what the X-adically convergent continued
fraction provides); only the first two relations are used in the proof.

Proof: modulo 2 the second relation reads `(A - T 0) * T 1 = 2^e x = 0` with `T 1` a unit, so
`T 0 = A` and the first relation gives `(A - 1) A = x`.  With `B = A - 1` this is
`B + B^2 = x`, i.e. `B = x + B(x^2)`, whose coefficients are the indicator of the powers of 2.
-/

noncomputable section
namespace HannaA338633
open PowerSeries

local notation "K" => ZMod 2

/-- Frobenius in `(ZMod 2)[[X]]`: squaring is the substitution `X ↦ X^2`. -/
lemma sq_eq_expand (F : PowerSeries K) : F ^ 2 = expand 2 two_ne_zero F := by
  have h := MvPowerSeries.map_frobenius_expand (R := K) (σ := Unit) 2 two_ne_zero (f := F)
  rw [ZMod.frobenius_zmod] at h
  rw [← h]
  simp [MvPowerSeries.map_id]
  rfl

lemma two_eq_zero' : (2 : PowerSeries K) = 0 := by
  simpa only [map_ofNat, map_zero] using
    congrArg (C : K →+* PowerSeries K) (show (2 : K) = 0 by decide)

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

/-- General statement: if `1 = A - x/T0` and `T0 = A - c x / T1` with `c` even and `T0, T1`
units, then `a(n)` is odd iff `n` is a power of two (for `n > 0`). -/
theorem parity_of_two_tails (A T0 T1 : PowerSeries ℤ) (c : ℤ) (hc : Even c)
    (hT0 : IsUnit T0) (hT1 : IsUnit T1)
    (h0 : (A - 1) * T0 = X) (h1 : (A - T0) * T1 = C c * X) (n : ℕ) (hn : 0 < n) :
    Odd (coeff n A) ↔ ∃ k, n = 2 ^ k := by
  let f : ℤ →+* K := Int.castRingHom K
  have hcK : f c = 0 := by
    obtain ⟨r, rfl⟩ := hc
    change ((r + r : ℤ) : K) = 0
    push_cast
    rw [← two_mul, show (2 : K) = 0 by decide, zero_mul]
  -- reduce both relations
  have e1 : (A.map f - 1) * T0.map f = X := by
    have h := congrArg (PowerSeries.map f) h0
    simpa only [map_mul, map_sub, map_one, map_X] using h
  have e2 : (A.map f - T0.map f) * T1.map f = 0 := by
    have h := congrArg (PowerSeries.map f) h1
    simp only [map_mul, map_sub, map_X] at h
    rw [h, show PowerSeries.map f (C c) = C (f c) from map_C f c, hcK, map_zero, zero_mul]
  have hu1 : IsUnit (T1.map f) := hT1.map (PowerSeries.map f)
  have hT : T0.map f = A.map f := by
    have h := (hu1.mul_left_eq_zero).mp e2
    exact (sub_eq_zero.mp h).symm
  rw [hT] at e1
  -- `B = A - 1` satisfies `B = X + B^2`
  set B := A.map f - 1 with hBdef
  have hB : B = X + B ^ 2 := by
    have hA : A.map f = B + 1 := by rw [hBdef]; ring
    rw [hA] at e1
    linear_combination -e1 + (B - X) * two_eq_zero'
  have ha0 : constantCoeff A = 1 := by
    have h := congrArg constantCoeff h0
    rw [map_mul, map_sub, map_one, constantCoeff_X] at h
    have hu : IsUnit (constantCoeff T0) := isUnit_iff_constantCoeff.mp hT0
    exact sub_eq_zero.mp ((hu.mul_left_eq_zero).mp h)
  have hB0 : constantCoeff B = 0 := by
    rw [hBdef, map_sub, map_one, ← coeff_zero_eq_constantCoeff_apply, coeff_map,
      coeff_zero_eq_constantCoeff_apply, ha0, map_one, sub_self]
  have hr := catalan_mod_two B hB0 hB n
  have hcoef : coeff n B = coeff n (A.map f) := by
    rw [hBdef, map_sub, coeff_one, if_neg (by omega), sub_zero]
  rw [hcoef, coeff_map] at hr
  rw [← ZMod.intCast_eq_one_iff_odd]
  exact hr

/-- **A338633.**  If `A` and unit tails `T k` satisfy the continued-fraction relations
`(A - 1) * T 0 = x` and `(A - T k) * T (k+1) = (k+2)^3 * x`, then for `n > 0`, `a(n)` is odd
iff `n` is a power of two. -/
theorem hanna_a338633 (A : PowerSeries ℤ) (T : ℕ → PowerSeries ℤ) (hT : ∀ k, IsUnit (T k))
    (h0 : (A - 1) * T 0 = X)
    (hk : ∀ k : ℕ, (A - T k) * T (k + 1) = C (((k : ℤ) + 2) ^ 3) * X)
    (n : ℕ) (hn : 0 < n) : Odd (coeff n A) ↔ ∃ k, n = 2 ^ k := by
  refine parity_of_two_tails A (T 0) (T 1) ((((0 : ℕ) : ℤ) + 2) ^ 3) ?_ (hT 0) (hT 1) h0 (hk 0) n hn
  exact ⟨4, by norm_num⟩

/-- **A338634.**  The same statement with fourth powers `(k+2)^4`. -/
theorem hanna_a338634 (A : PowerSeries ℤ) (T : ℕ → PowerSeries ℤ) (hT : ∀ k, IsUnit (T k))
    (h0 : (A - 1) * T 0 = X)
    (hk : ∀ k : ℕ, (A - T k) * T (k + 1) = C (((k : ℤ) + 2) ^ 4) * X)
    (n : ℕ) (hn : 0 < n) : Odd (coeff n A) ↔ ∃ k, n = 2 ^ k := by
  refine parity_of_two_tails A (T 0) (T 1) ((((0 : ℕ) : ℤ) + 2) ^ 4) ?_ (hT 0) (hT 1) h0 (hk 0) n hn
  exact ⟨8, by norm_num⟩

end HannaA338633

#print axioms HannaA338633.hanna_a338633
#print axioms HannaA338633.hanna_a338634
