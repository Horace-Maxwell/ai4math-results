import Mathlib.RingTheory.PowerSeries.Substitution
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-!
# OEIS A295762: the parity conjecture

A295762 (Paul D. Hanna, Dec 03 2017), NAME:
"G.f. A(x) satisfies:  A(x - 2*A(x^2))  =  x + A(x^2)."  (offset 1, so `a(0) = 0`)
COMMENT: "Odd terms seem to occur only at a(2^n) for n>=0 (conjecture)."

We prove the (stronger, two-sided) statement: for every integer power series `A` with zero
constant term satisfying the generating equation, and every `n ≥ 1`,
`a(n)` is odd iff `n` is a power of two.

Proof idea: modulo 2 the inner series `x - 2*A(x^2)` becomes `x`, so the equation becomes
`F = x + F(x^2)`, i.e. `f(n) = [n = 1] + [2 ∣ n] f(n/2)`, whose solution on the positive
integers is the indicator of the powers of two.
-/

noncomputable section
namespace HannaA295762
open PowerSeries

local notation "K" => ZMod 2

lemma two_eq_zero : (2 : K) = 0 := by decide

/-- The dyadic recursion `g n = [n = 1] + [2 ∣ n] g (n/2)` (for `n ≥ 1`) forces `g` to be
the indicator function of the powers of two on the positive integers. -/
lemma pow2_of_rec (g : ℕ → K)
    (hg : ∀ n, 1 ≤ n → g n = (if n = 1 then 1 else 0) + (if 2 ∣ n then g (n / 2) else 0)) :
    ∀ n, 1 ≤ n → (g n = 1 ↔ ∃ k, n = 2 ^ k) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    rcases Nat.even_or_odd' n with ⟨m, rfl | rfl⟩
    · have hm : 1 ≤ m := by omega
      rw [hg (2 * m) hn, if_neg (show ¬ 2 * m = 1 by omega), if_pos (dvd_mul_right 2 m),
        Nat.mul_div_cancel_left m two_pos, zero_add, ih m (by omega) hm]
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
    · rw [hg (2 * m + 1) hn, if_neg (show ¬ 2 ∣ 2 * m + 1 by omega)]
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

/-- The statement in `(ZMod 2)[[X]]`: any solution of `F = X + F(X^2)` has
`coeff n F = 1` exactly at the powers of two (for `n ≥ 1`). -/
theorem residue (F : PowerSeries K) (hF : F = X + F.subst (X ^ 2 : PowerSeries K))
    (n : ℕ) (hn : 1 ≤ n) : coeff n F = 1 ↔ ∃ k, n = 2 ^ k := by
  refine pow2_of_rec (fun n => coeff n F) ?_ n hn
  intro m _
  have h := congrArg (coeff m) hF
  rw [map_add, coeff_X, coeff_subst_X_pow two_ne_zero] at h
  simpa using h

/-- **A295762 parity conjecture** (both directions).  For every integer power series `A`
with `A(0) = 0` and `A(x - 2*A(x^2)) = x + A(x^2)`, and every `n > 0`,
`a(n)` is odd iff `n` is a power of two. -/
theorem hanna_a295762 (A : PowerSeries ℤ) (h0 : constantCoeff A = 0)
    (hA : A.subst (X - 2 * A.subst (X ^ 2 : PowerSeries ℤ) : PowerSeries ℤ) =
      X + A.subst (X ^ 2 : PowerSeries ℤ)) (n : ℕ) (hn : 0 < n) :
    Odd (coeff n A) ↔ ∃ k, n = 2 ^ k := by
  let f : ℤ →+* K := Int.castRingHom K
  have hs2 : HasSubst (X ^ 2 : PowerSeries ℤ) := HasSubst.X_pow two_ne_zero
  have hc : constantCoeff (A.subst (X ^ 2 : PowerSeries ℤ) : PowerSeries ℤ) = 0 := by
    rw [constantCoeff_subst_X_pow two_ne_zero, h0]
    simp
  have hs : HasSubst (X - 2 * A.subst (X ^ 2 : PowerSeries ℤ) : PowerSeries ℤ) := by
    apply HasSubst.of_constantCoeff_zero'
    rw [map_sub, map_mul, hc, constantCoeff_X]
    simp
  have h2 : (2 : PowerSeries K) = 0 := by
    simpa only [map_ofNat, map_zero] using congrArg (C : K →+* PowerSeries K) two_eq_zero
  -- reduction of the inner substitution `A(x^2)`
  have hsub2 : (PowerSeries.map f) (A.subst (X ^ 2 : PowerSeries ℤ)) =
      (A.map f).subst (X ^ 2 : PowerSeries K) := by
    have h1 := map_subst hs2 (h := f) A
    have h3 : (A.map f).subst ((PowerSeries.map f) (X ^ 2 : PowerSeries ℤ)) =
        (A.map f).subst (X ^ 2 : PowerSeries K) := by
      rw [map_pow, map_X]
    exact h1.trans h3
  -- reduction of the outer substitution
  have hX : (PowerSeries.map f) (X - 2 * A.subst (X ^ 2 : PowerSeries ℤ) : PowerSeries ℤ) = X := by
    rw [map_sub, map_mul, map_X, map_ofNat, h2, zero_mul, sub_zero]
  have hsub : (PowerSeries.map f) (A.subst (X - 2 * A.subst (X ^ 2 : PowerSeries ℤ) :
      PowerSeries ℤ)) = A.map f := by
    have h1 := map_subst hs (h := f) A
    have h3 : (A.map f).subst ((PowerSeries.map f)
        (X - 2 * A.subst (X ^ 2 : PowerSeries ℤ) : PowerSeries ℤ)) = A.map f := by
      rw [hX, X_subst]
    exact h1.trans h3
  have hm : A.map f = X + (A.map f).subst (X ^ 2 : PowerSeries K) := by
    have h4 := congrArg (PowerSeries.map f) hA
    rw [hsub, map_add, map_X, hsub2] at h4
    exact h4
  have hr := residue (A.map f) hm n hn
  rw [coeff_map] at hr
  rw [← ZMod.intCast_eq_one_iff_odd]
  exact hr

end HannaA295762

#print axioms HannaA295762.hanna_a295762
