import Mathlib.RingTheory.PowerSeries.Expand
import Mathlib.RingTheory.PowerSeries.Substitution
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Tactic

/-!
# OEIS A240998: the parity conjecture

A240998 (Paul D. Hanna, Aug 06 2014), NAME: "G.f. satisfies: A(x)^2 = x + A(x + 2*x^2)."
COMMENT: "For n>0, a(n) == 1 (mod 2) iff n=2^k for k>=0 (conjecture)."

We prove the congruence for *every* integer power series `A` satisfying the generating
equation (the OEIS sequence is the solution with `a(0) = 1`).  No hypothesis beyond the
functional equation is used.

Proof idea: reduce modulo 2.  Then `x + 2*x^2 ≡ x`, so the equation becomes
`F^2 = x + F`, and Frobenius gives `F^2 = F(x^2)`.  Comparing coefficients,
`f(n) = [n = 1] + [2 ∣ n] f(n/2)` for `n ≥ 1`, whose solution is the indicator of the
powers of two.
-/

noncomputable section
namespace HannaA240998
open PowerSeries

local notation "K" => ZMod 2

/-- Frobenius in `(ZMod 2)[[X]]`: squaring is the substitution `X ↦ X^2`. -/
lemma sq_eq_expand (F : PowerSeries K) : F ^ 2 = expand 2 two_ne_zero F := by
  have h := MvPowerSeries.map_frobenius_expand (R := K) (σ := Unit) 2 two_ne_zero (f := F)
  rw [ZMod.frobenius_zmod] at h
  rw [← h]
  simp [MvPowerSeries.map_id]
  rfl

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

/-- The statement in `(ZMod 2)[[X]]`: any solution of `F^2 = X + F` has
`coeff n F = 1` exactly at the powers of two (for `n ≥ 1`). -/
theorem residue (F : PowerSeries K) (hF : F ^ 2 = X + F) (n : ℕ) (hn : 1 ≤ n) :
    coeff n F = 1 ↔ ∃ k, n = 2 ^ k := by
  refine pow2_of_rec (fun n => coeff n F) ?_ n hn
  intro m _
  have h := congrArg (coeff m) hF
  rw [sq_eq_expand, coeff_expand, map_add, coeff_X] at h
  show coeff m F = (if m = 1 then 1 else 0) + (if 2 ∣ m then coeff (m / 2) F else 0)
  linear_combination -h - (if m = 1 then (1 : K) else 0) * two_eq_zero

/-- **A240998 parity conjecture.** For every integer power series `A` with
`A(x)^2 = x + A(x + 2x^2)` and every `n > 0`, `a(n)` is odd iff `n` is a power of two. -/
theorem hanna_a240998 (A : PowerSeries ℤ)
    (hA : A ^ 2 = X + A.subst (X + 2 * X ^ 2 : PowerSeries ℤ)) (n : ℕ) (hn : 0 < n) :
    Odd (coeff n A) ↔ ∃ k, n = 2 ^ k := by
  let f : ℤ →+* K := Int.castRingHom K
  have hs : HasSubst (X + 2 * X ^ 2 : PowerSeries ℤ) := by
    apply HasSubst.of_constantCoeff_zero'
    simp
  have h2 : (2 : PowerSeries K) = 0 := by
    simpa only [map_ofNat, map_zero] using congrArg (C : K →+* PowerSeries K) two_eq_zero
  have hX : (PowerSeries.map f) (X + 2 * X ^ 2 : PowerSeries ℤ) = X := by
    simp only [map_add, map_mul, map_pow, map_X, map_ofNat]
    rw [h2]
    ring
  have hsub : (PowerSeries.map f) (A.subst (X + 2 * X ^ 2 : PowerSeries ℤ)) = A.map f := by
    have h1 := map_subst hs (h := f) A
    have h3 : (A.map f).subst ((PowerSeries.map f) (X + 2 * X ^ 2 : PowerSeries ℤ)) =
        A.map f := by
      rw [hX, X_subst]
    exact h1.trans h3
  have hm : (A.map f) ^ 2 = X + A.map f := by
    have h4 := congrArg (PowerSeries.map f) hA
    rw [map_pow, map_add, map_X, hsub] at h4
    exact h4
  have hr := residue (A.map f) hm n hn
  rw [coeff_map] at hr
  rw [← ZMod.intCast_eq_one_iff_odd]
  exact hr

end HannaA240998

#print axioms HannaA240998.hanna_a240998
