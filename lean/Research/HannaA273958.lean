import Mathlib.RingTheory.PowerSeries.Expand
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Tactic

/-!
# OEIS A273958: the parity conjecture

A273958 (Paul D. Hanna, Jun 10 2016), NAME:
"G.f. A(x) satisfies: x*A(x) + x^2*A(x)^2 = C(x)^2, where C(x) = x + C(x)^2 is a g.f. of
the Catalan numbers (A000108)."  (offset 1)
COMMENT: "It appears that a(n) = 1 (mod 2) iff n = 2*4^k - 1 for k>=0."

We prove: for all integer power series `C, A` with `C = X + C^2` and
`X*A + X^2*A^2 = C^2`, and every `n`, `a(n)` is odd iff `n + 1 = 2*4^k` for some `k`.
(The equation forces `C(0) = 0` and `A(0) = 0`; the OEIS indexing starts at `n = 1`,
and `n = 0` is harmless since `a(0) = 0`.)

Proof idea: modulo 2, Frobenius gives `F^2 = F(x^2)`.  Then `c = x + c(x^2)` makes `c` the
indicator of powers of two, and `B = x*A` satisfies `B + B(x^2) = c(x^2)`, i.e.
`b(2m) = b(m) + c(m)` and `b(odd) = 0`, so `b` is the indicator of the odd powers of two.
-/

noncomputable section
namespace HannaA273958
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

/-! ### Elementary facts about powers of two and four -/

lemma pow2_iff (m : ℕ) :
    (∃ i, m = 2 ^ i) ↔ (∃ j, m = 4 ^ j) ∨ (∃ k, m = 2 * 4 ^ k) := by
  constructor
  · rintro ⟨i, rfl⟩
    rcases Nat.even_or_odd' i with ⟨j, rfl | rfl⟩
    · left; exact ⟨j, by rw [pow_mul]; norm_num⟩
    · right; exact ⟨j, by rw [pow_succ, pow_mul]; norm_num; ring⟩
  · rintro (⟨j, rfl⟩ | ⟨k, rfl⟩)
    · exact ⟨2 * j, by rw [pow_mul]; norm_num⟩
    · exact ⟨2 * k + 1, by rw [pow_succ, pow_mul]; norm_num; ring⟩

lemma not_four_and_twice (m : ℕ) : ¬ ((∃ j, m = 4 ^ j) ∧ (∃ k, m = 2 * 4 ^ k)) := by
  rintro ⟨⟨j, rfl⟩, ⟨k, hk⟩⟩
  have h1 : (4 : ℕ) ^ j = 2 ^ (2 * j) := by rw [pow_mul]; norm_num
  have h2 : 2 * (4 : ℕ) ^ k = 2 ^ (2 * k + 1) := by rw [pow_succ, pow_mul]; norm_num; ring
  rw [h1, h2] at hk
  have := Nat.pow_right_injective (le_refl 2) hk
  omega

lemma zmod2_add_eq_one (x y : K) : x + y = 1 ↔ ¬ (x = 1 ↔ y = 1) := by
  revert x y; decide

/-! ### The Catalan series modulo 2 -/

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

/-- `B + B^2 = c^2` with `B(0) = 0` and `c` the power-of-two indicator forces `B` to be the
indicator of the numbers `2 * 4^k`. -/
lemma shifted_mod_two (c B : PowerSeries K) (hc : ∀ n, coeff n c = 1 ↔ ∃ k, n = 2 ^ k)
    (hB0 : constantCoeff B = 0) (hB : B + B ^ 2 = c ^ 2) :
    ∀ n, coeff n B = 1 ↔ ∃ k, n = 2 * 4 ^ k := by
  have hrec : ∀ n, coeff n B + (if 2 ∣ n then coeff (n / 2) B else 0) =
      (if 2 ∣ n then coeff (n / 2) c else 0) := by
    intro n
    have h := congrArg (coeff n) hB
    rw [sq_eq_expand, sq_eq_expand, map_add, coeff_expand, coeff_expand] at h
    exact h
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.even_or_odd' n with ⟨m, rfl | rfl⟩
    · by_cases hm : m = 0
      · subst hm
        rw [Nat.mul_zero, coeff_zero_eq_constantCoeff_apply, hB0]
        constructor
        · intro h; exact absurd h (by decide)
        · rintro ⟨k, hk⟩
          have : 0 < 4 ^ k := pow_pos (by norm_num) k
          omega
      · have h := hrec (2 * m)
        rw [if_pos (dvd_mul_right 2 m), if_pos (dvd_mul_right 2 m),
          Nat.mul_div_cancel_left m two_pos] at h
        have hb : coeff (2 * m) B = coeff m c + coeff m B := by
          linear_combination h - (coeff m B) * two_eq_zero
        rw [hb, zmod2_add_eq_one, hc m, ih m (by omega)]
        have e1 : (∃ k, 2 * m = 2 * 4 ^ k) ↔ ∃ j, m = 4 ^ j := by
          constructor
          · rintro ⟨k, hk⟩; exact ⟨k, by omega⟩
          · rintro ⟨k, hk⟩; exact ⟨k, by omega⟩
        rw [e1, pow2_iff]
        have hx := not_four_and_twice m
        tauto
    · have h := hrec (2 * m + 1)
      rw [if_neg (show ¬ 2 ∣ 2 * m + 1 by omega), if_neg (show ¬ 2 ∣ 2 * m + 1 by omega),
        add_zero] at h
      rw [h]
      constructor
      · intro h1; exact absurd h1 (by decide)
      · rintro ⟨k, hk⟩
        omega

/-- **A273958 parity conjecture.**  For all integer power series `C, A` with `C = X + C^2`
(the Catalan equation) and `X*A + X^2*A^2 = C^2`, `a(n)` is odd iff `n = 2*4^k - 1`. -/
theorem hanna_a273958 (C A : PowerSeries ℤ) (hC : C = X + C ^ 2)
    (hA : X * A + X ^ 2 * A ^ 2 = C ^ 2) (n : ℕ) :
    Odd (coeff n A) ↔ ∃ k, n + 1 = 2 * 4 ^ k := by
  let f : ℤ →+* K := Int.castRingHom K
  -- the equation forces `C(0) = 0`
  have hC0 : constantCoeff C = 0 := by
    have h' : constantCoeff C ^ 2 = 0 := by
      rw [← map_pow, ← hA]
      simp
    exact pow_eq_zero_iff two_ne_zero |>.mp h'
  set c := C.map f with hcdef
  set a := A.map f with hadef
  have hc0 : constantCoeff c = 0 := by
    rw [hcdef, ← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff_apply,
      hC0, map_zero]
  have hc : c = X + c ^ 2 := by
    have h := congrArg (PowerSeries.map f) hC
    rw [map_add, map_pow, map_X] at h
    exact h
  have hB : X * a + (X * a) ^ 2 = c ^ 2 := by
    have h := congrArg (PowerSeries.map f) hA
    simp only [map_add, map_mul, map_pow, map_X] at h
    rw [mul_pow]
    exact h
  have hB0 : constantCoeff (X * a) = 0 := by simp
  have hcat := catalan_mod_two c hc0 hc
  have hsh := shifted_mod_two c (X * a) hcat hB0 hB
  rw [← ZMod.intCast_eq_one_iff_odd]
  have hcoef : ((coeff n A : ℤ) : K) = coeff (n + 1) (X * a) := by
    rw [coeff_succ_X_mul, hadef, coeff_map]
    rfl
  rw [hcoef]
  exact hsh (n + 1)

end HannaA273958

#print axioms HannaA273958.hanna_a273958
