import Mathlib.RingTheory.PowerSeries.Substitution
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.RingTheory.PowerSeries.Expand
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Tactic

/-!
# OEIS A361047: the coefficients modulo 3

A361047 (Paul D. Hanna, Mar 03 2023), offset 1, NAME:
"Expansion of g.f. A(x) satisfying A(x) = Series_Reversion(x - x^3*A'(x)^2)."
FORMULA: "G.f. A(x) = Sum_{n>=1} a(n)*x^(2*n-1) may be defined by the following.
(1) A(x) = Series_Reversion(x - x^3*A'(x)^2)."  EXAMPLE: "By definition, A(x - x^3*A'(x)^2) = x".
COMMENT: "Conjecture: a(n) == 1 (mod 3) iff n = (3^k - 1)/2 for k >= 0, otherwise
a(n) == 0 (mod 3)."

Indexing remark.  With the entry's offset (`a(n)` is the coefficient of `x^(2n-1)`) the
literal statement is contradicted by the data (`a(2) = 1`, but `2 ≠ (3^k-1)/2`); it is
correct for the 0-based index `i = n - 1` (`x^(2i+1)`, `i = (3^k-1)/2` iff `2i+1 = 3^k`).
We prove the intended statement in exponent form: for every integer power series `A` with
`A(0) = 0` and `A(x - x^3 A'(x)^2) = x`,
* `[x^(3^k)] A ≡ 1 (mod 3)` for all `k`, and
* `[x^m] A ≡ 0 (mod 3)` whenever `m` is not a power of 3.

Proof: modulo 3 let `S = Σ_k x^(3^k)`.  Then `S' = 1` (as `3 ∣ 3^k` for `k ≥ 1`) and
`S - S^3 = S - S(x^3) = x`, so `S` is the compositional inverse of `g = x - x^3 = x - x^3 S'^2`.
Uniqueness: with `D = F - S` and `x^n ∣ D`, the two inner series differ by
`x^3 (F'^2 - S'^2) = x^3 D' (F' + S')`, divisible by `x^(n+2)`, so
`0 = F(g_F) - S(g_S) ≡ D (mod x^(n+1))`.
-/

noncomputable section
namespace HannaA361047
open PowerSeries

local notation "K" => ZMod 3
local notation "Dr" => PowerSeries.derivative K

lemma cube_eq_expand (F : PowerSeries K) : F ^ 3 = expand 3 three_ne_zero F := by
  have h := MvPowerSeries.map_frobenius_expand (R := K) (σ := Unit) 3 three_ne_zero (f := F)
  rw [ZMod.frobenius_zmod] at h
  rw [← h]
  simp [MvPowerSeries.map_id]
  rfl

lemma not_pow_div (m : ℕ) (hm : ∀ j, m ≠ 3 ^ j) (h3 : 3 ∣ m) : ∀ j, m / 3 ≠ 3 ^ j := by
  intro j hj
  apply hm (j + 1)
  obtain ⟨t, rfl⟩ := h3
  rw [Nat.mul_div_cancel_left t (by norm_num)] at hj
  rw [hj, pow_succ]; ring

open Classical in
/-- `S = Σ_k x^(3^k)`. -/
def S : PowerSeries K := PowerSeries.mk fun m => if ∃ k, m = 3 ^ k then 1 else 0

lemma coeff_S_pow (k : ℕ) : coeff (3 ^ k) S = 1 := by
  classical
  simp only [S, coeff_mk]
  rw [if_pos ⟨k, rfl⟩]

lemma coeff_S_nonpow (m : ℕ) (hm : ∀ k, m ≠ 3 ^ k) : coeff m S = 0 := by
  classical
  simp only [S, coeff_mk]
  rw [if_neg (by push Not; exact hm)]

lemma S_const : constantCoeff S = 0 := by
  rw [← coeff_zero_eq_constantCoeff_apply]
  exact coeff_S_nonpow 0 (fun k h => by have := pow_pos (by norm_num : 0 < 3) k; omega)

lemma S_one : coeff 1 S = 1 := by simpa using coeff_S_pow 0

/-- `S' = 1` in characteristic 3. -/
lemma S_deriv : Dr S = 1 := by
  ext n
  rw [coeff_derivative, coeff_one]
  rcases n with _ | n
  · simp [S_one]
  · rw [if_neg (by omega)]
    by_cases h : ∃ k, n + 1 + 1 = 3 ^ k
    · obtain ⟨k, hk⟩ := h
      have hk0 : k ≠ 0 := by rintro rfl; simp at hk
      have hc : ((n + 1 + 1 : ℕ) : K) = 0 := by
        rw [hk, ZMod.natCast_eq_zero_iff]
        exact dvd_pow_self 3 hk0
      push_cast at hc ⊢
      rw [hc, mul_zero]
    · push Not at h
      rw [coeff_S_nonpow _ h, zero_mul]

/-- `S - S^3 = x`. -/
lemma S_sub_cube : S - S ^ 3 = X := by
  ext m
  rw [cube_eq_expand, map_sub, coeff_expand, coeff_X]
  by_cases hp : ∃ k, m = 3 ^ k
  · obtain ⟨k, rfl⟩ := hp
    rw [coeff_S_pow]
    rcases k with _ | k
    · simp
    · have h3 : 3 ∣ 3 ^ (k + 1) := dvd_pow_self 3 (Nat.succ_ne_zero k)
      rw [if_pos h3, show 3 ^ (k + 1) / 3 = 3 ^ k by rw [pow_succ, Nat.mul_div_cancel _ (by norm_num)],
        coeff_S_pow, sub_self, if_neg]
      have := Nat.one_lt_pow (Nat.succ_ne_zero k) (by norm_num : 1 < 3)
      omega
  · push Not at hp
    rw [coeff_S_nonpow m hp]
    have hm1 : m ≠ 1 := fun h => hp 0 (by simp [h])
    rw [if_neg hm1]
    split_ifs with h3
    · rw [coeff_S_nonpow _ (not_pow_div m hp h3), sub_zero]
    · rw [sub_zero]

lemma hsS : HasSubst S := HasSubst.of_constantCoeff_zero' S_const

/-- `S(x - x^3) = x`. -/
lemma S_subst_g : PowerSeries.subst (X - X ^ 3 : PowerSeries K) S = X := by
  have hu : IsUnit (coeff 1 S) := by rw [S_one]; exact isUnit_one
  obtain ⟨Q, hQdef⟩ : ∃ Q, Q = S.substInvOfIsUnit hu := ⟨_, rfl⟩
  have hQ : HasSubst Q := by rw [hQdef]; exact HasSubst.substInvOfIsUnit S hu
  have hSQ : PowerSeries.subst Q S = X := by rw [hQdef]; exact subst_substInvOfIsUnit_right S S_const hu
  have hgS : (X - X ^ 3 : PowerSeries K).subst S = X := by
    have e : (X - X ^ 3 : PowerSeries K).subst S = S - S ^ 3 := by
      rw [subst_sub hsS, subst_pow hsS, subst_X hsS]
    rw [e, S_sub_cube]
  have hcomp : PowerSeries.subst Q (PowerSeries.subst S (X - X ^ 3 : PowerSeries K)) =
      PowerSeries.subst (PowerSeries.subst Q S) (X - X ^ 3 : PowerSeries K) :=
    subst_comp_subst_apply hsS hQ (X - X ^ 3 : PowerSeries K)
  rw [hSQ, X_subst, hgS, subst_X hQ] at hcomp
  rw [← hcomp, hSQ]

/-- Composition respects congruences modulo `X^n` in the inner argument. -/
lemma subst_congr_right (F G1 G2 : PowerSeries K) (hG1 : HasSubst G1) (hG2 : HasSubst G2)
    (n : ℕ) (h : X ^ n ∣ G1 - G2) : X ^ n ∣ F.subst G1 - F.subst G2 := by
  rw [X_pow_dvd_iff]
  intro m hm
  rw [map_sub, sub_eq_zero, coeff_subst' hG1, coeff_subst' hG2]
  refine finsum_congr (fun d => ?_)
  have h' : X ^ n ∣ G1 ^ d - G2 ^ d := h.trans (sub_dvd_pow_sub_pow G1 G2 d)
  rw [X_pow_dvd_iff] at h'
  have := h' m hm
  rw [map_sub, sub_eq_zero] at this
  rw [this]

lemma deriv_dvd {D : PowerSeries K} {n : ℕ} (h : X ^ (n + 1) ∣ D) : X ^ n ∣ Dr D := by
  rw [X_pow_dvd_iff] at h ⊢
  intro m hm
  rw [coeff_derivative, h (m + 1) (by omega), zero_mul]

/-- The statement in `(ZMod 3)[[X]]`: the reduced equation forces `F = S`. -/
theorem residue (F : PowerSeries K) (h0 : constantCoeff F = 0)
    (hF : F.subst (X - X ^ 3 * (Dr F) ^ 2 : PowerSeries K) = X) : F = S := by
  obtain ⟨gF, hgF⟩ : ∃ gF : PowerSeries K, gF = X - X ^ 3 * (Dr F) ^ 2 := ⟨_, rfl⟩
  obtain ⟨g, hg⟩ : ∃ g : PowerSeries K, g = X - X ^ 3 := ⟨_, rfl⟩
  rw [← hgF] at hF
  have hgF0 : constantCoeff gF = 0 := by simp [hgF]
  have hsF : HasSubst gF := HasSubst.of_constantCoeff_zero' hgF0
  have hsg : HasSubst g := HasSubst.of_constantCoeff_zero' (by simp [hg])
  have hSg : PowerSeries.subst g S = X := by rw [hg]; exact S_subst_g
  -- `gF = X * V` with `V(0) = 1`
  have hV : gF = X * (1 - X ^ 2 * (Dr F) ^ 2) := by rw [hgF]; ring
  have key : ∀ n, 1 ≤ n → X ^ n ∣ F - S := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base =>
      rw [pow_one, X_dvd_iff, map_sub, h0, S_const, sub_zero]
    | succ n hn ih =>
      obtain ⟨Q, hQ⟩ := ih
      -- (a) `D ∘ gF ≡ D`
      have ha : X ^ (n + 1) ∣ (F - S).subst gF - (F - S) := by
        have e : (F - S).subst gF - (F - S) =
            X ^ n * ((1 - X ^ 2 * (Dr F) ^ 2) ^ n * Q.subst gF - Q) := by
          rw [hQ, subst_mul hsF, subst_pow hsF, subst_X hsF, hV, mul_pow]; ring
        rw [e, pow_succ]
        refine mul_dvd_mul_left _ ?_
        rw [X_dvd_iff, map_sub, map_mul, map_pow]
        have hQg : constantCoeff (Q.subst gF) = constantCoeff Q := by
          have hXg : (X : PowerSeries K) ^ 1 ∣ gF - X := by
            rw [pow_one, X_dvd_iff]; simp [hgF]
          have := subst_congr_right Q gF X hsF HasSubst.X' 1 hXg
          rw [X_subst, pow_one, X_dvd_iff, map_sub, sub_eq_zero] at this
          exact this
        rw [hQg]; simp
      -- (b) `S ∘ gF ≡ S ∘ g`
      have hb : X ^ (n + 1) ∣ PowerSeries.subst gF S - PowerSeries.subst g S := by
        have hdiff : X ^ (n + 1) ∣ gF - g := by
          have hD : X ^ (n - 1) ∣ Dr (F - S) := by
            apply deriv_dvd
            rw [show n - 1 + 1 = n by omega, hQ]
            exact dvd_mul_right _ _
          have e : gF - g = -(X ^ 3 * (Dr (F - S) * (Dr F + Dr S))) := by
            rw [hgF, hg, map_sub, S_deriv]; ring
          rw [e, dvd_neg]
          have : (X : PowerSeries K) ^ (n + 1) ∣ (X : PowerSeries K) ^ 3 * X ^ (n - 1) := by
            rw [← pow_add]; exact pow_dvd_pow X (by omega)
          exact this.trans (mul_dvd_mul_left _ (dvd_mul_of_dvd_left hD _))
        exact subst_congr_right S gF g hsF hsg (n + 1) hdiff
      -- combine: `F∘gF - S∘g = 0`
      have hsum : F - S = ((F - S) - (F - S).subst gF) - (PowerSeries.subst gF S - PowerSeries.subst g S) := by
        have e0 : (F - S).subst gF = F.subst gF - PowerSeries.subst gF S := subst_sub hsF F S
        rw [e0, hF, hSg]; ring
      rw [hsum]
      refine dvd_sub ?_ hb
      rw [← neg_sub, dvd_neg]
      exact ha
  have hz : F - S = 0 := by
    ext m
    have h := key (m + 1) (by omega)
    rw [X_pow_dvd_iff] at h
    simpa using h m (by omega)
  exact sub_eq_zero.mp hz

lemma map_derivative (f : ℤ →+* K) (A : PowerSeries ℤ) :
    PowerSeries.map f (derivative ℤ A) = Dr (PowerSeries.map f A) := by
  ext n
  simp only [coeff_map, coeff_derivative, map_mul, map_add, map_natCast, map_one]

lemma reduce (A : PowerSeries ℤ) (h0 : constantCoeff A = 0)
    (hA : A.subst (X - X ^ 3 * (derivative ℤ A) ^ 2 : PowerSeries ℤ) = X) :
    A.map (Int.castRingHom K) = S := by
  let f : ℤ →+* K := Int.castRingHom K
  have hs : HasSubst (X - X ^ 3 * (derivative ℤ A) ^ 2 : PowerSeries ℤ) :=
    HasSubst.of_constantCoeff_zero' (by simp)
  have hm : (A.map f).subst (X - X ^ 3 * (Dr (A.map f)) ^ 2 : PowerSeries K) = X := by
    have e := map_subst hs (h := f) A
    have h := congrArg (PowerSeries.map f) hA
    have hg : PowerSeries.map f (X - X ^ 3 * (derivative ℤ A) ^ 2 : PowerSeries ℤ) =
        (X - X ^ 3 * (Dr (A.map f)) ^ 2 : PowerSeries K) := by
      simp only [map_sub, map_mul, map_pow, map_X, map_derivative]
    calc (A.map f).subst (X - X ^ 3 * (Dr (A.map f)) ^ 2 : PowerSeries K)
        = (A.map f).subst (PowerSeries.map f (X - X ^ 3 * (derivative ℤ A) ^ 2 : PowerSeries ℤ)) := by
          rw [hg]
      _ = PowerSeries.map f (A.subst (X - X ^ 3 * (derivative ℤ A) ^ 2 : PowerSeries ℤ)) := e.symm
      _ = X := by rw [h, map_X]
  have hc0 : constantCoeff (A.map f) = 0 := by
    rw [← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff_apply, h0,
      map_zero]
  exact residue (A.map f) hc0 hm

/-- **A361047 (exponent form), part 1.**  `[x^(3^k)] A ≡ 1 (mod 3)`. -/
theorem hanna_a361047_pow (A : PowerSeries ℤ) (h0 : constantCoeff A = 0)
    (hA : A.subst (X - X ^ 3 * (derivative ℤ A) ^ 2 : PowerSeries ℤ) = X) (k : ℕ) :
    coeff (3 ^ k) A ≡ 1 [ZMOD 3] := by
  have hcoef := congrArg (coeff (3 ^ k)) (reduce A h0 hA)
  rw [coeff_map, coeff_S_pow] at hcoef
  change ((coeff (3 ^ k) A : ℤ) : K) = 1 at hcoef
  have hmod := (ZMod.intCast_eq_intCast_iff (coeff (3 ^ k) A) 1 3).mp
    (by rw [Int.cast_one]; exact hcoef)
  exact_mod_cast hmod

/-- **A361047 (exponent form), part 2.**  `[x^m] A ≡ 0 (mod 3)` if `m` is not a power of 3. -/
theorem hanna_a361047_nonpow (A : PowerSeries ℤ) (h0 : constantCoeff A = 0)
    (hA : A.subst (X - X ^ 3 * (derivative ℤ A) ^ 2 : PowerSeries ℤ) = X) (m : ℕ)
    (hm : ∀ k, m ≠ 3 ^ k) : (3 : ℤ) ∣ coeff m A := by
  have hcoef := congrArg (coeff m) (reduce A h0 hA)
  rw [coeff_map, coeff_S_nonpow m hm] at hcoef
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).mp hcoef

end HannaA361047

#print axioms HannaA361047.hanna_a361047_pow
#print axioms HannaA361047.hanna_a361047_nonpow
