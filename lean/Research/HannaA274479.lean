import Mathlib.RingTheory.PowerSeries.Substitution
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-!
# OEIS A274479: the mod-3 conjecture

A274479 (Paul D. Hanna, Jun 2016), offset 1, data `1, 1, 4, 10, 34, ...`, NAME:
"G.f. satisfies: A(x)^2 = A( x^2/(1 - 2*x - 4*x^2) )."
COMMENT: "a(n) = 1 (mod 3) for n>=1 (conjecture)."

Formalization.  `x^2/(1 - 2x - 4x^2)` is the power series `h` with
`h * (1 - 2x - 4x^2) = x^2` (unique, since `1 - 2x - 4x^2` is a unit).  The offset gives
`a(0) = 0` and the first term is `a(1) = 1`.  (A normalization is necessary: if `A` is a
solution then so is every power `A^m`.)

Proof: modulo 3, `1 - 2x - 4x^2 = 1 + x - x^2` and `E = x/(1-x)` satisfies
`E(h) = h/(1-h) = x^2/(1 + x - 2x^2) = x^2/(1-x)^2 = E^2`.  Uniqueness: with `D = F - E`,
`D (F + E) = F^2 - E^2 = D(h)`; if `x^n ∣ D` then `x^(2n) ∣ D(h)` (as `x^2 ∣ h`), while
`F + E = x * (2 + ...)` with `2` a unit mod 3, so `x^(2n-1) ∣ D`.
-/

noncomputable section
namespace HannaA274479
open PowerSeries

local notation "K" => ZMod 3

lemma three_eq_zero : (3 : PowerSeries K) = 0 := by
  simpa only [map_ofNat, map_zero] using
    congrArg (C : K →+* PowerSeries K) (show (3 : K) = 0 by decide)

/-- `E = x/(1-x) = Σ_{n ≥ 1} x^n`. -/
def E : PowerSeries K := PowerSeries.mk fun n => if n = 0 then 0 else 1

lemma E_mul : E * (1 - X) = X := by
  ext n
  rcases n with _ | _ | n <;> simp [E, mul_sub, coeff_X, coeff_succ_mul_X]

lemma E_const : constantCoeff E = 0 := by
  rw [← coeff_zero_eq_constantCoeff_apply]
  simp [E]

lemma E_one : coeff 1 E = 1 := by simp [E]

lemma subst_one' {a : PowerSeries K} (ha : HasSubst a) : (1 : PowerSeries K).subst a = 1 := by
  rw [← coe_substAlgHom ha, map_one]

lemma E_subst_mul {a : PowerSeries K} (ha : HasSubst a) : E.subst a * (1 - a) = a := by
  have h := congrArg (fun f => f.subst a) E_mul
  simp only [subst_mul ha, subst_sub ha, subst_X ha, subst_one' ha] at h
  exact h

lemma ne_zero_of_const_one {a : PowerSeries K} (ha : constantCoeff a = 1) : a ≠ 0 := by
  intro h
  rw [h, map_zero] at ha
  exact zero_ne_one ha

/-- The substituted series `η` has zero constant term and is divisible by `x^2`. -/
lemma eta_props (η : PowerSeries K) (hη : η * (1 - 2 * X - 4 * X ^ 2) = X ^ 2) :
    constantCoeff η = 0 ∧ (X : PowerSeries K) ^ 2 ∣ η := by
  have hu : IsUnit (1 - 2 * X - 4 * X ^ 2 : PowerSeries K) := by
    rw [isUnit_iff_constantCoeff]; simp
  refine ⟨?_, ?_⟩
  · have h := congrArg constantCoeff hη
    simpa using h
  · refine (hu.dvd_mul_right).mp ?_
    rw [hη]

/-- `E` solves the reduced equation. -/
lemma E_eq (η : PowerSeries K) (hη : η * (1 - 2 * X - 4 * X ^ 2) = X ^ 2) :
    E ^ 2 = E.subst η := by
  have hη0 := (eta_props η hη).1
  have hs : HasSubst η := HasSubst.of_constantCoeff_zero' hη0
  have he := E_subst_mul hs
  have h1 := E_mul
  have hne : ((1 - η) * (1 - X) ^ 2 * (1 - 2 * X - 4 * X ^ 2) : PowerSeries K) ≠ 0 :=
    ne_zero_of_const_one (by simp [hη0])
  have key : (E.subst η - E ^ 2) * ((1 - η) * (1 - X) ^ 2 * (1 - 2 * X - 4 * X ^ 2)) = 0 := by
    linear_combination ((1 - X) ^ 2 * (1 - 2 * X - 4 * X ^ 2)) * he +
      ((1 - X) ^ 2 + X ^ 2) * hη -
      ((1 - η) * (1 - 2 * X - 4 * X ^ 2) * (E * (1 - X) + X)) * h1 +
      (2 * X ^ 4) * three_eq_zero
  exact (sub_eq_zero.mp ((mul_eq_zero.mp key).resolve_right hne)).symm

/-- The statement in `(ZMod 3)[[X]]`. -/
theorem residue (F η : PowerSeries K) (h0 : constantCoeff F = 0) (h1 : coeff 1 F = 1)
    (hη : η * (1 - 2 * X - 4 * X ^ 2) = X ^ 2) (hF : F ^ 2 = F.subst η) : F = E := by
  obtain ⟨hη0, hηX⟩ := eta_props η hη
  have hs : HasSubst η := HasSubst.of_constantCoeff_zero' hη0
  have hE := E_eq η hη
  -- `F + E = X * W` with `W(0) = 2`, a unit
  have hXFE : (X : PowerSeries K) ∣ F + E := by
    rw [X_dvd_iff]; simp [h0, E_const]
  obtain ⟨W, hW⟩ := hXFE
  have hW0 : constantCoeff W = 2 := by
    have h := congrArg (coeff 1) hW
    rw [map_add, h1, E_one, show (1 : ℕ) = 0 + 1 from rfl, coeff_succ_X_mul,
      coeff_zero_eq_constantCoeff_apply] at h
    rw [← h]; norm_num
  have hWu : IsUnit W := by
    rw [isUnit_iff_constantCoeff, hW0]
    exact isUnit_iff_ne_zero.mpr (by decide)
  have key : ∀ n, 2 ≤ n → X ^ n ∣ F - E := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base =>
      rw [X_pow_dvd_iff]
      intro m hm
      interval_cases m
      · simp [map_sub, coeff_zero_eq_constantCoeff_apply, h0, E_const]
      · simp [map_sub, h1, E_one]
    | succ n hn ih =>
      have hid : X * (F - E) * W = (F - E).subst η := by
        rw [subst_sub hs]
        linear_combination -(F - E) * hW + hF - hE
      obtain ⟨Q, hQ⟩ := ih
      have hsub : X ^ (2 * n) ∣ (F - E).subst η := by
        rw [hQ, subst_mul hs, subst_pow hs, subst_X hs, pow_mul]
        exact dvd_mul_of_dvd_left (pow_dvd_pow_of_dvd hηX n) _
      rw [← hid] at hsub
      have h2 : X * X ^ (2 * n - 1) ∣ X * (F - E) := by
        rw [← pow_succ', show 2 * n - 1 + 1 = 2 * n by omega]
        exact (hWu.dvd_mul_right).mp hsub
      have h3 : X ^ (2 * n - 1) ∣ F - E := (mul_dvd_mul_iff_left X_ne_zero).mp h2
      exact (pow_dvd_pow X (by omega : n + 1 ≤ 2 * n - 1)).trans h3
  have hz : F - E = 0 := by
    ext m
    have h := key (m + 2) (by omega)
    rw [X_pow_dvd_iff] at h
    simpa using h m (by omega)
  exact sub_eq_zero.mp hz

/-- **A274479 mod-3 conjecture.**  Let `A` be an integer power series with `a(0) = 0`,
`a(1) = 1`, and `A^2 = A(h)` where `h = x^2/(1 - 2x - 4x^2)` (i.e.
`h * (1 - 2x - 4x^2) = x^2`).  Then `a(n) ≡ 1 (mod 3)` for every `n ≥ 1`. -/
theorem hanna_a274479 (A h : PowerSeries ℤ) (h0 : constantCoeff A = 0) (h1 : coeff 1 A = 1)
    (hh : h * (1 - 2 * X - 4 * X ^ 2) = X ^ 2) (hA : A ^ 2 = A.subst h) (n : ℕ) (hn : 1 ≤ n) :
    coeff n A ≡ 1 [ZMOD 3] := by
  let f : ℤ →+* K := Int.castRingHom K
  have hh0 : constantCoeff h = 0 := by
    have := congrArg constantCoeff hh
    simpa using this
  have hs : HasSubst h := HasSubst.of_constantCoeff_zero' hh0
  have hη : h.map f * (1 - 2 * X - 4 * X ^ 2) = X ^ 2 := by
    have := congrArg (PowerSeries.map f) hh
    simpa only [map_mul, map_sub, map_ofNat, map_pow, map_X, map_one] using this
  have hm : (A.map f) ^ 2 = (A.map f).subst (h.map f) := by
    have e := map_subst hs (h := f) A
    have h4 := congrArg (PowerSeries.map f) hA
    rw [map_pow] at h4
    exact h4.trans e
  have hc0 : constantCoeff (A.map f) = 0 := by
    rw [← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff_apply, h0,
      map_zero]
  have hc1 : coeff 1 (A.map f) = 1 := by rw [coeff_map, h1, map_one]
  have hF := residue (A.map f) (h.map f) hc0 hc1 hη hm
  have hcoef := congrArg (coeff n) hF
  rw [coeff_map] at hcoef
  have hE : coeff n E = 1 := by simp [E, show n ≠ 0 by omega]
  rw [hE] at hcoef
  change ((coeff n A : ℤ) : K) = 1 at hcoef
  have hmod := (ZMod.intCast_eq_intCast_iff (coeff n A) 1 3).mp (by rw [Int.cast_one]; exact hcoef)
  exact_mod_cast hmod

end HannaA274479

#print axioms HannaA274479.hanna_a274479
