import Mathlib.RingTheory.PowerSeries.Substitution
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-!
# OEIS A377100: the mod-3 conjecture

A377100 (Paul D. Hanna, Nov 24 2024), offset 1, data `1, 1, 1, 4, 10, 28, ...`, NAME:
"G.f. A(x) satisfies A(x) = A(x^3)/A(x^2) + A(x)^2."
COMMENT: "Conjecture: a(n) == 1 (mod 3) for n >= 1, which has been verified for the initial
2305 terms."

Formalization of the equation.  `A(x^3)/A(x^2)` is a power series `U` with
`A(x^2) * U = A(x^3)` (exact division; `U` is unique because `ℤ[[x]]` is a domain and
`A(x^2) ≠ 0`), and the equation reads `A = U + A^2`.  The offset gives `a(0) = 0` and the
first term is `a(1) = 1`.  (Some normalization of the leading term is necessary: for
instance `x^2 * G` with `G = G(x^3)/G(x^2) + x^2 G^2` gives other solutions.)

Proof: modulo 3, `E = x/(1-x)` satisfies the equation because `1 - x^3 = (1 - x)^3`.
Uniqueness: if `F ≡ E` modulo `x^n` (`n ≥ 2`), then
`E(x^2) (F - E) (1 - F - E) = D(x^3) - D(x^2) (F - F^2)` with `D = F - E` is divisible by
`x^(2n+1)`, and since `E(x^2) = x^2 * unit` and `1 - F - E` is a unit, `x^(2n-1) ∣ F - E`.
-/

noncomputable section
namespace HannaA377100
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

/-- `E(a) * (1 - a) = a` for every admissible substitution `a`. -/
lemma E_subst_mul {a : PowerSeries K} (ha : HasSubst a) : E.subst a * (1 - a) = a := by
  have h := congrArg (fun f => f.subst a) E_mul
  simp only [subst_mul ha, subst_sub ha, subst_X ha, subst_one' ha] at h
  exact h

lemma one_sub_ne_zero {a : PowerSeries K} (ha : constantCoeff a = 0) : (1 - a) ≠ 0 := by
  intro h
  have := congrArg constantCoeff h
  simp [ha] at this

/-- `E` solves the reduced equation. -/
lemma E_eq : E.subst (X ^ 2 : PowerSeries K) * (E - E ^ 2) = E.subst (X ^ 3 : PowerSeries K) := by
  have hs2 : HasSubst (X ^ 2 : PowerSeries K) := HasSubst.X_pow two_ne_zero
  have hs3 : HasSubst (X ^ 3 : PowerSeries K) := HasSubst.X_pow three_ne_zero
  have h1 := E_mul
  have h2 := E_subst_mul hs2
  have h3 := E_subst_mul hs3
  have hc : (1 - X) ^ 3 = (1 - X ^ 3 : PowerSeries K) := by
    linear_combination (X ^ 2 - X) * three_eq_zero
  have hne : ((1 - X ^ 2) * (1 - X) ^ 3 : PowerSeries K) ≠ 0 :=
    mul_ne_zero (one_sub_ne_zero (by simp)) (pow_ne_zero _ (one_sub_ne_zero (by simp)))
  have key : (E.subst (X ^ 2 : PowerSeries K) * (E - E ^ 2) - E.subst (X ^ 3 : PowerSeries K)) *
      ((1 - X ^ 2) * (1 - X) ^ 3) = 0 := by
    linear_combination (E * (1 - E) * (1 - X) ^ 3) * h2 +
      (X ^ 2 * (1 - X) * ((1 - X) - E * (1 - X) - X)) * h1 - (1 - X ^ 2) * h3 -
      (E.subst (X ^ 3 : PowerSeries K) * (1 - X ^ 2)) * hc + (X ^ 3 * (X ^ 2 - X)) * three_eq_zero
  exact sub_eq_zero.mp ((mul_eq_zero.mp key).resolve_right hne)

lemma X_pow_dvd_subst_X_pow {k n : ℕ} (hk : k ≠ 0) {D : PowerSeries K} (h : X ^ n ∣ D) :
    X ^ (k * n) ∣ D.subst (X ^ k : PowerSeries K) := by
  obtain ⟨Q, rfl⟩ := h
  have hs : HasSubst (X ^ k : PowerSeries K) := HasSubst.X_pow hk
  rw [subst_mul hs, subst_pow hs, subst_X hs, ← pow_mul]
  exact dvd_mul_right _ _

/-- The statement in `(ZMod 3)[[X]]`: the reduced equation has the unique normalized solution
`x/(1-x)`. -/
theorem residue (F : PowerSeries K) (h0 : constantCoeff F = 0) (h1 : coeff 1 F = 1)
    (hF : F.subst (X ^ 2 : PowerSeries K) * (F - F ^ 2) = F.subst (X ^ 3 : PowerSeries K)) :
    F = E := by
  have hs2 : HasSubst (X ^ 2 : PowerSeries K) := HasSubst.X_pow two_ne_zero
  have hs3 : HasSubst (X ^ 3 : PowerSeries K) := HasSubst.X_pow three_ne_zero
  have hE := E_eq
  have hE2 := E_subst_mul hs2
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
      -- the difference identity
      have hid : E.subst (X ^ 2 : PowerSeries K) * ((F - E) * (1 - F - E)) =
          (F - E).subst (X ^ 3 : PowerSeries K) -
            (F - E).subst (X ^ 2 : PowerSeries K) * (F - F ^ 2) := by
        rw [subst_sub hs2, subst_sub hs3]
        linear_combination hF - hE
      -- divisibility of the right-hand side by `X^(2n+1)`
      have hX : (X : PowerSeries K) ∣ F - F ^ 2 := by
        rw [X_dvd_iff]; simp [h0]
      have d3 : X ^ (2 * n + 1) ∣ (F - E).subst (X ^ 3 : PowerSeries K) :=
        (pow_dvd_pow X (by omega : 2 * n + 1 ≤ 3 * n)).trans
          (X_pow_dvd_subst_X_pow three_ne_zero ih)
      have d2 : X ^ (2 * n + 1) ∣ (F - E).subst (X ^ 2 : PowerSeries K) * (F - F ^ 2) := by
        rw [pow_succ]
        exact mul_dvd_mul (X_pow_dvd_subst_X_pow two_ne_zero ih) hX
      have hL : X ^ (2 * n + 1) ∣
          E.subst (X ^ 2 : PowerSeries K) * ((F - E) * (1 - F - E)) := by
        rw [hid]; exact dvd_sub d3 d2
      -- multiply by `1 - X^2` to replace `E(x^2)` by `x^2`
      have hL2 : X ^ 2 * X ^ (2 * n - 1) ∣ X ^ 2 * ((F - E) * (1 - F - E)) := by
        rw [← pow_add, show 2 + (2 * n - 1) = 2 * n + 1 by omega, ← hE2]
        have := dvd_mul_of_dvd_left hL (1 - X ^ 2)
        calc X ^ (2 * n + 1) ∣ E.subst (X ^ 2 : PowerSeries K) * ((F - E) * (1 - F - E)) *
              (1 - X ^ 2) := this
          _ = E.subst (X ^ 2 : PowerSeries K) * (1 - X ^ 2) * ((F - E) * (1 - F - E)) := by ring
      have hL3 : X ^ (2 * n - 1) ∣ (F - E) * (1 - F - E) :=
        (mul_dvd_mul_iff_left (pow_ne_zero 2 X_ne_zero)).mp hL2
      have hu : IsUnit (1 - F - E) := by
        rw [isUnit_iff_constantCoeff]
        simp [h0, E_const]
      have hL4 : X ^ (2 * n - 1) ∣ F - E := (hu.dvd_mul_right).mp hL3
      exact (pow_dvd_pow X (by omega : n + 1 ≤ 2 * n - 1)).trans hL4
  have hz : F - E = 0 := by
    ext m
    have h := key (m + 2) (by omega)
    rw [X_pow_dvd_iff] at h
    simpa using h m (by omega)
  exact sub_eq_zero.mp hz

/-- **A377100 mod-3 conjecture.**  Let `A` be an integer power series with `a(0) = 0`,
`a(1) = 1`, and `A = U + A^2` where `U = A(x^3)/A(x^2)` (i.e. `A(x^2) * U = A(x^3)`).
Then `a(n) ≡ 1 (mod 3)` for every `n ≥ 1`. -/
theorem hanna_a377100 (A U : PowerSeries ℤ) (h0 : constantCoeff A = 0) (h1 : coeff 1 A = 1)
    (hU : A.subst (X ^ 2 : PowerSeries ℤ) * U = A.subst (X ^ 3 : PowerSeries ℤ))
    (hA : A = U + A ^ 2) (n : ℕ) (hn : 1 ≤ n) : coeff n A ≡ 1 [ZMOD 3] := by
  let f : ℤ →+* K := Int.castRingHom K
  have hs2 : HasSubst (X ^ 2 : PowerSeries ℤ) := HasSubst.X_pow two_ne_zero
  have hs3 : HasSubst (X ^ 3 : PowerSeries ℤ) := HasSubst.X_pow three_ne_zero
  have hUA : U = A - A ^ 2 := by linear_combination -hA
  rw [hUA] at hU
  have hm : (A.map f).subst (X ^ 2 : PowerSeries K) * (A.map f - (A.map f) ^ 2) =
      (A.map f).subst (X ^ 3 : PowerSeries K) := by
    have e2 : PowerSeries.map f (A.subst (X ^ 2 : PowerSeries ℤ)) =
        (A.map f).subst (X ^ 2 : PowerSeries K) := by
      have h1 := map_subst hs2 (h := f) A
      have h3 : (A.map f).subst ((PowerSeries.map f) (X ^ 2 : PowerSeries ℤ)) =
          (A.map f).subst (X ^ 2 : PowerSeries K) := by rw [map_pow, map_X]
      exact h1.trans h3
    have e3 : PowerSeries.map f (A.subst (X ^ 3 : PowerSeries ℤ)) =
        (A.map f).subst (X ^ 3 : PowerSeries K) := by
      have h1 := map_subst hs3 (h := f) A
      have h3 : (A.map f).subst ((PowerSeries.map f) (X ^ 3 : PowerSeries ℤ)) =
          (A.map f).subst (X ^ 3 : PowerSeries K) := by rw [map_pow, map_X]
      exact h1.trans h3
    have h := congrArg (PowerSeries.map f) hU
    rw [map_mul, e2, e3, map_sub, map_pow] at h
    exact h
  have hc0 : constantCoeff (A.map f) = 0 := by
    rw [← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff_apply, h0,
      map_zero]
  have hc1 : coeff 1 (A.map f) = 1 := by rw [coeff_map, h1, map_one]
  have hF := residue (A.map f) hc0 hc1 hm
  have hcoef := congrArg (coeff n) hF
  rw [coeff_map] at hcoef
  have hE : coeff n E = 1 := by simp [E, show n ≠ 0 by omega]
  rw [hE] at hcoef
  change ((coeff n A : ℤ) : K) = 1 at hcoef
  have hmod := (ZMod.intCast_eq_intCast_iff (coeff n A) 1 3).mp (by rw [Int.cast_one]; exact hcoef)
  exact_mod_cast hmod

end HannaA377100

#print axioms HannaA377100.hanna_a377100
