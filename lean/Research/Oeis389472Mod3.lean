import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-!
A389472 second conjecture, proved directly from its integral generating equation.
The source generating-function equation is used as the hypothesis; no conjecture
from the external statement corpus is imported.
-/
noncomputable section
namespace Oeis389472Mod3
open PowerSeries
local notation "K" => ZMod 3
local notation "D" => PowerSeries.derivative K

private def h : PowerSeries K := X ^ 2 + X ^ 3
private lemma h_subst : HasSubst h := by
  apply HasSubst.of_constantCoeff_zero'
  simp [h]
/-- In characteristic three the substitution polynomial has derivative `-X`. -/
private lemma h_deriv : D h = -X := by
  simp only [h, map_add, derivative_pow, derivative_X]
  norm_num
  have h3 : (3 : PowerSeries K) = 0 := by
    simpa only [map_ofNat, map_zero] using congrArg (C : K →+* PowerSeries K) (show (3 : K) = 0 by decide)
  have h2 : (2 : PowerSeries K) = -1 := by
    have h3 : (3 : PowerSeries K) = 0 := by
      simpa only [map_ofNat, map_zero] using congrArg (C : K →+* PowerSeries K) (show (3 : K) = 0 by decide)
    linear_combination h3
  rw [h3, h2]
  ring

/-- A series fixed by substitution of order at least two must be constant. -/
private lemma fixed_is_constant (F : PowerSeries K) (hf : F.subst h = F) :
    F = C (constantCoeff F) := by
  let E := F - C (constantCoeff F)
  have hE0 : constantCoeff E = 0 := by simp [E]
  have hE : E.subst h = E := by
    simp only [E, subst_sub h_subst, subst_C, hf]
    rfl
  have horder : (2 : ENat) ≤ PowerSeries.order h := by
    apply nat_le_order h 2
    intro i hi
    interval_cases i <;> simp [h, coeff_X_pow]
  by_contra hne
  have hEn : E ≠ 0 := sub_ne_zero.mpr hne
  have hn := coe_toNat_order hEn
  have hpos := one_le_order_iff_constCoeff_eq_zero.mpr hE0
  have hbound := le_order_subst h h_subst E
  change MvPowerSeries.order h * PowerSeries.order E ≤ MvPowerSeries.order (E.subst h) at hbound
  rw [PowerSeries.order_eq_order] at horder
  have hh : (2 : ENat) * PowerSeries.order E ≤ PowerSeries.order E := by
    have ht := (mul_le_mul_of_nonneg_right horder (show 0 ≤ PowerSeries.order E from zero_le)).trans hbound
    simpa only [← PowerSeries.order_eq_order, hE] using ht
  rw [← hn] at hh hpos
  have ha : 2 * (PowerSeries.order E).toNat ≤ (PowerSeries.order E).toNat := by exact_mod_cast hh
  have hb : 1 ≤ (PowerSeries.order E).toNat := by exact_mod_cast hpos
  omega

/-- Two formal differentiations give invariance of the second derivative. -/
private lemma second_derivative_fixed (F : PowerSeries K)
    (heq : F.subst h = X ^ 2 * (1 + F)) :
    (D (D F)).subst h = D (D F) := by
  have h1 := congrArg D heq
  rw [derivative_subst h_subst, h_deriv] at h1
  simp only [Derivation.leibniz, map_add, derivative_one, zero_add, derivative_pow,
    derivative_X] at h1
  norm_num at h1
  have h2 : (2 : PowerSeries K) = -1 := by
    have h3 : (3 : PowerSeries K) = 0 := by
      simpa only [map_ofNat, map_zero] using congrArg (C : K →+* PowerSeries K) (show (3 : K) = 0 by decide)
    linear_combination h3
  rw [h2] at h1
  have step1 : (D F).subst h = 1 + F - X * D F := by
    apply (mul_right_cancel₀ (neg_ne_zero.mpr (X_ne_zero (R := K))))
    calc
      (D F).subst h * -X = X ^ 2 * D F + (1 + F) * (-1 * X) := by simpa using h1
      _ = (1 + F - X * D F) * -X := by ring
  have step2 := congrArg D step1
  rw [derivative_subst h_subst, h_deriv] at step2
  simp only [map_sub, map_add, derivative_one, zero_add, Derivation.leibniz,
    derivative_X] at step2
  apply (mul_right_cancel₀ (neg_ne_zero.mpr (X_ne_zero (R := K))))
  calc
    (D (D F)).subst h * -X = _ := step2
    _ = D (D F) * -X := by ring

/-- The mod-three assertion, directly from the original generating equation. -/
theorem residue_conjecture (F : PowerSeries K)
    (heq : F.subst (X ^ 2 + X ^ 3) = X ^ 2 * (1 + F))
    (n : ℕ) (hn : 1 < n) : coeff (3 * n - 1) F = 0 := by
  have hc := fixed_is_constant (D (D F)) (second_derivative_fixed F heq)
  have he := congrArg (coeff (3 * n - 3)) hc
  rw [coeff_derivative, coeff_derivative] at he
  have ha : 3 * n - 3 + 1 + 1 = 3 * n - 1 := by omega
  have hb : 3 * n - 3 + 1 = 3 * n - 2 := by omega
  rw [ha, hb] at he
  have hpos : 3 * n - 3 ≠ 0 := by omega
  simp only [coeff_C, if_neg hpos] at he
  have hcast2 : ((3 * n - 2 : ℕ) : K) = 1 := by
    have : 3 * n - 2 = 3 * (n - 1) + 1 := by omega
    rw [this]
    push_cast
    rw [show (3 : K) = 0 by decide]
    ring
  have hcast0 : ((3 * n - 3 : ℕ) : K) = 0 := by
    have : 3 * n - 3 = 3 * (n - 1) := by omega
    rw [this]
    push_cast
    rw [show (3 : K) = 0 by decide]
    ring
  rw [hcast2, hcast0] at he
  have htwo : (2 : K) ≠ 0 := by decide
  simpa only [zero_add, one_add_one_eq_two, mul_one, mul_eq_zero, or_iff_left htwo] using he

/-- Hanna's second A389472 conjecture for any integral solution of its defining equation. -/
theorem integer_conjecture (A : PowerSeries ℤ)
    (heq : A.subst (X ^ 2 + X ^ 3) = X ^ 2 * (1 + A))
    (n : ℕ) (hn : 1 < n) : (3 : ℤ) ∣ coeff (3 * n - 1) A := by
  let f : ℤ →+* K := Int.castRingHom K
  have hs : HasSubst (X ^ 2 + X ^ 3 : PowerSeries ℤ) := by
    apply HasSubst.of_constantCoeff_zero'
    simp
  have hm := congrArg (PowerSeries.map f) heq
  change (A.subst (X ^ 2 + X ^ 3)).map f = (X ^ 2 * (1 + A) : PowerSeries ℤ).map f at hm
  rw [map_subst hs] at hm
  change (A.map f).subst ((PowerSeries.map f) (X ^ 2 + X ^ 3)) =
    (PowerSeries.map f) (X ^ 2 * (1 + A)) at hm
  simp only [map_mul, map_add, map_pow, map_one, map_X] at hm
  have hr := residue_conjecture (A.map f) hm n hn
  change (coeff (3 * n - 1)) ((PowerSeries.map f) A) = 0 at hr
  rw [coeff_map] at hr
  change (↑(coeff (3 * n - 1) A) : K) = 0 at hr
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hr

#print axioms Oeis389472Mod3.integer_conjecture
end Oeis389472Mod3
