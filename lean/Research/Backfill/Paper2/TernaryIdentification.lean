import Research.Backfill.Paper2.TernaryAlgebra
import Research.Backfill.Paper2.TernaryBinomial

/-! Identify the actual integral algebraic inverse with the prescribed Nat-quotient
series. Rational comparison is cleared before integer division; no divisibility premise. -/
set_option autoImplicit false
noncomputable section
namespace BackfillPaper2.TernaryIdentification
open PowerSeries BackfillPaper2.Challenge BackfillPaper2.TernaryAlgebra BackfillPaper2.TernaryBinomial
local notation "D" => PowerSeries.derivative (R := ℤ)

theorem coeff_even (V : PowerSeries ℤ) (h0 : constantCoeff V = 0)
    (hODE : (4 - 27 * X ^ 2) * D (D V) - 27 * X * D V + 3 * V = 0) (k : ℕ) :
    coeff (2 * k) V = 0 := by
  induction k with
  | zero => simpa only [Nat.mul_zero, coeff_zero_eq_constantCoeff_apply] using h0
  | succ k ih =>
    have he := ode_coeff_recurrence V hODE (2 * k)
    rw [ih, mul_zero] at he
    have hn : 4 * ((2 * k + 2 : ℕ) : ℤ) * ((2 * k + 1 : ℕ) : ℤ) ≠ 0 := by positivity
    have hz := (mul_eq_zero.mp he).resolve_left hn
    simpa only [show 2 * (k + 1) = 2 * k + 2 by omega] using hz

theorem coeff_odd_rational (V : PowerSeries ℤ) (h1 : coeff 1 V = 1)
    (hODE : (4 - 27 * X ^ 2) * D (D V) - 27 * X * D V + 3 * V = 0) (k : ℕ) :
    ((coeff (2 * k + 1) V : ℤ) : ℚ) = q k := by
  induction k with
  | zero => simp only [Nat.mul_zero, zero_add, h1, Int.cast_one, q_zero]
  | succ k ih =>
    have hv := ode_coeff_recurrence V hODE (2 * k + 1)
    have hvq : (4 : ℚ) * ((2 * k + 1 + 2 : ℕ) : ℚ) * ((2 * k + 1 + 1 : ℕ) : ℚ) *
        ((coeff (2 * k + 1 + 2) V : ℤ) : ℚ) =
        (27 * (((2 * k + 1 : ℕ) : ℚ)) ^ 2 - 3) * ((coeff (2 * k + 1) V : ℤ) : ℚ) := by
      exact_mod_cast hv
    rw [show 2 * k + 1 + 2 = 2 * (k + 1) + 1 by omega, ih] at hvq
    push_cast at hvq
    have hq := q_recurrence k
    have hz : (4 * (2 * (k : ℚ) + 3) * (2 * (k : ℚ) + 2)) *
        (((coeff (2 * (k + 1) + 1) V : ℤ) : ℚ) - q (k + 1)) = 0 := by
      linear_combination hvq - 4 * hq
    have hn : 4 * (2 * (k : ℚ) + 3) * (2 * (k : ℚ) + 2) ≠ 0 := by positivity
    exact sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left hn)

theorem coeff_odd_quotient (V : PowerSeries ℤ) (h1 : coeff 1 V = 1)
    (hODE : (4 - 27 * X ^ 2) * D (D V) - 27 * X * D V + 3 * V = 0) (k : ℕ) :
    coeff (2 * k + 1) V = (ternary k : ℤ) := by
  have hc := coeff_odd_rational V h1 hODE k
  have hq : (2 * (k : ℚ) + 1) * ((coeff (2 * k + 1) V : ℤ) : ℚ) =
      ((3 * k).choose k : ℚ) := by rw [hc]; exact q_mul_den k
  have hz : ((2 * k + 1 : ℕ) : ℤ) * coeff (2 * k + 1) V = ((3 * k).choose k : ℤ) := by
    exact_mod_cast hq
  have hn : ((2 * k + 1 : ℕ) : ℤ) ≠ 0 := by positivity
  change coeff (2 * k + 1) V = (((3 * k).choose k / (2 * k + 1) : ℕ) : ℤ)
  rw [Int.natCast_ediv, ← hz, Int.mul_ediv_cancel_left _ hn]

theorem eq_ternarySeries (V : PowerSeries ℤ) (h0 : constantCoeff V = 0) (h1 : coeff 1 V = 1)
    (hODE : (4 - 27 * X ^ 2) * D (D V) - 27 * X * D V + 3 * V = 0) : V = ternarySeries := by
  apply PowerSeries.ext
  intro n
  rcases Nat.even_or_odd n with hn | hn
  · obtain ⟨k, hk⟩ := hn
    have he : n = 2 * k := by omega
    rw [he]
    rw [coeff_even V h0 hODE k, ternarySeries, coeff_mk, ite_eq_right (by omega)]
  · obtain ⟨k, hk⟩ := hn
    have he : n = 2 * k + 1 := by omega
    rw [he]
    rw [coeff_odd_quotient V h1 hODE k, ternarySeries, coeff_mk,
      ite_eq_left (by omega), show (2 * k + 1) / 2 = k by omega]

theorem check_Rem11_ternaryReversion : Rem11_ternaryReversion := by
  obtain ⟨V, h0, h1, hV, hR, hL⟩ := exists_integral_reversion
  have he := eq_ternarySeries V h0 h1 (reversion_ode V h0 hV)
  unfold Rem11_ternaryReversion
  rw [← he]
  exact ⟨hV, hR, hL⟩

end BackfillPaper2.TernaryIdentification
#print axioms BackfillPaper2.TernaryIdentification.coeff_even
#print axioms BackfillPaper2.TernaryIdentification.coeff_odd_rational
#print axioms BackfillPaper2.TernaryIdentification.coeff_odd_quotient
#print axioms BackfillPaper2.TernaryIdentification.eq_ternarySeries
#print axioms BackfillPaper2.TernaryIdentification.check_Rem11_ternaryReversion
