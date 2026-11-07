import Research.Backfill.Paper2.Challenge

/-!
Paper 2 backfill, blueprint section 3.1: general tools.
Statements are the independently reviewed frozen 84-statement contract of 2026-11-05.
The fixed-series argument generalizes the already published Oeis389472Mod3 private
argument to the actual arbitrary-field/arbitrary-substitution statement. Frobenius
uses Mathlib's map/expand theorem. No existence or sequence identification is assumed.
-/
set_option autoImplicit false
universe u
noncomputable section
namespace BackfillPaper2.Tools
open PowerSeries BackfillPaper2.Challenge

/-- Reduction commutes with substitution and formal differentiation. -/
theorem check_Sec2_reduction : Sec2_reduction := by
  intro p _ A h hc
  constructor
  · simpa only [red, PowerSeries.map] using
      (PowerSeries.map_subst (h := Int.castRingHom (ZMod p))
        (HasSubst.of_constantCoeff_zero' hc) A)
  · ext n
    simp [red, coeff_derivative]

/-- Frobenius for an arbitrary prime, with the original substitution conclusion. -/
theorem check_Lemma1 : Lemma1 := by
  intro p hp F
  let : Fact p.Prime := ⟨hp⟩
  have he : F ^ p = expand p hp.ne_zero F := by
    have h := MvPowerSeries.map_frobenius_expand (R := ZMod p) (σ := Unit)
      p hp.ne_zero (f := F)
    rw [ZMod.frobenius_zmod] at h
    rw [← h]
    simp [MvPowerSeries.map_id]
    rfl
  simpa only [expand_apply] using he

/-- An order-at-least-two substitution has no nonconstant fixed series. -/
theorem check_Lemma2 : Lemma2.{u} := by
  intro K _ h H hc horder hf
  have hs : HasSubst h := HasSubst.of_constantCoeff_zero' hc
  let E := H - C (constantCoeff H)
  have hE0 : constantCoeff E = 0 := by simp [E]
  have hE : E.subst h = E := by
    simp only [E, subst_sub hs, subst_C, hf]
    rfl
  by_contra hne
  have hEn : E ≠ 0 := sub_ne_zero.mpr hne
  have hn := coe_toNat_order hEn
  have hpos := one_le_order_iff_constCoeff_eq_zero.mpr hE0
  have hbound := le_order_subst h hs E
  change MvPowerSeries.order h * PowerSeries.order E ≤
    MvPowerSeries.order (E.subst h) at hbound
  rw [PowerSeries.order_eq_order] at horder
  have hh : (2 : ENat) * PowerSeries.order E ≤ PowerSeries.order E := by
    have ht := (mul_le_mul_of_nonneg_right horder
      (show 0 ≤ PowerSeries.order E from zero_le)).trans hbound
    simpa only [← PowerSeries.order_eq_order, hE] using ht
  rw [← hn] at hh hpos
  have ha : 2 * (PowerSeries.order E).toNat ≤ (PowerSeries.order E).toNat := by
    exact_mod_cast hh
  have hb : 1 ≤ (PowerSeries.order E).toNat := by exact_mod_cast hpos
  omega

/-- Divisibility by successively all powers forces every coefficient to vanish. -/
theorem check_ObsXadic : ObsXadic := by
  intro p _ D n₀ hbase hstep
  have hd : ∀ n : ℕ, (X : PowerSeries (ZMod p)) ^ (n₀ + n) ∣ D := by
    intro n
    induction n with
    | zero => simpa using hbase
    | succ n ih =>
      simpa [Nat.add_assoc] using hstep (n₀ + n) (by omega) ih
  apply PowerSeries.ext
  intro n
  simpa using (X_pow_dvd_iff.mp (hd (n + 1)) n (by omega))

#print axioms BackfillPaper2.Tools.check_Sec2_reduction
#print axioms BackfillPaper2.Tools.check_Lemma1
#print axioms BackfillPaper2.Tools.check_Lemma2
#print axioms BackfillPaper2.Tools.check_ObsXadic
end BackfillPaper2.Tools
