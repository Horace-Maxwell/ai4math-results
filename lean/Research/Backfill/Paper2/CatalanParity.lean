import Research.Backfill.Paper2.Tools
import Research.Backfill.Paper2.CatalanCore

/-!
Paper 2: original dyadic recursion and Catalan parity contracts.
Dyadic coefficient induction is transported from the published HannaA301933
source, with no import of old project theorems. The index shift is proved here.
-/
set_option autoImplicit false
noncomputable section
namespace BackfillPaper2.CatalanParity
open PowerSeries BackfillPaper2.Challenge
local notation "K" => ZMod 2

private theorem sq_eq_expand (F : PowerSeries K) : F ^ 2 = expand 2 two_ne_zero F := by
  simpa only [expand_apply] using Tools.check_Lemma1 2 Nat.prime_two F

/-- `c = X + c^2` with `c(0) = 0` forces `c` to be the indicator of the powers of two. -/
private theorem dyadic_coefficients (c : PowerSeries K) (hc0 : constantCoeff c = 0) (hc : c = X + c ^ 2) :
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
      · rw [hrec, ite_eq_right (show ¬ 2 * m = 1 by omega), ite_eq_left (dvd_mul_right 2 m),
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
    · rw [hrec, ite_eq_right (show ¬ 2 ∣ 2 * m + 1 by omega)]
      by_cases hm : m = 0
      · subst hm
        refine ⟨fun _ => ⟨0, by norm_num⟩, fun _ => by norm_num⟩
      · rw [ite_eq_right (show ¬ 2 * m + 1 = 1 by omega), add_zero]
        constructor
        · intro h
          exact absurd h (by decide)
        · rintro ⟨k, hk⟩
          cases k with
          | zero => rw [pow_zero] at hk; omega
          | succ k =>
            rw [pow_succ] at hk
            omega

theorem check_Lemma3 : Lemma3 := by
  intro F h0 hF n _
  exact dyadic_coefficients F h0 hF n

theorem check_RC_catalanParity : RC_catalanParity := by
  intro n
  have hC := congrArg (PowerSeries.map (Int.castRingHom (ZMod 2)))
    (show catalanC = X + catalanC ^ 2 from CatalanCore.check_CatalanEq)
  simp only [map_add, map_pow, map_X] at hC
  have hC0 : constantCoeff (red 2 catalanC) = 0 := by simp [red, catalanC]
  have h := check_Lemma3 (red 2 catalanC) hC0 hC (n + 1) (by omega)
  have hc : coeff (n + 1) (red 2 catalanC) = (catalan n : ZMod 2) := by
    simp [red, catalanC, coeff_succ_X_mul, catalanSeries_coeff]
  rw [hc, ZMod.natCast_eq_one_iff_odd] at h
  rw [h]
  constructor
  · rintro ⟨k, hk⟩
    exact ⟨k, by omega⟩
  · rintro ⟨k, hk⟩
    have hp : 0 < 2 ^ k := pow_pos two_pos k
    exact ⟨k, by omega⟩

end BackfillPaper2.CatalanParity
#print axioms BackfillPaper2.CatalanParity.check_Lemma3
#print axioms BackfillPaper2.CatalanParity.check_RC_catalanParity
