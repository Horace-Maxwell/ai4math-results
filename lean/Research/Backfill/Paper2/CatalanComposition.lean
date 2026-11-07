import Research.Backfill.Paper2.Tools
import Research.Backfill.Paper2.CatalanCore

/-!
A273958: exact Catalan-composition closed form, its reduction, and complete
quartic indicator. The original equation forces the Catalan constant to zero;
no normalization or existence hypothesis is added to the frozen statements.
-/
set_option autoImplicit false
noncomputable section
namespace BackfillPaper2.CatalanComposition
open PowerSeries BackfillPaper2.Challenge
local notation "K" => ZMod 2

private theorem constant_zero (Cs A : PowerSeries ℤ) (h : Eq273958 Cs A) :
    constantCoeff Cs = 0 := by
  have hz : constantCoeff Cs ^ 2 = 0 := by
    rw [← map_pow, ← h.2]
    simp
  exact (pow_eq_zero_iff two_ne_zero).mp hz

private theorem canonical (Cs A : PowerSeries ℤ) (h : Eq273958 Cs A) : Cs = catalanC := by
  have h0 := constant_zero Cs A h
  have hc0 : constantCoeff catalanC = 0 := by simp [catalanC]
  have hu : IsUnit (1 - Cs - catalanC) :=
    PowerSeries.isUnit_iff_constantCoeff.mpr (by simp [h0, hc0])
  have hc : catalanC = X + catalanC ^ 2 := CatalanCore.check_CatalanEq
  have hz : (1 - Cs - catalanC) * (Cs - catalanC) = 0 := by
    linear_combination h.1 - hc
  exact sub_eq_zero.mp (hu.mul_right_eq_zero.mp hz)

theorem check_RC_A273958_closedForm : RC_A273958_closedForm := by
  intro Cs A h
  have hc0 := constant_zero Cs A h
  have hi0 : constantCoeff (-(Cs ^ 2)) = 0 := by simp [hc0]
  have hs : HasSubst (-(Cs ^ 2)) := HasSubst.of_constantCoeff_zero' hi0
  let U : PowerSeries ℤ := X * A
  let V := -(Cs.subst (-(Cs ^ 2)))
  have hu0 : constantCoeff U = 0 := by simp [U]
  have hv0 : constantCoeff V = 0 := by
    have hsub0 : constantCoeff (Cs.subst (-(Cs ^ 2))) = 0 :=
      constantCoeff_subst_eq_zero hi0 Cs hc0
    dsimp only [V]
    rw [map_neg, hsub0, neg_zero]
  have hu : U + U ^ 2 = Cs ^ 2 := by simpa only [U, mul_pow] using h.2
  have hsub := congrArg (fun F : PowerSeries ℤ => F.subst (-(Cs ^ 2))) h.1
  rw [subst_add hs, subst_X hs, subst_pow hs] at hsub
  have hv : V + V ^ 2 = Cs ^ 2 := by dsimp [V]; linear_combination -hsub
  have hunit : IsUnit (1 + U + V) :=
    PowerSeries.isUnit_iff_constantCoeff.mpr (by simp [hu0, hv0])
  have hz : (1 + U + V) * (U - V) = 0 := by linear_combination hu - hv
  exact sub_eq_zero.mp (hunit.mul_right_eq_zero.mp hz)

private theorem two_zero : (2 : PowerSeries K) = 0 := by
  simpa only [map_ofNat, map_zero] using
    congrArg (C : K →+* PowerSeries K) (show (2 : K) = 0 by decide)

private theorem neg_self (F : PowerSeries K) : -F = F := by
  linear_combination (-F) * two_zero

theorem check_RC_A273958_mod2 : RC_A273958_mod2 := by
  intro Cs A h
  have hc0 := constant_zero Cs A h
  have hi0 : constantCoeff (-(Cs ^ 2)) = 0 := by simp [hc0]
  have hs : HasSubst (-(Cs ^ 2)) := HasSubst.of_constantCoeff_zero' hi0
  have he := congrArg (PowerSeries.map (Int.castRingHom K))
    (check_RC_A273958_closedForm Cs A h)
  rw [map_neg] at he
  change red 2 (X * A) = -(red 2 (Cs.subst (-(Cs ^ 2)))) at he
  have hm : red 2 (Cs.subst (-(Cs ^ 2))) = (red 2 Cs).subst (red 2 (-(Cs ^ 2))) := by
    simpa only [red, PowerSeries.map] using
      (PowerSeries.map_subst (h := Int.castRingHom K) hs Cs)
  rw [hm] at he
  simp only [red, map_neg, map_pow] at he
  change red 2 (X * A) = -((red 2 Cs).subst (-((red 2 Cs) ^ 2))) at he
  rw [neg_self ((red 2 Cs) ^ 2), neg_self] at he
  rw [he, Tools.check_Lemma1 2 Nat.prime_two (red 2 Cs)]

private theorem fourth_expand (F : PowerSeries K) :
    F ^ 4 = expand 4 (by decide) F := by
  have hs (G : PowerSeries K) : G ^ 2 = expand 2 two_ne_zero G := by
    simpa only [expand_apply] using Tools.check_Lemma1 2 Nat.prime_two G
  calc
    F ^ 4 = (F ^ 2) ^ 2 := by ring
    _ = expand 2 two_ne_zero (expand 2 two_ne_zero F) := by rw [hs, hs]
    _ = expand 4 (by decide) F := (expand_mul 2 two_ne_zero 2 two_ne_zero F).symm

private theorem quartic_coeff (H : PowerSeries K) (h0 : constantCoeff H = 0)
    (hH : H = X + H ^ 4) : ∀ n : ℕ, coeff n H = 1 ↔ ∃ k, n = 4 ^ k := by
  have hr (n : ℕ) : coeff n H = (if n = 1 then 1 else 0) +
      (if 4 ∣ n then coeff (n / 4) H else 0) := by
    have he := congrArg (coeff n) hH
    rw [fourth_expand, map_add, coeff_X, coeff_expand] at he
    exact he
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    by_cases hn0 : n = 0
    · subst n
      rw [coeff_zero_eq_constantCoeff_apply, h0]
      constructor
      · intro he; exact False.elim ((by decide : (0 : K) ≠ 1) he)
      · rintro ⟨k, hk⟩
        have hp : 0 < 4 ^ k := pow_pos (by decide) k
        omega
    by_cases hn1 : n = 1
    · subst n
      constructor
      · intro _; exact ⟨0, rfl⟩
      · intro _; rw [hr]; norm_num
    by_cases hd : 4 ∣ n
    · rw [hr, ite_eq_right hn1, ite_eq_left hd, zero_add,
        ih (n / 4) (Nat.div_lt_self (Nat.pos_of_ne_zero hn0) (by decide))]
      constructor
      · rintro ⟨k, hk⟩
        refine ⟨k + 1, ?_⟩
        calc
          n = 4 * (n / 4) := (Nat.mul_div_cancel' hd).symm
          _ = 4 * 4 ^ k := by rw [hk]
          _ = 4 ^ (k + 1) := by ring
      · rintro ⟨k, hk⟩
        cases k with
        | zero => exact False.elim (hn1 (by simpa using hk))
        | succ k =>
          refine ⟨k, ?_⟩
          have he : n = 4 * 4 ^ k := by rw [hk, pow_succ]; ring
          rw [he, Nat.mul_div_cancel_left _ (by decide : 0 < 4)]
    · rw [hr, ite_eq_right hn1, ite_eq_right hd, add_zero]
      constructor
      · intro he; exact False.elim ((by decide : (0 : K) ≠ 1) he)
      · rintro ⟨k, hk⟩
        cases k with
        | zero => exact False.elim (hn1 (by simpa using hk))
        | succ k =>
          exact False.elim (hd (by rw [hk]; exact dvd_pow_self 4 (by omega)))

theorem check_RC_CCmod2 : RC_CCmod2 := by
  let c := red 2 catalanC
  have hc0 : constantCoeff c = 0 := by simp [c, red, catalanC]
  have hc : c = X + c ^ 2 := by
    have he := congrArg (PowerSeries.map (Int.castRingHom K))
      (show catalanC = X + catalanC ^ 2 from CatalanCore.check_CatalanEq)
    simpa only [map_add, map_X, map_pow] using he
  have hs : HasSubst c := HasSubst.of_constantCoeff_zero' hc0
  let H := c.subst c
  have hH0 : constantCoeff H = 0 := constantCoeff_subst_eq_zero hc0 c hc0
  have he := congrArg (fun F : PowerSeries K => F.subst c) hc
  rw [subst_add hs, subst_X hs, subst_pow hs] at he
  change H = c + H ^ 2 at he
  have hd : c = H + H ^ 2 := by linear_combination -he - H ^ 2 * two_zero
  have hsq := congrArg (fun F : PowerSeries K => F ^ 2) hd
  have hH : H = X + H ^ 4 := by
    linear_combination hc - hd + hsq + H ^ 3 * two_zero
  exact quartic_coeff H hH0 hH

private theorem shifted_parity (Cs A : PowerSeries ℤ) (h : Eq273958 Cs A) (n : ℕ) :
    Odd (coeff n A) ↔ ∃ k, n + 1 = 2 * 4 ^ k := by
  have hcanon := canonical Cs A h
  subst Cs
  let c := red 2 catalanC
  have hc0 : constantCoeff c = 0 := by simp [c, red, catalanC]
  have hs : HasSubst c := HasSubst.of_constantCoeff_zero' hc0
  have he : red 2 (X * A) = expand 2 two_ne_zero (c.subst c) := by
    rw [expand_apply, subst_comp_subst_apply hs (HasSubst.X_pow two_ne_zero)]
    exact check_RC_A273958_mod2 catalanC A h
  rw [← ZMod.intCast_eq_one_iff_odd]
  have hcoef : ((coeff n A : ℤ) : K) = coeff (n + 1) (red 2 (X * A)) := by
    simp [red, coeff_succ_X_mul]
  rw [hcoef, he, coeff_expand]
  split_ifs with hd
  · rw [check_RC_CCmod2]
    constructor
    · rintro ⟨k, hk⟩
      refine ⟨k, ?_⟩
      calc
        n + 1 = 2 * ((n + 1) / 2) := (Nat.mul_div_cancel' hd).symm
        _ = 2 * 4 ^ k := by rw [hk]
    · rintro ⟨k, hk⟩
      exact ⟨k, by rw [hk, Nat.mul_div_cancel_left _ (by decide : 0 < 2)]⟩
  · constructor
    · intro he; exact False.elim ((by decide : (0 : K) ≠ 1) he)
    · rintro ⟨k, hk⟩
      exact False.elim (hd ⟨4 ^ k, hk⟩)

theorem check_Thm5_A273958 : Thm5_A273958 := by
  intro Cs A h n
  rw [shifted_parity Cs A h n]
  constructor
  · rintro ⟨k, hk⟩
    exact ⟨k, by omega⟩
  · rintro ⟨k, hk⟩
    have hp : 1 ≤ 4 ^ k := Nat.one_le_pow _ _ (by decide)
    exact ⟨k, by omega⟩

theorem check_Sec7_quotedA273958 : Sec7_quotedA273958 := by
  intro Cs A hc hA n
  exact shifted_parity Cs A ⟨hc, hA⟩ n

end BackfillPaper2.CatalanComposition
#print axioms BackfillPaper2.CatalanComposition.check_RC_A273958_closedForm
#print axioms BackfillPaper2.CatalanComposition.check_RC_A273958_mod2
#print axioms BackfillPaper2.CatalanComposition.check_RC_CCmod2
#print axioms BackfillPaper2.CatalanComposition.check_Thm5_A273958
#print axioms BackfillPaper2.CatalanComposition.check_Sec7_quotedA273958
