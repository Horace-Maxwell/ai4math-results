import Research.Backfill.Paper2.Tools
import Research.Backfill.Paper2.CatalanCore
import Research.Backfill.Paper2.CFFamily

/-!
The five original equations reduce to the same normalized Catalan series.
Every substitution is justified from the original zero-constant hypotheses.
The A240998 argument allows both constant terms rather than imposing one.
-/
set_option autoImplicit false
noncomputable section
namespace BackfillPaper2.CatalanTransport
open PowerSeries BackfillPaper2.Challenge

private theorem constantCoeff_red (A : PowerSeries ℤ) :
    constantCoeff (red 2 A) = ((constantCoeff A : ℤ) : ZMod 2) := by
  change constantCoeff (PowerSeries.map (Int.castRingHom (ZMod 2)) A) =
    ((constantCoeff A : ℤ) : ZMod 2)
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff_apply]
  rfl

private theorem two_zero : (2 : PowerSeries (ZMod 2)) = 0 := by
  simpa only [map_ofNat, map_zero] using congrArg
    (C : ZMod 2 →+* PowerSeries (ZMod 2)) (show (2 : ZMod 2) = 0 by decide)

private theorem catalan_unique (F : PowerSeries (ZMod 2))
    (h0 : constantCoeff F = 0) (hF : F = X + F ^ 2) : F = red 2 catalanC := by
  have hG := congrArg (PowerSeries.map (Int.castRingHom (ZMod 2)))
    (show catalanC = X + catalanC ^ 2 from CatalanCore.check_CatalanEq)
  simp only [map_add, map_pow, map_X] at hG
  have hG0 : constantCoeff (red 2 catalanC) = 0 := by simp [red, catalanC]
  have hu : IsUnit (1 - F - red 2 catalanC) :=
    PowerSeries.isUnit_iff_constantCoeff.mpr (by simp [h0, hG0])
  have hz : (1 - F - red 2 catalanC) * (F - red 2 catalanC) = 0 := by
    change (1 - F - PowerSeries.map (Int.castRingHom (ZMod 2)) catalanC) *
      (F - PowerSeries.map (Int.castRingHom (ZMod 2)) catalanC) = 0
    linear_combination hF - hG
  exact sub_eq_zero.mp (hu.mul_right_eq_zero.mp hz)

private theorem reduce240998 (A : PowerSeries ℤ) (hA : Eq240998 A) :
    red 2 (A - C (constantCoeff A)) = red 2 catalanC := by
  let f : ℤ →+* ZMod 2 := Int.castRingHom (ZMod 2)
  have hx : red 2 ((X : PowerSeries ℤ) + 2 * X ^ 2) = X := by
    simp only [red, map_add, map_mul, map_pow, map_X, map_ofNat]
    rw [two_zero, zero_mul, add_zero]
  have hs := (Tools.check_Sec2_reduction 2 Nat.prime_two A
    ((X : PowerSeries ℤ) + 2 * X ^ 2) (by simp)).1
  rw [hx, X_subst] at hs
  have hm := congrArg (PowerSeries.map f) hA
  simp only [map_pow, map_add, map_X] at hm
  change (red 2 A) ^ 2 = X + red 2 (A.subst (X + 2 * X ^ 2)) at hm
  rw [hs] at hm
  let F := red 2 A
  let c : PowerSeries (ZMod 2) := C (constantCoeff F)
  have hcc : c ^ 2 = c := by
    have he : (constantCoeff F) ^ 2 = constantCoeff F :=
      (by decide : ∀ a : ZMod 2, a ^ 2 = a) (constantCoeff F)
    simpa only [map_pow] using congrArg (C : ZMod 2 →+* PowerSeries (ZMod 2)) he
  have hraw : F = X + F ^ 2 := by
    change F ^ 2 = X + F at hm
    linear_combination -hm - X * two_zero
  have hB : F - c = X + (F - c) ^ 2 := by
    linear_combination hraw - hcc + (F * c - c) * two_zero
  have hB0 : constantCoeff (F - c) = 0 := by simp [c]
  have h := catalan_unique (F - c) hB0 hB
  have hc0 : constantCoeff F = ((constantCoeff A : ℤ) : ZMod 2) := constantCoeff_red A
  have hnorm : red 2 (A - C (constantCoeff A)) = F - c := by
    change PowerSeries.map (Int.castRingHom (ZMod 2)) (A - C (constantCoeff A)) =
      F - C (constantCoeff F)
    rw [map_sub, PowerSeries.map_C]
    change F - C ((constantCoeff A : ℤ) : ZMod 2) = F - C (constantCoeff F)
    rw [hc0]
  exact hnorm.trans h

private theorem reduce295762 (A : PowerSeries ℤ) (h0 : constantCoeff A = 0)
    (hA : Eq295762 A) : red 2 A = red 2 catalanC := by
  have hc : constantCoeff (A.subst ((X : PowerSeries ℤ) ^ 2)) = 0 := by
    rw [constantCoeff_subst_X_pow two_ne_zero, h0]
    simp
  have hi : constantCoeff ((X : PowerSeries ℤ) - 2 * A.subst (X ^ 2)) = 0 := by
    simp [hc]
  have hx : red 2 ((X : PowerSeries ℤ) - 2 * A.subst (X ^ 2)) = X := by
    simp only [red, map_sub, map_mul, map_X, map_ofNat]
    rw [two_zero, zero_mul, sub_zero]
  have hs := (Tools.check_Sec2_reduction 2 Nat.prime_two A
    ((X : PowerSeries ℤ) - 2 * A.subst (X ^ 2)) hi).1
  rw [hx, X_subst] at hs
  have hs2 := (Tools.check_Sec2_reduction 2 Nat.prime_two A
    ((X : PowerSeries ℤ) ^ 2) (by simp)).1
  have hx2 : red 2 ((X : PowerSeries ℤ) ^ 2) = X ^ 2 := by simp [red]
  rw [hx2] at hs2
  have hm := congrArg (PowerSeries.map (Int.castRingHom (ZMod 2))) hA
  simp only [map_add, map_X] at hm
  change red 2 (A.subst (X - 2 * A.subst (X ^ 2))) =
    X + red 2 (A.subst (X ^ 2)) at hm
  rw [hs, hs2, ← Tools.check_Lemma1 2 Nat.prime_two] at hm
  exact catalan_unique (red 2 A) (by simp only [constantCoeff_red, h0, Int.cast_zero]) hm

private theorem reduce301933 (A : PowerSeries ℤ) (h0 : constantCoeff A = 0)
    (hA : Eq301933 A) : red 2 A = red 2 catalanC := by
  have hd := (Tools.check_Sec2_reduction 2 Nat.prime_two A 0 (by simp)).2
  have hm := congrArg (PowerSeries.map (Int.castRingHom (ZMod 2))) hA
  simp only [map_mul, map_add, map_one, map_ofNat, map_X] at hm
  change red 2 A * (1 + red 2 A * red 2 (derivative (R := ℤ) A)) =
    X * (1 + 4 * red 2 A * red 2 (derivative (R := ℤ) A)) at hm
  have h4 : (4 : PowerSeries (ZMod 2)) = 0 := by
    linear_combination (2 : PowerSeries (ZMod 2)) * two_zero
  rw [hd, h4, zero_mul, zero_mul, add_zero, mul_one] at hm
  exact CatalanCore.check_RC_A301933_determines (red 2 A) (by simp only [constantCoeff_red, h0, Int.cast_zero]) hm

private theorem cf_constant (e : ℕ) (A : PowerSeries ℤ) (T : ℕ → PowerSeries ℤ)
    (h : CF e A T) : constantCoeff A = 1 := by
  have hu : IsUnit (constantCoeff (T 0)) := by
    rcases h.1 0 with ht | ht <;> simp [ht]
  have he := congrArg constantCoeff h.2.1
  rw [map_mul, map_sub, map_one, constantCoeff_X] at he
  exact sub_eq_zero.mp (hu.mul_left_eq_zero.mp he)

private theorem reduceCF (e : ℕ) (he : 1 ≤ e) (A : PowerSeries ℤ)
    (T : ℕ → PowerSeries ℤ) (h : CF e A T) : red 2 (A - 1) = red 2 catalanC := by
  have ha0 := cf_constant e A T h
  have hF := CFFamily.check_RC_CFfamilyMod2 e he A T h
  have hB : red 2 A - 1 = X + (red 2 A - 1) ^ 2 := by
    linear_combination -hF + (red 2 A - 1 - X) * two_zero
  have h0 : constantCoeff (red 2 A - 1) = 0 := by
    rw [map_sub, map_one, constantCoeff_red, ha0, Int.cast_one, sub_self]
  simpa only [red, map_sub, map_one] using catalan_unique (red 2 A - 1) h0 hB

theorem check_RC_seriesMod2 : RC_seriesMod2 := by
  refine ⟨reduce295762, reduce301933, ?_, ?_, ?_⟩
  · intro A h0 hA
    simpa only [h0, map_one] using reduce240998 A hA
  · intro A T h
    exact reduceCF 3 (by omega) A T h
  · intro A T h
    exact reduceCF 4 (by omega) A T h

theorem check_RC_abstractMod2 : RC_abstractMod2 := by
  refine ⟨reduce240998, ?_, ?_, ?_, ?_⟩
  · intro A h0 hA
    simpa only [h0, map_zero, sub_zero] using reduce295762 A h0 hA
  · intro A h0 hA
    simpa only [h0, map_zero, sub_zero] using reduce301933 A h0 hA
  · intro A T h
    simpa only [cf_constant 3 A T h, map_one] using reduceCF 3 (by omega) A T h
  · intro A T h
    simpa only [cf_constant 4 A T h, map_one] using reduceCF 4 (by omega) A T h

private theorem coefficient_transport (A : PowerSeries ℤ)
    (h : red 2 (A - C (constantCoeff A)) = red 2 catalanC)
    (n : ℕ) (hn : 1 ≤ n) : coeff n A ≡ (catalan (n - 1) : ℤ) [ZMOD 2] := by
  have hcoeff := congrArg (coeff n) h
  simp only [red, coeff_map] at hcoeff
  have hA : coeff n (A - C (constantCoeff A)) = coeff n A := by
    simp only [map_sub, coeff_C, ite_eq_right (by omega : n ≠ 0), sub_zero]
  have hC : coeff n catalanC = (catalan (n - 1) : ℤ) := by
    cases n with
    | zero => omega
    | succ n => simp [catalanC, coeff_succ_X_mul, catalanSeries_coeff]
  rw [hA, hC] at hcoeff
  exact (ZMod.intCast_eq_intCast_iff _ _ 2).mp hcoeff

theorem check_RC_coeffMod2 : RC_coeffMod2 := by
  rcases check_RC_abstractMod2 with ⟨h1, h2, h3, h4, h5⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro A h n hn
    exact coefficient_transport A (h1 A h) n hn
  · intro A h0 h n hn
    exact coefficient_transport A (h2 A h0 h) n hn
  · intro A h0 h n hn
    exact coefficient_transport A (h3 A h0 h) n hn
  · intro A T h n hn
    exact coefficient_transport A (h4 A T h) n hn
  · intro A T h n hn
    exact coefficient_transport A (h5 A T h) n hn

end BackfillPaper2.CatalanTransport
#print axioms BackfillPaper2.CatalanTransport.check_RC_seriesMod2
#print axioms BackfillPaper2.CatalanTransport.check_RC_abstractMod2
#print axioms BackfillPaper2.CatalanTransport.check_RC_coeffMod2
