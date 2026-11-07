import Research.Backfill.Paper2.TernaryIdentification
import Research.Backfill.Paper2.Rem11Indexing

/-! Reduction of the fully identified integer ternary reversion modulo three. -/
set_option autoImplicit false
noncomputable section
namespace BackfillPaper2.Rem11Bridges
open PowerSeries BackfillPaper2.Challenge

private theorem index_iff (i : ℕ) :
    (∃ k : ℕ, 2 * i + 1 = 3 ^ k) ↔ ∃ k : ℕ, i = (3 ^ k - 1) / 2 := by
  constructor
  · rintro ⟨k, hk⟩
    exact ⟨k, by omega⟩
  · rintro ⟨k, hk⟩
    have ho : Odd (3 ^ k : ℕ) := Odd.pow (by decide : Odd (3 : ℕ))
    obtain ⟨j, hj⟩ := ho
    exact ⟨k, by omega⟩

private theorem coeff_ternary_odd (k : ℕ) :
    coeff (2 * k + 1) ternarySeries = (ternary k : ℤ) := by
  rw [ternarySeries, coeff_mk, ite_eq_left (by omega), show (2 * k + 1) / 2 = k by omega]

theorem reduced_ternary_eq_S : red 3 ternarySeries = EntryA361047.S := by
  let F : PowerSeries (ZMod 3) := red 3 ternarySeries
  let g : PowerSeries ℤ := X - X ^ 3
  have ht := TernaryIdentification.check_Rem11_ternaryReversion
  have ht0 : constantCoeff ternarySeries = 0 := by
    rw [← coeff_zero_eq_constantCoeff_apply]
    simp [ternarySeries]
  have hf0 : constantCoeff F = 0 := by
    change constantCoeff (PowerSeries.map (Int.castRingHom (ZMod 3)) ternarySeries) = 0
    rw [← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff_apply, ht0, map_zero]
  have he : F - F ^ 3 = X := by
    simpa only [F, red, map_sub, map_pow, map_X] using congrArg (red 3) ht.1
  have h3 : (3 : PowerSeries (ZMod 3)) = 0 := by
    simpa only [map_ofNat, map_zero] using
      congrArg (C : ZMod 3 →+* PowerSeries (ZMod 3)) (show (3 : ZMod 3) = 0 by decide)
  have hd : derivative (R := ZMod 3) F = 1 := by
    have hh := congrArg (derivative (R := ZMod 3)) he
    simp only [map_sub, derivative_pow, derivative_X, Nat.cast_ofNat, h3, zero_mul, sub_zero] at hh
    exact hh
  have hg0 : constantCoeff g = 0 := by simp [g]
  have hm : red 3 (ternarySeries.subst g) = (red 3 ternarySeries).subst (red 3 g) := by
    simpa only [red, PowerSeries.map] using
      (map_subst (h := Int.castRingHom (ZMod 3)) (HasSubst.of_constantCoeff_zero' hg0) ternarySeries)
  have hcomp : ternarySeries.subst g = X := ht.2.2
  have hx : red 3 (X : PowerSeries ℤ) = X := by simp [red]
  have hgm : red 3 g = (X : PowerSeries (ZMod 3)) - X ^ 3 := by simp [g, red]
  rw [hcomp, hx, hgm] at hm
  have hfg : F.subst ((X : PowerSeries (ZMod 3)) - X ^ 3) = X := hm.symm
  have hF : F.subst ((X : PowerSeries (ZMod 3)) - X ^ 3 * (derivative (R := ZMod 3) F) ^ 2) = X := by
    simpa only [hd, one_pow, mul_one] using hfg
  exact EntryA361047.residue F hf0 hF

theorem ternary_coeff_mod3 (m : ℕ) :
    ((∃ k : ℕ, m = 3 ^ k) → coeff m ternarySeries ≡ 1 [ZMOD 3]) ∧
    ((¬ ∃ k : ℕ, m = 3 ^ k) → coeff m ternarySeries ≡ 0 [ZMOD 3]) := by
  have hc := congrArg (coeff m) reduced_ternary_eq_S
  rw [coeff_map] at hc
  constructor
  · rintro ⟨k, rfl⟩
    rw [EntryA361047.coeff_S_pow] at hc
    exact_mod_cast (ZMod.intCast_eq_intCast_iff (coeff (3 ^ k) ternarySeries) 1 3).mp
      (by simpa only [Int.coe_castRingHom, Int.cast_one] using hc)
  · intro hm
    rw [EntryA361047.coeff_S_nonpow m (by intro k hk; exact hm ⟨k, hk⟩)] at hc
    exact_mod_cast (ZMod.intCast_eq_intCast_iff (coeff m ternarySeries) 0 3).mp
      (by simpa only [Int.coe_castRingHom, Int.cast_zero] using hc)

theorem check_Rem11_mod3 : Rem11_mod3 := by
  refine ⟨ternary_coeff_mod3, ?_⟩
  intro A h0 hA n hn
  have ha := EntryTheorems.check_Thm10 A h0 hA (2 * n - 1)
  have ht := ternary_coeff_mod3 (2 * n - 1)
  have hc : coeff (2 * n - 1) ternarySeries = (ternary (n - 1) : ℤ) := by
    rw [show 2 * n - 1 = 2 * (n - 1) + 1 by omega]
    exact coeff_ternary_odd (n - 1)
  by_cases hp : ∃ k : ℕ, 2 * n - 1 = 3 ^ k
  · have ha1 := ha.1 hp
    have ht1 := ht.1 hp
    rw [hc] at ht1
    exact ha1.trans ht1.symm
  · have ha0 := ha.2 hp
    have ht0 := ht.2 hp
    rw [hc] at ht0
    exact ha0.trans ht0.symm

theorem check_Rem11_A113047 : Rem11_A113047 := by
  intro k
  have ht := ternary_coeff_mod3 (2 * k + 1)
  rw [coeff_ternary_odd k] at ht
  constructor
  · intro hk
    exact ht.1 ((index_iff k).mpr hk)
  · intro hk
    exact ht.2 (by intro hp; exact hk ((index_iff k).mp hp))

end BackfillPaper2.Rem11Bridges
#print axioms BackfillPaper2.Rem11Bridges.reduced_ternary_eq_S
#print axioms BackfillPaper2.Rem11Bridges.ternary_coeff_mod3
#print axioms BackfillPaper2.Rem11Bridges.check_Rem11_mod3
#print axioms BackfillPaper2.Rem11Bridges.check_Rem11_A113047
