import Research.Backfill.Paper2.CompositionLinearization
import Research.Backfill.Paper2.IntegerHalf

/-! Construct A=X+2B; evenness is derived before coefficientwise halving.
Uniqueness compares arbitrary normalized integral solutions, with no parity assumption. -/
set_option autoImplicit false
noncomputable section
namespace BackfillPaper2.ExistenceA107099
open PowerSeries BackfillPaper2.Challenge BackfillPaper2.XadicFixedPoint
open BackfillPaper2.IntegerHalf

theorem check_EX_A107099 : EX_A107099 := by
  let h : PowerSeries ℤ → PowerSeries ℤ := fun B => X + 2 * B
  let δ : PowerSeries ℤ → PowerSeries ℤ := fun B => B.subst (h B) - B
  let Φ : PowerSeries ℤ → PowerSeries ℤ := fun B => X ^ 3 - halve (δ B)
  let Ψ : (Unit → PowerSeries ℤ) → Unit → PowerSeries ℤ := fun B _ => Φ (B ())
  let seed : Unit → PowerSeries ℤ := fun _ => 0
  have norm0 : ∀ B : Unit → PowerSeries ℤ, Jet 2 B seed → constantCoeff (B ()) = 0 := by
    intro B hb
    simpa only [seed, coeff_zero_eq_constantCoeff_apply, map_zero] using hb () 0 (by omega)
  have norm1 : ∀ B : Unit → PowerSeries ℤ, Jet 2 B seed → coeff 1 (B ()) = 0 := by
    intro B hb
    simpa only [seed, map_zero] using hb () 1 (by omega)
  have hzero : ∀ B, constantCoeff B = 0 → constantCoeff (h B) = 0 := by
    intro B hb; simp [h, hb]
  have hone : ∀ B, coeff 1 B = 0 → coeff 1 (h B) = 1 := by
    intro B hb; simp [h, hb]
  have evenδ : ∀ B, constantCoeff B = 0 → ∀ n, (2 : ℤ) ∣ coeff n (δ B) := by
    intro B hb n
    have hred : red 2 (h B) = (X : PowerSeries (ZMod 2)) := by
      have ht : (2 : PowerSeries (ZMod 2)) = 0 := by
        simpa only [map_ofNat, map_zero] using
          congrArg (C : ZMod 2 →+* PowerSeries (ZMod 2)) (show (2 : ZMod 2) = 0 by decide)
      simp only [h, red, map_add, map_mul, map_ofNat, map_X, ht, zero_mul, add_zero]
    have hm : red 2 (B.subst (h B)) = (red 2 B).subst (red 2 (h B)) := by
      simpa only [red, PowerSeries.map] using
        (map_subst (h := Int.castRingHom (ZMod 2)) (HasSubst.of_constantCoeff_zero' (hzero B hb)) B)
    have he : red 2 (δ B) = 0 := by
      have hd : red 2 (δ B) = red 2 (B.subst (h B)) - red 2 B := by simp only [δ, red, map_sub]
      rw [hd, hm, hred, X_subst, sub_self]
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd (coeff n (δ B)) 2).mp
    simpa only [red, coeff_map, map_zero, Int.coe_castRingHom] using congrArg (coeff n) he
  have δlow : ∀ B, constantCoeff B = 0 → coeff 1 B = 0 →
      coeff 0 (δ B) = 0 ∧ coeff 1 (δ B) = 0 := by
    intro B hb0 hb1
    constructor
    · have hcomp0 : constantCoeff (B.subst (h B)) = 0 :=
        constantCoeff_subst_eq_zero (hzero B hb0) B hb0
      change coeff 0 (B.subst (h B) - B) = 0
      simp only [map_sub, coeff_zero_eq_constantCoeff_apply, hcomp0, hb0, sub_self]
    · change coeff 1 (B.subst (h B) - B) = 0
      rw [map_sub, FiniteCoefficients.coeff_subst_range B (h B) (hzero B hb0) 1]
      simp [Finset.sum_range_succ, hb1]
  have hp : ∀ B, Jet 2 B seed → Jet 2 (Ψ B) seed := by
    intro B hb i j hj
    have hl := δlow (B ()) (norm0 B hb) (norm1 B hb)
    interval_cases j <;> simp [Ψ, Φ, seed, halve, coeff_X_pow, hl.1, hl.2]
  have hc : ∀ n, 2 ≤ n → ∀ B C, Jet 2 B seed → Jet 2 C seed →
      Jet n B C → Jet (n + 1) (Ψ B) (Ψ C) := by
    intro n hn B C hb hc hbc
    have hb0 := norm0 B hb
    have hc0 := norm0 C hc
    have hb1 := norm1 B hb
    have hc1 := norm1 C hc
    have hd : X ^ n ∣ B () - C () := by
      rw [X_pow_dvd_iff]
      intro j hj
      rw [map_sub, hbc () j hj, sub_self]
    have hnear := XadicAlgebra.subst_near_id (B () - C ()) (h (B ())) (hzero _ hb0) (hone _ hb1) n hd
    have hh : X ^ n ∣ h (B ()) - h (C ()) := by
      have he : h (B ()) - h (C ()) = 2 * (B () - C ()) := by dsimp only [h]; ring
      rw [he]
      exact dvd_mul_of_dvd_right hd _
    have hin := CompositionLinearization.inner_difference (C ()) (h (B ())) (h (C ()))
      (hzero _ hb0) (hzero _ hc0) n (by omega) hh
    rw [hc1, map_zero, zero_mul, sub_zero] at hin
    have he : δ (B ()) - δ (C ()) =
        ((B () - C ()).subst (h (B ())) - (B () - C ())) +
          ((C ()).subst (h (B ())) - (C ()).subst (h (C ()))) := by
      rw [subst_sub (HasSubst.of_constantCoeff_zero' (hzero _ hb0))]
      dsimp only [δ]; ring
    have ht : X ^ (n + 1) ∣ δ (B ()) - δ (C ()) := by rw [he]; exact dvd_add hnear hin
    have hh := precision_halve (δ (B ())) (δ (C ())) (n + 1) ht
    have heq : Φ (B ()) - Φ (C ()) = -(halve (δ (B ())) - halve (δ (C ()))) := by dsimp only [Φ]; ring
    have hv : X ^ (n + 1) ∣ Φ (B ()) - Φ (C ()) := by rw [heq]; exact dvd_neg.mpr hh
    rw [X_pow_dvd_iff] at hv
    intro i j hj
    have hz := hv j hj
    rw [map_sub, sub_eq_zero] at hz
    exact hz
  obtain ⟨B, ⟨hb, hfix⟩, _⟩ := existsUnique_fixed_seed 2 seed Ψ hp hc
  have hb0 := norm0 B hb
  have hb1 := norm1 B hb
  let A : PowerSeries ℤ := h (B ())
  have ha0 : constantCoeff A = 0 := hzero _ hb0
  have ha1 : coeff 1 A = 1 := hone _ hb1
  have he : Φ (B ()) = B () := congrFun hfix ()
  have hδ := twice_halve (δ (B ())) (evenδ (B ()) hb0)
  have hbEq : B () + (B ()).subst A = 2 * X ^ 3 := by
    dsimp only [Φ] at he
    dsimp only [δ] at hδ
    change B () + (B ()).subst (h (B ())) = 2 * X ^ 3
    linear_combination -2 * he - hδ
  have hA : Eq107099 A := by
    change PowerSeries.subst A A = X + 4 * X ^ 3
    have hs := HasSubst.of_constantCoeff_zero' ha0
    have hx : A.subst A = A + 2 * (B ()).subst A := by
      change (X + 2 * B ()).subst A = A + 2 * (B ()).subst A
      have h2 : (2 : PowerSeries ℤ).subst A = 2 := by
        change (C (2 : ℤ)).subst A = MvPowerSeries.C (2 : ℤ)
        exact subst_C _
      rw [subst_add hs, subst_mul hs, subst_X hs, h2]
    rw [hx]
    dsimp only [A, h]
    change X + 2 * B () + 2 * (B ()).subst (h (B ())) = X + 4 * X ^ 3
    change B () + (B ()).subst (h (B ())) = 2 * X ^ 3 at hbEq
    linear_combination 2 * hbEq
  refine ⟨A, ⟨ha0, ha1, hA⟩, ?_⟩
  rintro F ⟨hf0, hf1, hf⟩
  apply PowerSeries.ext
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn0 : n = 0
    · subst n
      simp only [coeff_zero_eq_constantCoeff_apply, hf0, ha0]
    have hd : X ^ n ∣ F - A := by
      rw [X_pow_dvd_iff]
      intro j hj
      rw [map_sub, ih j hj, sub_self]
    have ht := CompositionLinearization.self_difference F A hf0 ha0 hf1 ha1 n (by omega) hd
    have hz := X_pow_dvd_iff.mp ht n (by omega)
    change F.subst F = X + 4 * X ^ 3 at hf
    change A.subst A = X + 4 * X ^ 3 at hA
    rw [hf, hA, sub_self, zero_sub, map_neg, coeff_ofNat_mul, map_sub] at hz
    omega

end BackfillPaper2.ExistenceA107099
#print axioms BackfillPaper2.ExistenceA107099.check_EX_A107099
