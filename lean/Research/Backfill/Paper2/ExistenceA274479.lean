import Research.Backfill.Paper2.IntegerHalf
import Research.Backfill.Paper2.Tools

/-! Frobenius proves the residual even over the integers before halving.
The original normalized equation gives a strict integral contraction after A=XB. -/
set_option autoImplicit false
noncomputable section
namespace BackfillPaper2.ExistenceA274479
open PowerSeries BackfillPaper2.Challenge BackfillPaper2.XadicFixedPoint
open BackfillPaper2.IntegerHalf

theorem check_EX_A274479 : EX_A274479 := by
  let D : PowerSeries ℤ := 1 - 2 * X - 4 * X ^ 2
  let E : PowerSeries ℤ := invOfUnit D 1
  let h : PowerSeries ℤ := X ^ 2 * E
  let δ : PowerSeries ℤ → PowerSeries ℤ := fun B => B ^ 2 - E * B.subst h
  let Φ : PowerSeries ℤ → PowerSeries ℤ := fun B => B - halve (δ B)
  let Ψ : (Unit → PowerSeries ℤ) → Unit → PowerSeries ℤ := fun B _ => Φ (B ())
  let seed : Unit → PowerSeries ℤ := fun _ => 1
  have hD : constantCoeff D = 1 := by simp [D]
  have hE : constantCoeff E = 1 := by simp [E, constantCoeff_invOfUnit]
  have hDE : D * E = 1 := mul_invOfUnit D 1 (by simpa using hD)
  have hh0 : constantCoeff h = 0 := by simp [h]
  have hs : HasSubst h := HasSubst.of_constantCoeff_zero' hh0
  have heven : ∀ B : PowerSeries ℤ, ∀ n, (2 : ℤ) ∣ coeff n (δ B) := by
    intro B n
    have h2 : (2 : PowerSeries (ZMod 2)) = 0 := by
      simpa only [map_ofNat, map_zero] using
        congrArg (C : ZMod 2 →+* PowerSeries (ZMod 2)) (show (2 : ZMod 2) = 0 by decide)
    have h4 : (4 : PowerSeries (ZMod 2)) = 0 := by linear_combination 2 * h2
    have hDr : red 2 D = 1 := by
      simp only [D, red, map_sub, map_one, map_mul, map_pow, map_X, map_ofNat, h2, h4,
        zero_mul, sub_zero]
    have hEr : red 2 E = 1 := by
      have he : red 2 D * red 2 E = 1 := by simpa only [red, map_mul, map_one] using congrArg (red 2) hDE
      simpa only [hDr, one_mul] using he
    have hhr : red 2 h = (X : PowerSeries (ZMod 2)) ^ 2 := by
      simp only [h, red, map_mul, map_pow, map_X, hEr, mul_one]
    have hm : red 2 (B.subst h) = (red 2 B).subst (red 2 h) := by
      simpa only [red, PowerSeries.map] using (map_subst (h := Int.castRingHom (ZMod 2)) hs B)
    have hf := Tools.check_Lemma1 2 Nat.prime_two (red 2 B)
    have hz : red 2 (δ B) = 0 := by
      have he : red 2 (δ B) = (red 2 B) ^ 2 - red 2 E * red 2 (B.subst h) := by
        simp only [δ, red, map_sub, map_pow, map_mul]
      rw [he, hEr, one_mul, hm, hhr, hf, sub_self]
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd (coeff n (δ B)) 2).mp
    simpa only [red, coeff_map, map_zero, Int.coe_castRingHom] using congrArg (coeff n) hz
  have hnorm : ∀ B : Unit → PowerSeries ℤ, Jet 1 B seed → constantCoeff (B ()) = 1 := by
    intro B hb
    simpa only [seed, coeff_zero_eq_constantCoeff_apply, map_one] using hb () 0 (by omega)
  have hδ0 : ∀ B, constantCoeff B = 1 → coeff 0 (δ B) = 0 := by
    intro B hb
    have hcomp : constantCoeff (B.subst h) = constantCoeff B :=
      constantCoeff_subst_of_constantCoeff_zero hh0 B
    simp [δ, coeff_zero_eq_constantCoeff_apply, hE, hb, hcomp]
  have hp : ∀ B, Jet 1 B seed → Jet 1 (Ψ B) seed := by
    intro B hb i j hj
    have : j = 0 := by omega
    subst j
    simp [Ψ, Φ, seed, halve, hδ0 _ (hnorm B hb),
      coeff_zero_eq_constantCoeff_apply, hnorm B hb]
  have hsubst : ∀ F G : PowerSeries ℤ, ∀ n, X ^ n ∣ F - G →
      X ^ (2 * n) ∣ F.subst h - G.subst h := by
    intro F G n hd
    obtain ⟨Q, hQ⟩ := hd
    rw [← subst_sub hs, hQ, subst_mul hs, subst_pow hs, subst_X hs]
    have hh : X ^ (2 * n) ∣ h ^ n := by
      dsimp only [h]
      rw [mul_pow, ← pow_mul]
      exact dvd_mul_right _ _
    exact dvd_mul_of_dvd_left hh _
  have hc : ∀ n, 1 ≤ n → ∀ B C, Jet 1 B seed → Jet 1 C seed →
      Jet n B C → Jet (n + 1) (Ψ B) (Ψ C) := by
    intro n hn B C hb hc hbc
    have hb0 := hnorm B hb
    have hc0 := hnorm C hc
    have hd : X ^ n ∣ B () - C () := by
      rw [X_pow_dvd_iff]
      intro j hj
      rw [map_sub, hbc () j hj, sub_self]
    have hs1 : (X : PowerSeries ℤ) ∣ B () + C () - 2 := by
      rw [X_dvd_iff]
      simp [hb0, hc0, map_ofNat]
    have hm : X ^ (n + 1) ∣ (B () - C ()) * (B () + C () - 2) := by
      rw [pow_succ]
      exact mul_dvd_mul hd hs1
    have hsub := hsubst (B ()) (C ()) n hd
    have hsub' : X ^ (n + 1) ∣ (B () - C ()).subst h := by
      rw [subst_sub hs]
      exact (pow_dvd_pow X (by omega : n + 1 ≤ 2 * n)).trans hsub
    have heq : δ (B ()) - δ (C ()) - 2 * (B () - C ()) =
        (B () - C ()) * (B () + C () - 2) - E * (B () - C ()).subst h := by
      rw [subst_sub hs]
      dsimp only [δ]; ring
    have ht : X ^ (n + 1) ∣ δ (B ()) - δ (C ()) - 2 * (B () - C ()) := by
      rw [heq]
      exact dvd_sub hm (dvd_mul_of_dvd_right hsub' _)
    have hbhalf := twice_halve (δ (B ())) (heven _)
    have hchalf := twice_halve (δ (C ())) (heven _)
    have heq2 : 2 * ((halve (δ (B ())) - halve (δ (C ()))) - (B () - C ())) =
        δ (B ()) - δ (C ()) - 2 * (B () - C ()) := by linear_combination hbhalf - hchalf
    have hh : X ^ (n + 1) ∣ (halve (δ (B ())) - halve (δ (C ()))) - (B () - C ()) := by
      apply precision_cancel_two
      rw [heq2]
      exact ht
    have hΦ : Φ (B ()) - Φ (C ()) = -((halve (δ (B ())) - halve (δ (C ()))) - (B () - C ())) := by
      dsimp only [Φ]; ring
    have hv : X ^ (n + 1) ∣ Φ (B ()) - Φ (C ()) := by rw [hΦ]; exact dvd_neg.mpr hh
    rw [X_pow_dvd_iff] at hv
    intro i j hj
    have hz := hv j hj
    rw [map_sub, sub_eq_zero] at hz
    exact hz
  obtain ⟨B, ⟨hb, hfix⟩, huniq⟩ := existsUnique_fixed_seed 1 seed Ψ hp hc
  have hb0 := hnorm B hb
  have hΦ : Φ (B ()) = B () := congrFun hfix ()
  have hhalf : halve (δ (B ())) = 0 := by dsimp only [Φ] at hΦ; linear_combination -hΦ
  have hδ : δ (B ()) = 0 := by
    have he := twice_halve (δ (B ())) (heven _)
    rw [hhalf, mul_zero] at he
    exact he.symm
  let A : PowerSeries ℤ := X * B ()
  have ha0 : constantCoeff A = 0 := by simp [A]
  have ha1 : coeff 1 A = 1 := by
    change coeff (0 + 1) (X * B ()) = 1
    rw [coeff_succ_X_mul, coeff_zero_eq_constantCoeff_apply, hb0]
  have hA : Eq274479 A := by
    change A ^ 2 = PowerSeries.subst h A
    change (X * B ()) ^ 2 = (X * B ()).subst h
    rw [subst_mul hs, subst_X hs]
    dsimp only [h]
    dsimp only [δ] at hδ
    linear_combination X ^ 2 * hδ
  refine ⟨A, ⟨ha0, ha1, hA⟩, ?_⟩
  rintro F ⟨hf0, hf1, hf⟩
  obtain ⟨Q, hQ⟩ : (X : PowerSeries ℤ) ∣ F := X_dvd_iff.mpr hf0
  have hq0 : constantCoeff Q = 1 := by
    have he := congrArg (coeff 1) hQ
    rw [hf1, show (1 : ℕ) = 0 + 1 from rfl, coeff_succ_X_mul,
      coeff_zero_eq_constantCoeff_apply] at he
    exact he.symm
  have hqδ : δ Q = 0 := by
    change F ^ 2 = PowerSeries.subst h F at hf
    rw [hQ, subst_mul hs, subst_X hs] at hf
    have he : X ^ 2 * δ Q = 0 := by
      dsimp only [δ]
      dsimp only [h] at hf
      linear_combination hf
    exact (mul_eq_zero.mp he).resolve_left (pow_ne_zero 2 (X_ne_zero (R := ℤ)))
  let G : Unit → PowerSeries ℤ := fun _ => Q
  have hgn : Jet 1 G seed := by
    intro i j hj
    have : j = 0 := by omega
    subst j
    simpa only [G, seed, coeff_zero_eq_constantCoeff_apply, map_one] using hq0
  have hgf : Ψ G = G := by
    funext i
    change Q - halve (δ Q) = Q
    rw [hqδ, halve_zero, sub_zero]
  have heq : Q = B () := congrFun (huniq G ⟨hgn, hgf⟩) ()
  rw [hQ, heq]

end BackfillPaper2.ExistenceA274479
#print axioms BackfillPaper2.ExistenceA274479.check_EX_A274479
