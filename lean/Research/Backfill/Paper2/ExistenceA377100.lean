import Research.Backfill.Paper2.FiniteCoefficients

/-! Factoring A=XB gives an integral contraction with constant B(0)=1. -/
set_option autoImplicit false
noncomputable section
namespace BackfillPaper2.ExistenceA377100
open PowerSeries BackfillPaper2.Challenge BackfillPaper2.XadicFixedPoint

private theorem power_subst_dvd (F G : PowerSeries ℤ) (n k : ℕ) (hk : k ≠ 0)
    (hd : X ^ n ∣ F - G) : X ^ (k * n) ∣ F.subst ((X : PowerSeries ℤ) ^ k) - G.subst ((X : PowerSeries ℤ) ^ k) := by
  have hs := HasSubst.X_pow (R := ℤ) hk
  obtain ⟨Q, hQ⟩ := hd
  rw [← subst_sub hs, hQ, subst_mul hs, subst_pow hs, subst_X hs, ← pow_mul]
  exact dvd_mul_right _ _

theorem check_EX_A377100 : EX_A377100 := by
  let seed : Unit → PowerSeries ℤ := fun _ => 1
  let Φ : PowerSeries ℤ → PowerSeries ℤ := fun B =>
    B.subst (X ^ 3) - B * (B.subst (X ^ 2) - 1) + X * B ^ 2 * B.subst (X ^ 2)
  let Ψ : (Unit → PowerSeries ℤ) → Unit → PowerSeries ℤ := fun B _ => Φ (B ())
  have hc0 : ∀ B : Unit → PowerSeries ℤ, Jet 1 B seed → constantCoeff (B ()) = 1 := by
    intro B hb
    simpa only [seed, coeff_zero_eq_constantCoeff_apply, map_one] using hb () 0 (by omega)
  have hp : ∀ B, Jet 1 B seed → Jet 1 (Ψ B) seed := by
    intro B hb i j hj
    have : j = 0 := by omega
    subst j
    simp [Ψ, Φ, seed, coeff_zero_eq_constantCoeff_apply, hc0 B hb,
      constantCoeff_subst_X_pow two_ne_zero, constantCoeff_subst_X_pow three_ne_zero]
  have hc : ∀ n, 1 ≤ n → ∀ B C, Jet 1 B seed → Jet 1 C seed →
      Jet n B C → Jet (n + 1) (Ψ B) (Ψ C) := by
    intro n hn B C hb hcc hbc
    have hb0 := hc0 B hb
    have hc0' := hc0 C hcc
    have hd : X ^ n ∣ B () - C () := by
      rw [X_pow_dvd_iff]
      intro j hj
      rw [map_sub, hbc () j hj, sub_self]
    have hd2 := power_subst_dvd (B ()) (C ()) n 2 two_ne_zero hd
    have hd3 := power_subst_dvd (B ()) (C ()) n 3 three_ne_zero hd
    have hd2' : X ^ (n + 1) ∣ (B ()).subst (X ^ 2) - (C ()).subst (X ^ 2) :=
      (pow_dvd_pow X (by omega : n + 1 ≤ 2 * n)).trans hd2
    have hd3' : X ^ (n + 1) ∣ (B ()).subst (X ^ 3) - (C ()).subst (X ^ 3) :=
      (pow_dvd_pow X (by omega : n + 1 ≤ 3 * n)).trans hd3
    have hvan : (X : PowerSeries ℤ) ∣ (B ()).subst (X ^ 2) - 1 := by
      rw [X_dvd_iff]
      simp [constantCoeff_subst_X_pow two_ne_zero, hb0]
    have hmid : X ^ (n + 1) ∣ (B () - C ()) * ((B ()).subst (X ^ 2) - 1) +
        C () * ((B ()).subst (X ^ 2) - (C ()).subst (X ^ 2)) := by
      have ht : X ^ (n + 1) ∣ (B () - C ()) * ((B ()).subst (X ^ 2) - 1) := by
        rw [pow_succ]
        exact mul_dvd_mul hd hvan
      exact dvd_add ht (dvd_mul_of_dvd_right hd2' _)
    have htail : X ^ n ∣ ((B ()) ^ 2 - (C ()) ^ 2) * (B ()).subst (X ^ 2) +
        (C ()) ^ 2 * ((B ()).subst (X ^ 2) - (C ()).subst (X ^ 2)) := by
      have ht := hd.trans (sub_dvd_pow_sub_pow (B ()) (C ()) 2)
      have hi : X ^ n ∣ (B ()).subst (X ^ 2) - (C ()).subst (X ^ 2) :=
        (pow_dvd_pow X (by omega : n ≤ 2 * n)).trans hd2
      exact dvd_add (dvd_mul_of_dvd_left ht _) (dvd_mul_of_dvd_right hi _)
    have hx : X ^ (n + 1) ∣ X * (((B ()) ^ 2 - (C ()) ^ 2) * (B ()).subst (X ^ 2) +
        (C ()) ^ 2 * ((B ()).subst (X ^ 2) - (C ()).subst (X ^ 2))) := by
      rw [pow_succ']
      exact mul_dvd_mul_left X htail
    have he : Φ (B ()) - Φ (C ()) =
        ((B ()).subst (X ^ 3) - (C ()).subst (X ^ 3)) -
        ((B () - C ()) * ((B ()).subst (X ^ 2) - 1) +
          C () * ((B ()).subst (X ^ 2) - (C ()).subst (X ^ 2))) +
        X * (((B ()) ^ 2 - (C ()) ^ 2) * (B ()).subst (X ^ 2) +
          (C ()) ^ 2 * ((B ()).subst (X ^ 2) - (C ()).subst (X ^ 2))) := by dsimp only [Φ]; ring
    have ht : X ^ (n + 1) ∣ Φ (B ()) - Φ (C ()) := by
      rw [he]
      exact dvd_add (dvd_sub hd3' hmid) hx
    rw [X_pow_dvd_iff] at ht
    intro i j hj
    have hz := ht j hj
    rw [map_sub, sub_eq_zero] at hz
    exact hz
  obtain ⟨B, ⟨hb, hfix⟩, huniq⟩ := existsUnique_fixed_seed 1 seed Ψ hp hc
  have hb0 := hc0 B hb
  let A : PowerSeries ℤ := X * B ()
  let U : PowerSeries ℤ := A - A ^ 2
  have ha0 : constantCoeff A = 0 := by simp [A]
  have ha1 : coeff 1 A = 1 := by
    change coeff (0 + 1) (X * B ()) = 1
    rw [coeff_succ_X_mul, coeff_zero_eq_constantCoeff_apply, hb0]
  have he : Φ (B ()) = B () := congrFun hfix ()
  have hA : Eq377100 A U := by
    constructor
    · have hs2 := HasSubst.X_pow (R := ℤ) two_ne_zero
      have hs3 := HasSubst.X_pow (R := ℤ) three_ne_zero
      change (X * B ()).subst (X ^ 2) * (X * B () - (X * B ()) ^ 2) = (X * B ()).subst (X ^ 3)
      rw [subst_mul hs2, subst_X hs2, subst_mul hs3, subst_X hs3]
      dsimp only [Φ] at he
      linear_combination -(X ^ 3) * he
    · dsimp only [U]; ring
  refine ⟨A, ⟨ha0, ha1, U, hA⟩, ?_⟩
  rintro C ⟨hc0', hc1, V, hCV⟩
  obtain ⟨Q, hQ⟩ : (X : PowerSeries ℤ) ∣ C := X_dvd_iff.mpr hc0'
  have hq0 : constantCoeff Q = 1 := by
    have he := congrArg (coeff 1) hQ
    rw [hc1, show (1 : ℕ) = 0 + 1 from rfl, coeff_succ_X_mul,
      coeff_zero_eq_constantCoeff_apply] at he
    exact he.symm
  have hv : V = C - C ^ 2 := by linear_combination -hCV.2
  have hqeq : Φ Q = Q := by
    have he := hCV.1
    rw [hv, hQ, subst_mul (.X_pow two_ne_zero), subst_X (.X_pow two_ne_zero),
      subst_mul (.X_pow three_ne_zero), subst_X (.X_pow three_ne_zero)] at he
    have hz : X ^ 3 * (Φ Q - Q) = 0 := by
      dsimp only [Φ]
      linear_combination -he
    exact sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left (pow_ne_zero 3 (X_ne_zero (R := ℤ))))
  let G : Unit → PowerSeries ℤ := fun _ => Q
  have hgn : Jet 1 G seed := by
    intro i j hj
    have : j = 0 := by omega
    subst j
    simpa only [G, seed, coeff_zero_eq_constantCoeff_apply, map_one] using hq0
  have hgf : Ψ G = G := by funext i; exact hqeq
  have heq : Q = B () := congrFun (huniq G ⟨hgn, hgf⟩) ()
  rw [hQ, heq]

end BackfillPaper2.ExistenceA377100
#print axioms BackfillPaper2.ExistenceA377100.check_EX_A377100
