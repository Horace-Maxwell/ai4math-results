import Research.Backfill.Paper2.XadicFixedPoint

/-! Joint coefficient stabilization constructs all infinitely many integer tails.
The original sign normalization is derived to be +1, rather than strengthened. -/
set_option autoImplicit false
noncomputable section
namespace BackfillPaper2.ExistenceCFFamily
open PowerSeries BackfillPaper2.Challenge BackfillPaper2.XadicFixedPoint

private theorem inverse_dvd (A B : PowerSeries ℤ) (hA : constantCoeff A = 1)
    (hB : constantCoeff B = 1) (n : ℕ) (h : X ^ n ∣ A - B) :
    X ^ n ∣ invOfUnit A 1 - invOfUnit B 1 := by
  have ha : invOfUnit A 1 * A = 1 := invOfUnit_mul A 1 hA
  have hb : invOfUnit B 1 * B = 1 := invOfUnit_mul B 1 hB
  have he : invOfUnit A 1 - invOfUnit B 1 = -(invOfUnit A 1) * (A - B) * invOfUnit B 1 := by
    linear_combination (invOfUnit B 1) * ha - (invOfUnit A 1) * hb
  rw [he]
  exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_right h _) _

private theorem family (e : ℕ) : ∃! A : PowerSeries ℤ, ∃ T : ℕ → PowerSeries ℤ, CF e A T := by
  let a : ℕ → ℤ := fun k => ((k : ℤ) + 2) ^ e
  let seed : ℕ → PowerSeries ℤ := fun _ => 1
  let Φ : (ℕ → PowerSeries ℤ) → ℕ → PowerSeries ℤ := fun T k =>
    1 + X * invOfUnit (T 0) 1 - C (a k) * X * invOfUnit (T (k + 1)) 1
  have hc : ∀ T : ℕ → PowerSeries ℤ, Jet 1 T seed → ∀ k, constantCoeff (T k) = 1 := by
    intro T h k
    have he := h k 0 (by omega)
    simpa only [seed, coeff_zero_eq_constantCoeff_apply, map_one] using he
  have hpres : ∀ T, Jet 1 T seed → Jet 1 (Φ T) seed := by
    intro T _ k j hj
    have : j = 0 := by omega
    subst j
    simp [Φ, seed, coeff_zero_eq_constantCoeff_apply]
  have hcontract : ∀ n, 1 ≤ n → ∀ T U, Jet 1 T seed → Jet 1 U seed →
      Jet n T U → Jet (n + 1) (Φ T) (Φ U) := by
    intro n hn T U ht hu hd k j hj
    have hi : ∀ q, X ^ n ∣ invOfUnit (T q) 1 - invOfUnit (U q) 1 := by
      intro q
      apply inverse_dvd _ _ (hc T ht q) (hc U hu q) n
      rw [X_pow_dvd_iff]
      intro l hl
      rw [map_sub, hd q l hl, sub_self]
    have he : Φ T k - Φ U k =
        X * (invOfUnit (T 0) 1 - invOfUnit (U 0) 1) -
          C (a k) * (X * (invOfUnit (T (k + 1)) 1 - invOfUnit (U (k + 1)) 1)) := by
      dsimp only [Φ]
      ring
    have hdiv : X ^ (n + 1) ∣ Φ T k - Φ U k := by
      rw [he, pow_succ']
      exact dvd_sub (mul_dvd_mul_left X (hi 0))
        (dvd_mul_of_dvd_right (mul_dvd_mul_left X (hi (k + 1))) _)
    rw [X_pow_dvd_iff] at hdiv
    have hz := hdiv j hj
    rw [map_sub, sub_eq_zero] at hz
    exact hz
  obtain ⟨T, ⟨ht, hfix⟩, huniq⟩ := existsUnique_fixed_seed 1 seed Φ hpres hcontract
  have ht0 : ∀ k, constantCoeff (T k) = 1 := hc T ht
  let A : PowerSeries ℤ := 1 + X * invOfUnit (T 0) 1
  have hroot : (A - 1) * T 0 = X := by
    dsimp only [A]
    rw [add_sub_cancel_left, mul_assoc, invOfUnit_mul _ _ (ht0 0), mul_one]
  have htail : ∀ k, (A - T k) * T (k + 1) = C (a k) * X := by
    intro k
    have hk : T k = A - C (a k) * X * invOfUnit (T (k + 1)) 1 := (congrFun hfix k).symm
    rw [hk]
    have hi := invOfUnit_mul (T (k + 1)) 1 (ht0 (k + 1))
    linear_combination (C (a k) * X) * hi
  have hcf : CF e A T := ⟨fun k => Or.inl (ht0 k), hroot, htail⟩
  refine ⟨A, ⟨T, hcf⟩, ?_⟩
  rintro B ⟨U, hu⟩
  have hune : ∀ k, constantCoeff (U k) ≠ 0 := by
    intro k
    rcases hu.1 k with he | he <;> rw [he] <;> norm_num
  have hb0 : constantCoeff B = 1 := by
    have he := congrArg constantCoeff hu.2.1
    simp only [map_mul, map_sub, map_one, constantCoeff_X] at he
    exact sub_eq_zero.mp ((mul_eq_zero.mp he).resolve_right (hune 0))
  have hu0 : ∀ k, constantCoeff (U k) = 1 := by
    intro k
    have he := congrArg constantCoeff (hu.2.2 k)
    simp only [map_mul, map_sub, constantCoeff_C, constantCoeff_X, mul_zero] at he
    have hh := sub_eq_zero.mp ((mul_eq_zero.mp he).resolve_right (hune (k + 1)))
    exact hh.symm.trans hb0
  have hb : B = 1 + X * invOfUnit (U 0) 1 := by
    have hi := mul_invOfUnit (U 0) 1 (hu0 0)
    have he : B - 1 = X * invOfUnit (U 0) 1 := by
      calc
        B - 1 = (B - 1) * (U 0 * invOfUnit (U 0) 1) := by rw [hi, mul_one]
        _ = ((B - 1) * U 0) * invOfUnit (U 0) 1 := by ring
        _ = X * invOfUnit (U 0) 1 := by rw [hu.2.1]
    linear_combination he
  have hufix : Φ U = U := by
    funext k
    have hi := mul_invOfUnit (U (k + 1)) 1 (hu0 (k + 1))
    have hk := hu.2.2 k
    have he : B - U k = C (a k) * X * invOfUnit (U (k + 1)) 1 := by
      calc
        B - U k = (B - U k) * (U (k + 1) * invOfUnit (U (k + 1)) 1) := by rw [hi, mul_one]
        _ = ((B - U k) * U (k + 1)) * invOfUnit (U (k + 1)) 1 := by ring
        _ = C (a k) * X * invOfUnit (U (k + 1)) 1 := by rw [hk]
    dsimp only [Φ]
    rw [← hb]
    linear_combination he
  have hunorm : Jet 1 U seed := by
    intro k j hj
    have : j = 0 := by omega
    subst j
    simpa only [seed, coeff_zero_eq_constantCoeff_apply, map_one] using hu0 k
  have hut : U = T := huniq U ⟨hunorm, hufix⟩
  rw [hb, hut]

theorem check_EX_A338633 : EX_A338633 := family 3
theorem check_EX_A338634 : EX_A338634 := family 4

end BackfillPaper2.ExistenceCFFamily
#print axioms BackfillPaper2.ExistenceCFFamily.check_EX_A338633
#print axioms BackfillPaper2.ExistenceCFFamily.check_EX_A338634
