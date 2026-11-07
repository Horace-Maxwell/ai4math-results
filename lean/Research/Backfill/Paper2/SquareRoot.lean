import Research.Backfill.Paper2.AdditiveCore
import Research.Backfill.Paper2.BinomialHalf
import Research.Backfill.Paper2.CatalanCore
import Research.Backfill.Paper2.TernaryDigits

/-!
Complete residue chain. The ordinary root 1+C(-t) squares to 1+t in F3.
The actual sparse sqrtSeries3 is its 3-linearised associate. Finite powers
(1+t)^((3^j+1)/2) agree with the ordinary root below degree 3^j; this
proves the Lucas-half identity without casting a rational ring homomorphism.
-/
set_option autoImplicit false
noncomputable section
namespace BackfillPaper2.SquareRoot
open PowerSeries BackfillPaper2.Challenge
local notation "K" => ZMod 3

private def root : PowerSeries K := 1 + rescale (-1) (red 3 catalanC)

private theorem root_zero : constantCoeff root = 1 := by
  simp [root, red, catalanC]

private theorem root_coeff (j : ℕ) :
    coeff j root = ((Ring.choose (1 / 2 : ℚ) j : ℚ) : K) := by
  cases j with
  | zero => simp [coeff_zero_eq_constantCoeff_apply, root_zero]
  | succ n =>
    have hc : coeff (n + 1) (red 3 catalanC) = (catalan n : K) := by
      simp [red, catalanC, coeff_succ_X_mul, catalanSeries_coeff]
    rw [root, map_add, coeff_one, ite_eq_right (Nat.succ_ne_zero n), zero_add,
      coeff_rescale, hc]
    exact (BinomialHalf.check_Rem13_binomHalf (n + 1) (by omega)).2.symm

private theorem root_square : root ^ 2 = 1 + X := by
  let D := rescale (-1 : K) (red 3 catalanC)
  have hc := congrArg (PowerSeries.map (Int.castRingHom K))
    (show catalanC = X + catalanC ^ 2 from CatalanCore.check_CatalanEq)
  simp only [map_add, map_X, map_pow] at hc
  have hd := congrArg (rescale (-1 : K)) hc
  simp only [map_add, map_pow, rescale_neg_one_X] at hd
  have he : D ^ 2 = D + X := by linear_combination -hd
  have h3 : (3 : PowerSeries K) = 0 := by
    simpa only [map_ofNat, map_zero] using
      congrArg (C : K →+* PowerSeries K) (show (3 : K) = 0 by decide)
  change (1 + D) ^ 2 = 1 + X
  calc
    (1 + D) ^ 2 = 1 + X + 3 * D := by linear_combination he
    _ = 1 + X := by rw [h3, zero_mul, add_zero]

private theorem sqrt_additive : Additive3 sqrtSeries3 := by
  intro n hn
  rw [sqrtSeries3, coeff_mk]
  apply Finset.sum_eq_zero
  intro j _
  exact ite_eq_right (fun hj => hn ⟨j, hj⟩)

private theorem sqrt_pow_coeff (j : ℕ) :
    coeff (3 ^ j) sqrtSeries3 = coeff j root := by
  rw [sqrtSeries3, coeff_mk, Finset.sum_eq_single j]
  · rw [ite_eq_left rfl, root_coeff]
  · intro i _ hij
    exact ite_eq_right (fun he => hij (Nat.pow_right_injective (by decide : 2 ≤ 3) he).symm)
  · intro hj
    exact False.elim (hj (Finset.mem_range.mpr (by
      have := Nat.lt_pow_self (by decide : 1 < 3) (n := j)
      omega)))

private theorem sqrt_first : coeff 1 sqrtSeries3 = 1 := by
  simpa only [pow_zero, coeff_zero_eq_constantCoeff_apply, root_zero] using sqrt_pow_coeff 0

private def associate (F : PowerSeries K) : PowerSeries K := mk fun j => coeff (3 ^ j) F

private theorem associate_square (F : PowerSeries K)
    (h0 : constantCoeff F = 0) (h1 : coeff 1 F = 1)
    (hF : F.subst F = X + X ^ 3) : associate F ^ 2 = 1 + X := by
  ext j
  rw [pow_two, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp only [associate, coeff_mk]
  rw [← AdditiveCore.coeff_additive_subst F F (AdditiveCore.residue F h0 h1 hF) h0 j, hF]
  simp only [map_add, coeff_X, coeff_X_pow, coeff_one]
  by_cases hj0 : j = 0
  · subst j; simp
  · have hp1 : 3 ^ j ≠ 1 := by
      exact ne_of_gt (Nat.one_lt_pow hj0 (by decide : 1 < 3))
    have hp3 : 3 ^ j = 3 ↔ j = 1 := by
      constructor
      · intro h; exact Nat.pow_right_injective (by decide : 2 ≤ 3) (h.trans (pow_one 3).symm)
      · rintro rfl; rfl
    simp [hp3, hj0]

private theorem root_unique (S : PowerSeries K) (h0 : constantCoeff S = 1)
    (hS : S ^ 2 = 1 + X) : S = root := by
  have hu : IsUnit (S + root) := PowerSeries.isUnit_iff_constantCoeff.mpr (by
    rw [map_add, h0, root_zero]
    exact isUnit_iff_ne_zero.mpr (by decide))
  have hz : (S + root) * (S - root) = 0 := by
    linear_combination hS - root_square
  exact sub_eq_zero.mp (hu.mul_right_eq_zero.mp hz)

theorem check_Rem13_sqrtSeries : Rem13_sqrtSeries := by
  constructor
  · apply PowerSeries.ext
    intro n
    by_cases hn : ∃ j, n = 3 ^ j
    · obtain ⟨j, rfl⟩ := hn
      rw [AdditiveCore.check_Rem13_correspondence sqrtSeries3 sqrtSeries3
        sqrt_additive sqrt_additive j]
      simp_rw [sqrt_pow_coeff]
      have he := congrArg (coeff j) root_square
      rw [pow_two, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at he
      rw [he]
      simp only [map_add, coeff_one, coeff_X, coeff_X_pow]
      by_cases hj0 : j = 0
      · subst j; simp
      · have hp1 := ne_of_gt (Nat.one_lt_pow hj0 (by decide : 1 < 3))
        have hp3 : 3 ^ j = 3 ↔ j = 1 := by
          constructor
          · intro h; exact Nat.pow_right_injective (by decide : 2 ≤ 3) (h.trans (pow_one 3).symm)
          · rintro rfl; rfl
        simp [hj0, hp3]
    · rw [AdditiveCore.check_Sec6_additiveComp _ _ sqrt_additive sqrt_additive n hn,
        map_add, coeff_X, coeff_X_pow,
        ite_eq_right (fun h => hn ⟨0, by simpa using h⟩),
        ite_eq_right (fun h => hn ⟨1, by simpa using h⟩), add_zero]
  · intro A h0 h1 hA
    obtain ⟨hf0, hf1, hf⟩ := AdditiveCore.mapped_spec A h0 h1 hA
    have ha : associate (red 3 A) = root := root_unique _ (by
      rw [← coeff_zero_eq_constantCoeff_apply, associate, coeff_mk, pow_zero]
      exact hf1)
      (associate_square (red 3 A) hf0 hf1 hf)
    ext n
    by_cases hn : ∃ j, n = 3 ^ j
    · obtain ⟨j, rfl⟩ := hn
      rw [sqrt_pow_coeff]
      simpa only [associate, coeff_mk] using congrArg (coeff j) ha
    · rw [AdditiveCore.residue _ hf0 hf1 hf n (fun j hj => hn ⟨j, hj⟩),
        sqrt_additive n hn]

private theorem binomial_coeff (N j : ℕ) :
    coeff j ((1 + X : PowerSeries K) ^ N) = (Nat.choose N j : K) := by
  have he := PowerSeries.binomialSeries_nat (R := ℤ) (A := K) N
  rw [← he, binomialSeries_coeff, Ring.choose_natCast]
  simp

theorem check_Rem13_lucasHalf : Rem13_lucasHalf := by
  intro j
  let N := (3 ^ j + 1) / 2
  let W : PowerSeries K := (1 + X) ^ N
  have hp : 0 < 3 ^ j := pow_pos (by decide) j
  have he : 2 * N = 3 ^ j + 1 := by
    have ho : Odd (3 ^ j) := (by decide : Odd (3 : ℕ)).pow
    rcases ho with ⟨t, ht⟩
    dsimp [N]; omega
  have hw : W ^ 2 = (1 + X) * (1 + X ^ (3 ^ j)) := by
    have hpow : (1 + X : PowerSeries K) ^ (3 ^ j) = 1 + X ^ (3 ^ j) := by
      clear he hp W N
      induction j with
      | zero => simp
      | succ k ih =>
        rw [pow_succ, pow_mul, ih, AdditiveCore.cube_eq_expand,
          map_add, map_one, map_pow, expand_X]
        rw [← pow_mul, Nat.mul_comm 3 (3 ^ k)]
    dsimp only [W]
    rw [← pow_mul, Nat.mul_comm N 2, he, pow_succ, hpow]
    ring
  have hu : IsUnit (W + root) := PowerSeries.isUnit_iff_constantCoeff.mpr (by
    simp only [map_add, W, map_pow, map_one, constantCoeff_X, add_zero, one_pow, root_zero]
    exact isUnit_iff_ne_zero.mpr (by decide))
  have hd : (X : PowerSeries K) ^ (3 ^ j) ∣ (W - root) * (W + root) := by
    refine ⟨1 + X, ?_⟩
    linear_combination hw - root_square
  have hd' := hu.dvd_mul_right.mp hd
  rw [X_pow_dvd_iff] at hd'
  have hc := hd' j (Nat.lt_pow_self (by decide : 1 < 3))
  rw [map_sub, sub_eq_zero] at hc
  dsimp only [W] at hc
  rw [binomial_coeff, root_coeff] at hc
  exact hc

theorem check_Rem13_residues : Rem13_residues := by
  constructor
  · intro j hj
    let N := (3 ^ j + 1) / 2
    have hp : 0 < 3 ^ j := pow_pos (by decide) j
    have hN : 1 ≤ N := by dsimp [N]; omega
    have hi : 2 * N - 1 = 3 ^ j := by
      have ho : Odd (3 ^ j) := (by decide : Odd (3 : ℕ)).pow
      rcases ho with ⟨t, ht⟩
      dsimp [N]; omega
    have hm := TernaryIterate.check_Thm12_2 N j hN hi
    apply (ZMod.intCast_eq_intCast_iff _ _ 3).mp
    calc
      ((a184894 N : ℤ) : K) = (Nat.choose N j : K) := by
        simpa only [Int.cast_natCast] using (ZMod.intCast_eq_intCast_iff _ _ 3).mpr hm
      _ = ((Ring.choose (1 / 2 : ℚ) j : ℚ) : K) := check_Rem13_lucasHalf j
      _ = (-1) ^ j * (catalan (j - 1) : K) := (BinomialHalf.check_Rem13_binomHalf j hj).2
      _ = (((-1) ^ j * (catalan (j - 1) : ℤ) : ℤ) : K) := by norm_cast
  · intro A h0 h1 hA j hj
    apply (ZMod.intCast_eq_intCast_iff _ _ 3).mp
    have he := congrArg (coeff (3 ^ j)) (check_Rem13_sqrtSeries.2 A h0 h1 hA)
    rw [sqrt_pow_coeff, root_coeff] at he
    calc
      ((coeff (3 ^ j) A : ℤ) : K) = ((Ring.choose (1 / 2 : ℚ) j : ℚ) : K) := he
      _ = (-1) ^ j * (catalan (j - 1) : K) := (BinomialHalf.check_Rem13_binomHalf j hj).2
      _ = (((-1) ^ j * (catalan (j - 1) : ℤ) : ℤ) : K) := by norm_cast

theorem check_Rem13_DS52 : Rem13_DS52 := by
  intro j hj
  rw [← TernaryDigits.check_Thm12_digits j]
  have hm := (ZMod.intCast_eq_intCast_iff _ _ 3).mpr (check_Rem13_residues.1 j hj)
  have he : ((a184894 ((3 ^ j + 1) / 2) : ℤ) : K) =
      (-1) ^ j * (catalan (j - 1) : K) := by simpa only [Int.cast_mul, Int.cast_pow,
        Int.cast_neg, Int.cast_one, Int.cast_natCast] using hm
  have hz : (catalan (j - 1) : K) = 0 ↔
      ((a184894 ((3 ^ j + 1) / 2) : ℤ) : K) = 0 := by
    rw [he, mul_eq_zero]
    exact (or_iff_right (pow_ne_zero j (neg_ne_zero.mpr one_ne_zero))).symm
  simpa only [ZMod.natCast_eq_zero_iff, ZMod.intCast_zmod_eq_zero_iff_dvd,
    Nat.cast_ofNat] using not_congr hz

end BackfillPaper2.SquareRoot
#print axioms BackfillPaper2.SquareRoot.check_Rem13_sqrtSeries
#print axioms BackfillPaper2.SquareRoot.check_Rem13_lucasHalf
#print axioms BackfillPaper2.SquareRoot.check_Rem13_residues
#print axioms BackfillPaper2.SquareRoot.check_Rem13_DS52
