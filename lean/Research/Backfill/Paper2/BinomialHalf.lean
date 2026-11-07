import Research.Backfill.Paper2.Challenge

/-! Exact half-binomial formula, with reduction through an integer numerator
and a denominator 4^j. No general ring-hom law for rational-to-F3 casts is used. -/
set_option autoImplicit false
noncomputable section
namespace BackfillPaper2.BinomialHalf
open BackfillPaper2.Challenge
local notation "K" => ZMod 3

private theorem choose_step (r : ℚ) (n : ℕ) :
    ((n + 1 : ℕ) : ℚ) * Ring.choose r (n + 1) = Ring.choose r n * (r - n) := by
  have h := Ring.choose_smul_choose r (n := n + 1) (k := n) (by omega)
  simpa only [Nat.choose_succ_self_right, nsmul_eq_mul, Nat.add_sub_cancel_left,
    Ring.choose_one_right] using h

private theorem catalan_step (n : ℕ) :
    (n + 2) * catalan (n + 1) = 2 * (2 * n + 1) * catalan n := by
  have h := Nat.succ_mul_centralBinom_succ n
  rw [← succ_mul_catalan_eq_centralBinom (n + 1),
    ← succ_mul_catalan_eq_centralBinom n] at h
  apply Nat.eq_of_mul_eq_mul_left (by omega : 0 < n + 1)
  nlinarith only [h]

private theorem half_formula (n : ℕ) :
    Ring.choose (1 / 2 : ℚ) (n + 1) =
      2 * (-1) ^ n * (catalan n : ℚ) / 4 ^ (n + 1) := by
  induction n with
  | zero => norm_num [Ring.choose_one_right, catalan]
  | succ n ih =>
    have hr := choose_step (1 / 2 : ℚ) (n + 1)
    have hc : ((n : ℚ) + 2) * (catalan (n + 1) : ℚ) =
        2 * (2 * (n : ℚ) + 1) * (catalan n : ℚ) := by
      exact_mod_cast catalan_step n
    have hn : ((n : ℚ) + 2) ≠ 0 := by positivity
    have hp : (4 : ℚ) ^ (n + 1) ≠ 0 := pow_ne_zero _ (by norm_num)
    push_cast at hr
    rw [ih] at hr
    calc
      Ring.choose (1 / 2 : ℚ) (n + 1 + 1) =
          (2 * (-1) ^ n * (catalan n : ℚ) / 4 ^ (n + 1)) *
            (1 / 2 - ((n : ℚ) + 1)) / ((n : ℚ) + 2) := by
        apply (eq_div_iff hn).mpr
        linear_combination hr
      _ = 2 * (-1) ^ (n + 1) * (catalan (n + 1) : ℚ) / 4 ^ (n + 1 + 1) := by
        rw [pow_succ (-1 : ℚ), pow_succ (4 : ℚ)]
        field_simp
        linear_combination (8 * (4 : ℚ) ^ n) * hc

private theorem half_mod (n : ℕ) :
    ((Ring.choose (1 / 2 : ℚ) (n + 1) : ℚ) : K) =
      (-1) ^ (n + 1) * (catalan n : K) := by
  have he : Ring.choose (1 / 2 : ℚ) (n + 1) =
      mkRat (2 * (-1) ^ n * (catalan n : ℤ)) (4 ^ (n + 1)) := by
    rw [half_formula, Rat.mkRat_eq_div]
    push_cast
    rfl
  have hd : ((4 ^ (n + 1) : ℕ) : K) ≠ 0 := by
    simpa only [Nat.cast_pow, Nat.cast_ofNat, show (4 : K) = 1 by decide, one_pow] using
      (one_ne_zero : (1 : K) ≠ 0)
  rw [he, Rat.cast_mkRat_of_ne_zero _ hd]
  rw [Nat.cast_pow, Nat.cast_ofNat, show (4 : K) = 1 by decide, one_pow, div_one]
  push_cast
  rw [show (2 : K) = -1 by decide, pow_succ]
  ring

theorem check_Rem13_binomHalf : Rem13_binomHalf := by
  intro j hj
  obtain ⟨n, rfl⟩ : ∃ n, j = n + 1 := ⟨j - 1, by omega⟩
  simpa only [Nat.add_sub_cancel] using And.intro (half_formula n) (half_mod n)

end BackfillPaper2.BinomialHalf
#print axioms BackfillPaper2.BinomialHalf.check_Rem13_binomHalf
