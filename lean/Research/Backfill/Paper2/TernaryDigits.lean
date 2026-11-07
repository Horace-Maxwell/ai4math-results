import Research.Backfill.Paper2.TernaryIterate

/-!
The exact base-three digit criterion for every exceptional index.
Lucas is applied one digit at a time to repunits (3^l-1)/2. The first
digit of (3^(l+1)+1)/2 is 2; all its remaining l digits are 1.
-/
set_option autoImplicit false
noncomputable section
namespace BackfillPaper2.TernaryDigits
open BackfillPaper2.Challenge
local notation "K" => ZMod 3

private def ones (j : ℕ) : Prop := ∀ d ∈ Nat.digits 3 j, d ≤ 1
private def u (l : ℕ) : ℕ := (3 ^ l - 1) / 2
private def b (l : ℕ) : ℕ := (3 ^ l + 1) / 2

private theorem choose_split (N j : ℕ) : (Nat.choose N j : K) =
    (Nat.choose (N % 3) (j % 3) : K) * (Nat.choose (N / 3) (j / 3) : K) := by
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h := Choose.choose_modEq_choose_mod_mul_choose_div (n := N) (k := j) (p := 3)
  simpa only [Int.cast_natCast, Int.cast_mul, Nat.cast_mul] using
    (ZMod.intCast_eq_intCast_iff _ _ 3).mpr h

private theorem ones_rec (j : ℕ) : ones j ↔ j % 3 ≤ 1 ∧ ones (j / 3) := by
  by_cases hj : j = 0
  · subst j
    simp [ones]
  · simp only [ones, Nat.digits_eq_cons_digits_div (by decide : 1 < 3) hj,
      List.forall_mem_cons]

private theorem choose_one_nonzero (j : ℕ) :
    (Nat.choose 1 (j % 3) : K) ≠ 0 ↔ j % 3 ≤ 1 := by
  have hr : j % 3 < 3 := Nat.mod_lt j (by decide)
  have hc : j % 3 = 0 ∨ j % 3 = 1 ∨ j % 3 = 2 := by omega
  rcases hc with h | h | h <;> rw [h] <;> decide

private theorem choose_two_nonzero (j : ℕ) : (Nat.choose 2 (j % 3) : K) ≠ 0 := by
  have hr : j % 3 < 3 := Nat.mod_lt j (by decide)
  have hc : j % 3 = 0 ∨ j % 3 = 1 ∨ j % 3 = 2 := by omega
  rcases hc with h | h | h <;> rw [h] <;> decide

private theorem u_step (l : ℕ) : u (l + 1) = 1 + 3 * u l := by
  have ho : Odd (3 ^ l) := (by decide : Odd (3 : ℕ)).pow
  rcases ho with ⟨t, ht⟩
  dsimp [u]
  rw [pow_succ, ht]
  omega

private theorem b_step (l : ℕ) : b (l + 1) = 2 + 3 * u l := by
  have ho : Odd (3 ^ l) := (by decide : Odd (3 : ℕ)).pow
  rcases ho with ⟨t, ht⟩
  dsimp [b, u]
  rw [pow_succ, ht]
  omega

private theorem repunit_pattern (l : ℕ) : ∀ j : ℕ,
    (Nat.choose (u l) j : K) ≠ 0 ↔ ones j ∧ j < 3 ^ l := by
  induction l with
  | zero =>
    intro j
    cases j with
    | zero => simp [u, ones]
    | succ j => simp [u]
  | succ l ih =>
    intro j
    have hm : u (l + 1) % 3 = 1 := by rw [u_step]; omega
    have hd : u (l + 1) / 3 = u l := by rw [u_step]; omega
    have hc := choose_split (u (l + 1)) j
    rw [hm, hd] at hc
    rw [hc, mul_ne_zero_iff, choose_one_nonzero, ih, ones_rec j, pow_succ]
    rw [← Nat.div_lt_iff_lt_mul (by decide : 0 < 3)]
    tauto

private theorem top_pattern (l j : ℕ) :
    (Nat.choose (b (l + 1)) j : K) ≠ 0 ↔ ones (j / 3) ∧ j / 3 < 3 ^ l := by
  have hm : b (l + 1) % 3 = 2 := by rw [b_step]; omega
  have hd : b (l + 1) / 3 = u l := by rw [b_step]; omega
  have hc := choose_split (b (l + 1)) j
  rw [hm, hd] at hc
  constructor
  · intro hn
    have hn' : (Nat.choose 2 (j % 3) : K) * (Nat.choose (u l) (j / 3) : K) ≠ 0 := hc ▸ hn
    exact (repunit_pattern l (j / 3)).mp (mul_ne_zero_iff.mp hn').2
  · intro h
    rw [hc]
    exact mul_ne_zero (choose_two_nonzero j) ((repunit_pattern l (j / 3)).mpr h)

theorem check_Thm12_digits : Thm12_digits := by
  intro j
  have hp : 0 < 3 ^ j := pow_pos (by decide) j
  have hpos : 1 ≤ b j := by dsimp [b]; omega
  have hi : 2 * b j - 1 = 3 ^ j := by
    have ho : Odd (3 ^ j) := (by decide : Odd (3 : ℕ)).pow
    rcases ho with ⟨t, ht⟩
    dsimp [b]
    omega
  have hv := TernaryIterate.check_Thm12_2 (b j) j hpos hi
  have he : ((a184894 (b j) : ℤ) : K) = (Nat.choose (b j) j : K) := by
    simpa only [Int.cast_natCast] using (ZMod.intCast_eq_intCast_iff _ _ 3).mpr hv
  have hz : (¬ (3 : ℤ) ∣ a184894 (b j)) ↔ (Nat.choose (b j) j : K) ≠ 0 := by
    constructor
    · intro h hzero
      exact h ((ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).mp (he.trans hzero))
    · intro h hd
      exact h (he.symm.trans ((ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).mpr hd))
  change (¬ (3 : ℤ) ∣ a184894 (b j)) ↔ digitsExceptLastLeOne j
  rw [hz]
  cases j with
  | zero => simp [b, digitsExceptLastLeOne]
  | succ n =>
    have hb : (n + 1) / 3 < 3 ^ n := by
      rw [Nat.div_lt_iff_lt_mul (by decide : 0 < 3), ← pow_succ]
      exact Nat.lt_pow_self (by decide)
    rw [top_pattern]
    simp only [hb, and_true, ones, digitsExceptLastLeOne,
      Nat.digits_eq_cons_digits_div (by decide : 1 < 3) (Nat.succ_ne_zero n), List.tail_cons]

end BackfillPaper2.TernaryDigits
#print axioms BackfillPaper2.TernaryDigits.check_Thm12_digits
