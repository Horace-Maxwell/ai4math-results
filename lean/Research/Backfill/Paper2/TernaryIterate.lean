import Research.Backfill.Paper2.Challenge

/-!
Paper 2: the actual A184894 iterate, coefficient formula, and first failure.
Transport the published HannaA184894 coefficient induction to the frozen
recursive polynomial definition; no old project declaration is imported.
-/
set_option autoImplicit false
noncomputable section
namespace BackfillPaper2.TernaryIterate
open Polynomial BackfillPaper2.Challenge
local notation "K" => ZMod 3

private def iter3 : ℕ → K[X]
  | 0 => X
  | m + 1 => iter3 m + (iter3 m) ^ 3

private theorem map_P (m : ℕ) :
    (P184894 m).map (Int.castRingHom (ZMod 3)) = iter3 m := by
  induction m with
  | zero => simp [P184894, iter3]
  | succ m ih => simp only [P184894, iter3, Polynomial.map_add, Polynomial.map_pow, ih]

/-- The coefficient recursion modulo 3. -/
private theorem coeff_rec (m k : ℕ) : (iter3 (m + 1)).coeff k =
    (iter3 m).coeff k + (if 3 ∣ k then (iter3 m).coeff (k / 3) else 0) := by
  rw [iter3, coeff_add, ← ZMod.expand_card, coeff_expand (by norm_num)]

private theorem coeff_zero_iter (k : ℕ) : (iter3 0).coeff k = if k = 1 then 1 else 0 := by
  simp [iter3, coeff_X, eq_comm]

/-- Coefficients at non-powers of 3 vanish modulo 3. -/
private theorem coeff_nonpow (m : ℕ) : ∀ k, (∀ j, k ≠ 3 ^ j) → (iter3 m).coeff k = 0 := by
  induction m with
  | zero =>
    intro k hk
    rw [coeff_zero_iter, ite_eq_right (by simpa using hk 0)]
  | succ m ih =>
    intro k hk
    rw [coeff_rec, ih k hk, zero_add]
    split_ifs with h3
    · apply ih
      intro j hj
      apply hk (j + 1)
      obtain ⟨t, rfl⟩ := h3
      rw [Nat.mul_div_cancel_left t (by norm_num)] at hj
      rw [hj, pow_succ]; ring
    · rfl

/-- Coefficients at `3^j` are binomial coefficients modulo 3. -/
private theorem coeff_pow (m : ℕ) : ∀ j, (iter3 m).coeff (3 ^ j) = (m.choose j : K) := by
  induction m with
  | zero =>
    intro j
    rw [coeff_zero_iter]
    rcases j with _ | j
    · simp
    · have : 3 ^ (j + 1) ≠ 1 := by
        have := Nat.one_lt_pow (Nat.succ_ne_zero j) (by norm_num : 1 < 3)
        omega
      simp only [pow_succ] at this ⊢
      simp [this]
  | succ m ih =>
    intro j
    rw [coeff_rec, ih j]
    rcases j with _ | j
    · rw [ite_eq_right (by norm_num), add_zero]; simp
    · rw [ite_eq_left (dvd_pow_self 3 (Nat.succ_ne_zero j)),
        show 3 ^ (j + 1) / 3 = 3 ^ j by rw [pow_succ, Nat.mul_div_cancel _ (by norm_num)], ih j,
        Nat.choose_succ_succ', Nat.cast_add, add_comm]

private theorem a_cast (m : ℕ) : ((a184894 m : ℤ) : K) = (iter3 m).coeff (2 * m - 1) := by
  rw [a184894, ← map_P, coeff_map]
  rfl

theorem check_Thm12_1 : Thm12_1 := by
  intro m _ hm
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).mp
  rw [a_cast]
  exact coeff_nonpow m _ (fun j hj => hm ⟨j, hj⟩)

theorem check_Thm12_2 : Thm12_2 := by
  intro m j _ h
  apply (ZMod.intCast_eq_intCast_iff _ _ 3).mp
  have hv : ((a184894 m : ℤ) : K) = (m.choose j : K) := by rw [a_cast, h, coeff_pow]
  simpa only [Int.cast_natCast] using hv

private theorem choose_365_6 : Nat.choose 365 6 = 3151277509380 := by
  rw [Nat.choose_eq_descFactorial_div_factorial]
  norm_num [Nat.descFactorial, Nat.factorial]

theorem check_Thm12_3 : Thm12_3 := by
  refine ⟨by norm_num, ?_⟩
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).mp
  rw [a_cast, show 2 * 365 - 1 = 3 ^ 6 by norm_num, coeff_pow,
    choose_365_6, ZMod.natCast_eq_zero_iff]
  norm_num

theorem check_Thm12_entryLiteral : Thm12_entryLiteral := by
  intro m hm h
  apply check_Thm12_1 m hm
  rintro ⟨j, hj⟩
  apply h j
  omega

private theorem exceptional_index (j : ℕ) : 2 * ((3 ^ j + 1) / 2) - 1 = 3 ^ j := by
  have ho : Odd (3 ^ j) := (by decide : Odd (3 : ℕ)).pow
  rcases ho with ⟨t, ht⟩
  omega

theorem check_Thm12_firstFailure : Thm12_firstFailure := by
  have small : ∀ n : ℕ, n < 6 → (Nat.choose ((3 ^ n + 1) / 2) n : K) ≠ 0 := by
    intro n hn
    have hd : ¬ 3 ∣ Nat.choose ((3 ^ n + 1) / 2) n := by
      interval_cases n <;>
        norm_num [Nat.choose_eq_descFactorial_div_factorial, Nat.descFactorial, Nat.factorial]
    intro hz
    exact hd ((ZMod.natCast_eq_zero_iff _ 3).mp hz)
  constructor
  · intro n hn hd
    have hv : ((a184894 ((3 ^ n + 1) / 2) : ℤ) : K) =
        (Nat.choose ((3 ^ n + 1) / 2) n : K) := by
      rw [a_cast, exceptional_index, coeff_pow]
    have hz := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).mpr hd
    exact small n hn (hv.symm.trans hz)
  · simpa only [Nat.reducePow, Nat.reduceAdd, Nat.reduceDiv] using check_Thm12_3.2

end BackfillPaper2.TernaryIterate
#print axioms BackfillPaper2.TernaryIterate.check_Thm12_1
#print axioms BackfillPaper2.TernaryIterate.check_Thm12_2
#print axioms BackfillPaper2.TernaryIterate.check_Thm12_3
#print axioms BackfillPaper2.TernaryIterate.check_Thm12_entryLiteral
#print axioms BackfillPaper2.TernaryIterate.check_Thm12_firstFailure
