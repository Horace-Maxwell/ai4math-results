import Research.Backfill.Paper5.Proof.HalfCounting

set_option autoImplicit false

namespace CodexPaper5.BrauerParity

open BackfillPaper5

/-- Lucas at the prime 2, retaining the exact remainder for every n. -/
theorem choose_two_mod_two (n : ℕ) : (n.choose 2) % 2 = (n / 2) % 2 := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h : (n.choose 2) % 2 = ((n % 2).choose 0 * (n / 2).choose 1) % 2 :=
    Choose.choose_modEq_choose_mod_mul_choose_div_nat (n := n) (k := 2) (p := 2)
  simpa only [Nat.choose_zero_right, Nat.choose_one_right, one_mul] using h

/-- The low binary digit is required for rank 3; no parity premise is silently dropped. -/
theorem choose_three_mod_two (n : ℕ) :
    (n.choose 3) % 2 = ((n % 2) * (n / 2)) % 2 := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h : (n.choose 3) % 2 = ((n % 2).choose 1 * (n / 2).choose 1) % 2 :=
    Choose.choose_modEq_choose_mod_mul_choose_div_nat (n := n) (k := 3) (p := 2)
  simpa only [Nat.choose_one_right] using h

theorem odd_choose_two_iff (n : ℕ) (hn : n % 2 = 0) :
    Odd (n.choose 2) ↔ n % 4 = 2 := by
  rw [Nat.odd_iff, choose_two_mod_two]
  omega

theorem odd_choose_three_iff (n : ℕ) (hn : n % 2 = 1) :
    Odd (n.choose 3) ↔ n % 4 = 3 := by
  rw [Nat.odd_iff, choose_three_mod_two, hn, one_mul]
  omega

/-- Real Brauer half counts have the same parity as the number of free sets. -/
theorem odd_ncard_iff_odd_choose (n r : ℕ) (hle : r ≤ n) (hpar : r % 2 = n % 2) :
    Odd (Challenge.Hr Challenge.Fam.B n r).ncard ↔ Odd (n.choose r) := by
  have hm := InvolutionCounting.odd_doubleFactorial_pred
    (HalfFibreCounting.even_complement hle hpar)
  rw [HalfCounting.ncard_Hr_B n r hle hpar, Nat.odd_mul]
  constructor
  · exact fun h => h.1
  · intro h
    exact ⟨h, hm⟩

/-- The complete parity criterion uses the frozen direction of the congruence premise. -/
theorem odd_ncard_criterion (n r : ℕ) (hr : r = 2 ∨ r = 3) (hlt : r < n)
    (hpar : n % 2 = r % 2) :
    (Odd (Challenge.Hr Challenge.Fam.B n r).ncard ↔
      (r = 2 ∧ n % 4 = 2) ∨ (r = 3 ∧ n % 4 = 3)) := by
  rw [odd_ncard_iff_odd_choose n r (Nat.le_of_lt hlt) hpar.symm]
  rcases hr with rfl | rfl
  · simpa using (odd_choose_two_iff n (by simpa using hpar))
  · simpa using (odd_choose_three_iff n (by simpa using hpar))

/-- Oddness forces the next residue-class representative, so the rank gap is at least 4. -/
theorem odd_gap_and_choose (n r : ℕ) (hr : r = 2 ∨ r = 3) (hlt : r < n)
    (hpar : n % 2 = r % 2) (hodd : Odd (Challenge.Hr Challenge.Fam.B n r).ncard) :
    4 ≤ n - r ∧ Odd (n.choose r) := by
  have hchoose : Odd (n.choose r) :=
    (odd_ncard_iff_odd_choose n r (Nat.le_of_lt hlt) hpar.symm).mp hodd
  have hcriterion := (odd_ncard_criterion n r hr hlt hpar).mp hodd
  constructor
  · rcases hcriterion with ⟨rfl, hn⟩ | ⟨rfl, hn⟩ <;> omega
  · exact hchoose

theorem check_Lemma51 : Challenge.Lemma51 := by
  intro n r hr hlt hpar
  exact ⟨odd_ncard_criterion n r hr hlt hpar, odd_gap_and_choose n r hr hlt hpar⟩

#print axioms CodexPaper5.BrauerParity.choose_two_mod_two
#print axioms CodexPaper5.BrauerParity.choose_three_mod_two
#print axioms CodexPaper5.BrauerParity.odd_choose_two_iff
#print axioms CodexPaper5.BrauerParity.odd_choose_three_iff
#print axioms CodexPaper5.BrauerParity.odd_ncard_iff_odd_choose
#print axioms CodexPaper5.BrauerParity.odd_ncard_criterion
#print axioms CodexPaper5.BrauerParity.odd_gap_and_choose
#print axioms CodexPaper5.BrauerParity.check_Lemma51

end CodexPaper5.BrauerParity
