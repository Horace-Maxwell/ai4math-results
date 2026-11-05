import Research.Backfill.Paper7.ChallengeV2

/-! Arithmetic for the exact frozen product of distinct eligible primes. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace Paper7Corollary31
open BackfillPaper7.Challenge

theorem kappa_dvd_of_prime_divisors (b n : ℕ)
    (h : ∀ q : ℕ, q.Prime → q-1 ∣ b-1 → q ∣ n) : kappa b ∣ n := by
  unfold kappa
  apply Finset.prod_dvd_of_isRelPrime
  · intro q hq r hr hqr
    have hq' := (Finset.mem_filter.mp hq).2.1
    have hr' := (Finset.mem_filter.mp hr).2.1
    exact Nat.coprime_iff_isRelPrime.mp ((Nat.coprime_primes hq' hr').mpr hqr)
  · intro q hq
    exact h q (Finset.mem_filter.mp hq).2.1 (Finset.mem_filter.mp hq).2.2
#print axioms Paper7Corollary31.kappa_dvd_of_prime_divisors

theorem prime_dvd_kappa (b q : ℕ) (hb : 2 ≤ b) (hq : q.Prime)
    (hperiod : q-1 ∣ b-1) : q ∣ kappa b := by
  have hle : q-1 ≤ b-1 := Nat.le_of_dvd (by omega) hperiod
  have hq2 := hq.two_le
  have hmem : q ∈ (Finset.range (b+1)).filter (fun q => q.Prime ∧ q-1 ∣ b-1) :=
    Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hq, hperiod⟩
  exact Finset.dvd_prod_of_mem (fun q : ℕ => q) hmem
#print axioms Paper7Corollary31.prime_dvd_kappa

theorem kappa_prime_obstruction (b q : ℕ) (hb : 2 ≤ b) (hq : q.Prime)
    (hperiod : q-1 ∣ b-1) (hnot : ¬ q ∣ 2*b) : ¬ kappa b ∣ 2*b := by
  intro h
  exact hnot ((prime_dvd_kappa b q hb hq hperiod).trans h)
#print axioms Paper7Corollary31.kappa_prime_obstruction

theorem three_dvd_of_kappa (b : ℕ) (hb : 3 ≤ b) (ho : Odd b)
    (hk : kappa b ∣ 2*b) : 3 ∣ b := by
  have hp : 3-1 ∣ b-1 := by
    obtain ⟨j, hj⟩ := ho
    exact ⟨j, by omega⟩
  have h : 3 ∣ 2*b := (prime_dvd_kappa b 3 (by omega) Nat.prime_three hp).trans hk
  rcases Nat.prime_three.dvd_mul.mp h with h2 | hb3
  · norm_num at h2
  · exact hb3
#print axioms Paper7Corollary31.three_dvd_of_kappa

theorem fifteen_le_of_kappa (b : ℕ) (hb : 3 ≤ b) (ho : Odd b)
    (hk : kappa b ∣ 2*b) (hne : b ≠ 3) : 15 ≤ b := by
  have hthree := three_dvd_of_kappa b hb ho hk
  by_contra hsmall
  obtain ⟨j, hj⟩ := ho
  obtain ⟨k, hk3⟩ := hthree
  have hb9 : b = 9 := by omega
  rw [hb9] at hk
  exact kappa_prime_obstruction 9 5 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hk
#print axioms Paper7Corollary31.fifteen_le_of_kappa

end Paper7Corollary31
