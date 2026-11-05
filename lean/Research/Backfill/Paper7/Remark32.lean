import Research.Backfill.Paper7.ChallengeV3

/-!
# Paper 7: the exact Bernoulli denominator in Remark 3.2

Source-only author candidate for every odd `b ≥ 3`. The two divisibilities
come from the von Staudt–Clausen integer correction sum and the divisibility
of the Bernoulli denominator by each relevant prime. Distinct primes are
coprime, so their product divides the denominator.
-/

set_option autoImplicit false

open Finset
open BackfillPaper7.Challenge

namespace BackfillPaper7.BernoulliProof

/-- A divisor of the positive predecessor cannot introduce a prime beyond
the frozen finite range. The conclusion even holds without primality. -/
theorem pred_dvd_bound {b p : ℕ} (hb : 2 ≤ b) (hdiv : p - 1 ∣ b - 1) : p ≤ b := by
  have hle : p - 1 ≤ b - 1 := Nat.le_of_dvd (by omega) hdiv
  omega

theorem prime_product_dvd (s : Finset ℕ) (n : ℕ) :
    (∀ p ∈ s, p.Prime) → (∀ p ∈ s, p ∣ n) → (∏ p ∈ s, p) ∣ n := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro _ _
    simp
  | @insert p s hp ih =>
    intro hprime hdvd
    have hpprime : p.Prime := hprime p (Finset.mem_insert_self p s)
    have hsprime : ∀ q ∈ s, q.Prime :=
      fun q hq => hprime q (Finset.mem_insert_of_mem hq)
    have hsdvd : ∀ q ∈ s, q ∣ n :=
      fun q hq => hdvd q (Finset.mem_insert_of_mem hq)
    have hcop : p.Coprime (∏ q ∈ s, q) := by
      apply Nat.coprime_prod_right_iff.mpr
      intro q hq
      apply (Nat.coprime_primes hpprime (hsprime q hq)).mpr
      intro hpq
      exact hp (hpq.symm ▸ hq)
    rw [Finset.prod_insert hp]
    exact hcop.mul_dvd_of_dvd_of_dvd
      (hdvd p (Finset.mem_insert_self p s)) (ih hsprime hsdvd)

theorem even_bernoulli_den (k : ℕ) (hk : 0 < k) :
    (_root_.bernoulli (2 * k)).den =
      ∏ p ∈ (Finset.range (2 * k + 2)).filter
        (fun p => p.Prime ∧ (p - 1) ∣ 2 * k), p := by
  classical
  let s : Finset ℕ := (Finset.range (2 * k + 2)).filter
    (fun p => p.Prime ∧ (p - 1) ∣ 2 * k)
  change (_root_.bernoulli (2 * k)).den = ∏ p ∈ s, p
  obtain ⟨z, hz⟩ := Bernoulli.vonStaudt_clausen k
  change (z : ℚ) = _root_.bernoulli (2 * k) + ∑ p ∈ s, (1 : ℚ) / p at hz
  have hB : _root_.bernoulli (2 * k) = (z : ℚ) - ∑ p ∈ s, (1 : ℚ) / p := by
    linarith only [hz]
  apply Nat.dvd_antisymm
  · rw [hB, Rat.intCast_sub_den]
    have hsum := Finset.Rat.den_sum_dvd_prod_den s (fun p : ℕ => (1 : ℚ) / p)
    have hprod : (∏ p ∈ s, ((1 : ℚ) / p).den) = ∏ p ∈ s, p := by
      apply Finset.prod_congr rfl
      intro p hp
      have hpprime : p.Prime := (Finset.mem_filter.mp hp).2.1
      rw [one_div]
      exact Rat.inv_natCast_den_of_pos hpprime.pos
    rwa [hprod] at hsum
  · apply prime_product_dvd s (_root_.bernoulli (2 * k)).den
    · intro p hp
      exact (Finset.mem_filter.mp hp).2.1
    · intro p hp
      have hconditions : p.Prime ∧ (p - 1) ∣ 2 * k := (Finset.mem_filter.mp hp).2
      have : Fact p.Prime := ⟨hconditions.1⟩
      exact Bernoulli.dvd_den_bernoulli hk hconditions.2

end BackfillPaper7.BernoulliProof

theorem check_Remark32 : BackfillPaper7.Challenge.Remark32 := by
  intro b hb hodd
  obtain ⟨k, hbk⟩ := hodd
  have hk : 0 < k := by omega
  have hpred : b - 1 = 2 * k := by omega
  have hrange : b + 1 = 2 * k + 2 := by omega
  simpa only [kappa, hpred, hrange] using
    BackfillPaper7.BernoulliProof.even_bernoulli_den k hk

#print axioms BackfillPaper7.BernoulliProof.pred_dvd_bound
#print axioms BackfillPaper7.BernoulliProof.prime_product_dvd
#print axioms BackfillPaper7.BernoulliProof.even_bernoulli_den
#print axioms check_Remark32
