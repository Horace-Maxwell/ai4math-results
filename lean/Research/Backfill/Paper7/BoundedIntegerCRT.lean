import Research.Backfill.Paper7.LegacyTransfer

/-! Bounded integer CRT via divisibility. Concrete coprimality uses Euclidean
GCD on four fixed integers; no primality search or certificate is claimed. -/
set_option autoImplicit false
noncomputable section
namespace Paper7CRTAlgebra
open BackfillPaper7.Challenge.Legacy

theorem pairwise_coprime_prod_dvd (l : List ℕ) (hpair : l.Pairwise Nat.Coprime)
    (n : ℕ) (hdiv : ∀ a ∈ l, a ∣ n) : l.prod ∣ n := by
  revert hpair hdiv
  induction l with
  | nil => intro _ _; simp
  | cons a l ih =>
    intro hpair hdiv
    have hp := List.pairwise_cons.mp hpair
    have htail := ih hp.2 (fun b hb => hdiv b (List.mem_cons_of_mem a hb))
    have hac : a.Coprime l.prod := Nat.coprime_list_prod_right_iff.mpr hp.1
    simpa only [List.prod_cons] using
      hac.mul_dvd_of_dvd_of_dvd (hdiv a (List.mem_cons_self)) htail
#print axioms Paper7CRTAlgebra.pairwise_coprime_prod_dvd

theorem bounded_integer_crt (l : List ℕ) (hpair : l.Pairwise Nat.Coprime)
    (z : ℤ) (hz : z.natAbs < l.prod) :
    (∀ a ∈ l, (z : ZMod a) = 0) ↔ z = 0 := by
  constructor
  · intro hres
    have hdiv : ∀ a ∈ l, a ∣ z.natAbs := by
      intro a ha
      exact Int.natCast_dvd.mp ((ZMod.intCast_zmod_eq_zero_iff_dvd z a).mp (hres a ha))
    have hp := pairwise_coprime_prod_dvd l hpair z.natAbs hdiv
    by_contra hn
    have hpos : 0 < z.natAbs := by
      have : z.natAbs ≠ 0 := fun h => hn (Int.natAbs_eq_zero.mp h)
      omega
    exact (not_le_of_gt hz) (Nat.le_of_dvd hpos hp)
  · rintro rfl
    intro a _
    exact Int.cast_zero
#print axioms Paper7CRTAlgebra.bounded_integer_crt

/-- Six fixed Euclidean GCD computations, not a factorization or primality tactic. -/
theorem actual_aPrimes_pairwise_coprime : aPrimes.Pairwise Nat.Coprime := by
  norm_num [aPrimes, List.pairwise_cons, Nat.Coprime]
#print axioms Paper7CRTAlgebra.actual_aPrimes_pairwise_coprime

/-- Four fixed integer multiplications and one exact comparison. -/
theorem actual_aPrimes_product_bound : (2 : ℕ) ^ 240 < aPrimes.prod := by
  norm_num [aPrimes]
#print axioms Paper7CRTAlgebra.actual_aPrimes_product_bound

theorem actual_aPrimes_upper_bound : ∀ a ∈ aPrimes, a < (2 : ℕ) ^ 62 := by
  intro a ha
  simp only [aPrimes, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl <;> norm_num
#print axioms Paper7CRTAlgebra.actual_aPrimes_upper_bound

theorem actual_bounded_integer_crt (z : ℤ) (hz : z.natAbs < aPrimes.prod) :
    (∀ a ∈ aPrimes, (z : ZMod a) = 0) ↔ z = 0 :=
  bounded_integer_crt aPrimes actual_aPrimes_pairwise_coprime z hz
#print axioms Paper7CRTAlgebra.actual_bounded_integer_crt

end Paper7CRTAlgebra
