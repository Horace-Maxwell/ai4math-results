import Research.TaskU.H5.Witness
import Mathlib.Tactic

namespace TaskU.H5.SmallMultiples

/-- The only small cofactors divisible by 5 are 5 and 10; even then none supplies
the extra five powers required by the strengthened obstruction. -/
theorem insufficient (m : ℤ) (hm : 1 ≤ m) (hm' : m ≤ 10) :
    ¬ (5 ^ 33 : ℤ) ∣ 5 ^ 28 * m := by
  interval_cases m <;> decide +kernel

theorem no_inert_fourth_power (m : ℤ) (hm : 1 ≤ m) (hm' : m ≤ 10) :
    ¬ (2 ^ 4 : ℤ) ∣ 5 ^ 28 * m ∧ ¬ (3 ^ 4 : ℤ) ∣ 5 ^ 28 * m ∧
    ¬ (7 ^ 4 : ℤ) ∣ 5 ^ 28 * m := by
  interval_cases m <;> decide +kernel

/-- An ordinary norm already known to be 5 times a positive divisor of the
small cofactor must equal 5 if it has only one power of 5 and each of the three
inert primes contributes a fourth power whenever it divides the norm. -/
theorem ordinary_norm_eq (m n : ℤ) (hm : 1 ≤ m) (hm' : m ≤ 10)
    (hn : 0 < n) (hd : n ∣ m) (h5 : ¬ (5 : ℤ) ∣ n)
    (h2 : (2 : ℤ) ∣ n → 2^4 ∣ 5^28*m)
    (h3 : (3 : ℤ) ∣ n → 3^4 ∣ 5^28*m)
    (h7 : (7 : ℤ) ∣ n → 7^4 ∣ 5^28*m) : n = 1 := by
  obtain ⟨hN2,hN3,hN7⟩ := no_inert_fourth_power m hm hm'
  have hn' : n ≤ 10 := le_trans (Int.le_of_dvd (by omega) hd) hm'
  have hN : ¬ (2 : ℤ) ∣ n ∧ ¬ (3 : ℤ) ∣ n ∧ ¬ (7 : ℤ) ∣ n :=
    ⟨fun h => hN2 (h2 h), fun h => hN3 (h3 h), fun h => hN7 (h7 h)⟩
  interval_cases n <;> first
    | rfl
    | exact (h5 (by decide)).elim
    | exact (hN.1 (by decide)).elim
    | exact (hN.2.1 (by decide)).elim
    | exact (hN.2.2 (by decide)).elim

theorem least_from_small (base : ∀ f : H → ℤ, 5 ∣ groupDet f → 5^28 ∣ groupDet f)
    (small : ∀ (f : H → ℤ) (m : ℤ), 1 ≤ m → m ≤ 10 →
      groupDet f = 5^28*m → 5^33 ∣ groupDet f) : Challenge.leastPositiveMultiple := by
  constructor
  · refine ⟨by decide, by decide, witness, Proof.witnessValue⟩
  · rintro d ⟨hd, h5, f, rfl⟩
    obtain ⟨m, he⟩ := base f h5
    by_contra! hlt
    have hm : 1 ≤ m := by omega
    have hm' : m ≤ 10 := by omega
    exact insufficient m hm hm' (he ▸ small f m hm hm' he)

end TaskU.H5.SmallMultiples
