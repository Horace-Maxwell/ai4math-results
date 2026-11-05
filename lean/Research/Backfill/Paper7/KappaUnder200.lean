import Research.Backfill.Paper7.KappaDivisibility

/-! The finite clause is kernel decidable arithmetic, not a numerical spectrum
test. Source only: these certificates have not been run. -/
set_option autoImplicit false
namespace Paper7Corollary31
open BackfillPaper7.Challenge

theorem kappa_allowed_values (b : ℕ)
    (hb : b ∈ ({3, 15, 27, 39, 63, 75, 87, 99, 123, 135, 147, 159, 183, 195} : Finset ℕ)) :
    kappa b ∣ 2*b := by
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · apply kappa_dvd_of_prime_divisors
    intro q hq hp
    have hq2 := hq.two_le
    have hd : (2 : ℕ).divisors = ({1, 2} : Finset ℕ) := by decide +kernel
    have hm : q - 1 ∈ ({1, 2} : Finset ℕ) := by
      rw [← hd]
      exact Nat.mem_divisors.mpr ⟨by simpa using hp, by decide⟩
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm
    rcases hm with he | he
    · have heq : q = 2 := by omega
      subst q
      norm_num at *
    · have heq : q = 3 := by omega
      subst q
      norm_num at *
  · apply kappa_dvd_of_prime_divisors
    intro q hq hp
    have hq2 := hq.two_le
    have hd : (14 : ℕ).divisors = ({1, 2, 7, 14} : Finset ℕ) := by decide +kernel
    have hm : q - 1 ∈ ({1, 2, 7, 14} : Finset ℕ) := by
      rw [← hd]
      exact Nat.mem_divisors.mpr ⟨by simpa using hp, by decide⟩
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm
    rcases hm with he | he | he | he
    · have heq : q = 2 := by omega
      subst q
      norm_num at *
    · have heq : q = 3 := by omega
      subst q
      norm_num at *
    · have heq : q = 8 := by omega
      subst q
      norm_num at *
    · have heq : q = 15 := by omega
      subst q
      norm_num at *
  · apply kappa_dvd_of_prime_divisors
    intro q hq hp
    have hq2 := hq.two_le
    have hd : (26 : ℕ).divisors = ({1, 2, 13, 26} : Finset ℕ) := by decide +kernel
    have hm : q - 1 ∈ ({1, 2, 13, 26} : Finset ℕ) := by
      rw [← hd]
      exact Nat.mem_divisors.mpr ⟨by simpa using hp, by decide⟩
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm
    rcases hm with he | he | he | he
    · have heq : q = 2 := by omega
      subst q
      norm_num at *
    · have heq : q = 3 := by omega
      subst q
      norm_num at *
    · have heq : q = 14 := by omega
      subst q
      norm_num at *
    · have heq : q = 27 := by omega
      subst q
      norm_num at *
  · apply kappa_dvd_of_prime_divisors
    intro q hq hp
    have hq2 := hq.two_le
    have hd : (38 : ℕ).divisors = ({1, 2, 19, 38} : Finset ℕ) := by decide +kernel
    have hm : q - 1 ∈ ({1, 2, 19, 38} : Finset ℕ) := by
      rw [← hd]
      exact Nat.mem_divisors.mpr ⟨by simpa using hp, by decide⟩
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm
    rcases hm with he | he | he | he
    · have heq : q = 2 := by omega
      subst q
      norm_num at *
    · have heq : q = 3 := by omega
      subst q
      norm_num at *
    · have heq : q = 20 := by omega
      subst q
      norm_num at *
    · have heq : q = 39 := by omega
      subst q
      norm_num at *
  · apply kappa_dvd_of_prime_divisors
    intro q hq hp
    have hq2 := hq.two_le
    have hd : (62 : ℕ).divisors = ({1, 2, 31, 62} : Finset ℕ) := by decide +kernel
    have hm : q - 1 ∈ ({1, 2, 31, 62} : Finset ℕ) := by
      rw [← hd]
      exact Nat.mem_divisors.mpr ⟨by simpa using hp, by decide⟩
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm
    rcases hm with he | he | he | he
    · have heq : q = 2 := by omega
      subst q
      norm_num at *
    · have heq : q = 3 := by omega
      subst q
      norm_num at *
    · have heq : q = 32 := by omega
      subst q
      norm_num at *
    · have heq : q = 63 := by omega
      subst q
      norm_num at *
  · apply kappa_dvd_of_prime_divisors
    intro q hq hp
    have hq2 := hq.two_le
    have hd : (74 : ℕ).divisors = ({1, 2, 37, 74} : Finset ℕ) := by decide +kernel
    have hm : q - 1 ∈ ({1, 2, 37, 74} : Finset ℕ) := by
      rw [← hd]
      exact Nat.mem_divisors.mpr ⟨by simpa using hp, by decide⟩
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm
    rcases hm with he | he | he | he
    · have heq : q = 2 := by omega
      subst q
      norm_num at *
    · have heq : q = 3 := by omega
      subst q
      norm_num at *
    · have heq : q = 38 := by omega
      subst q
      norm_num at *
    · have heq : q = 75 := by omega
      subst q
      norm_num at *
  · apply kappa_dvd_of_prime_divisors
    intro q hq hp
    have hq2 := hq.two_le
    have hd : (86 : ℕ).divisors = ({1, 2, 43, 86} : Finset ℕ) := by decide +kernel
    have hm : q - 1 ∈ ({1, 2, 43, 86} : Finset ℕ) := by
      rw [← hd]
      exact Nat.mem_divisors.mpr ⟨by simpa using hp, by decide⟩
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm
    rcases hm with he | he | he | he
    · have heq : q = 2 := by omega
      subst q
      norm_num at *
    · have heq : q = 3 := by omega
      subst q
      norm_num at *
    · have heq : q = 44 := by omega
      subst q
      norm_num at *
    · have heq : q = 87 := by omega
      subst q
      norm_num at *
  · apply kappa_dvd_of_prime_divisors
    intro q hq hp
    have hq2 := hq.two_le
    have hd : (98 : ℕ).divisors = ({1, 2, 7, 14, 49, 98} : Finset ℕ) := by decide +kernel
    have hm : q - 1 ∈ ({1, 2, 7, 14, 49, 98} : Finset ℕ) := by
      rw [← hd]
      exact Nat.mem_divisors.mpr ⟨by simpa using hp, by decide⟩
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm
    rcases hm with he | he | he | he | he | he
    · have heq : q = 2 := by omega
      subst q
      norm_num at *
    · have heq : q = 3 := by omega
      subst q
      norm_num at *
    · have heq : q = 8 := by omega
      subst q
      norm_num at *
    · have heq : q = 15 := by omega
      subst q
      norm_num at *
    · have heq : q = 50 := by omega
      subst q
      norm_num at *
    · have heq : q = 99 := by omega
      subst q
      norm_num at *
  · apply kappa_dvd_of_prime_divisors
    intro q hq hp
    have hq2 := hq.two_le
    have hd : (122 : ℕ).divisors = ({1, 2, 61, 122} : Finset ℕ) := by decide +kernel
    have hm : q - 1 ∈ ({1, 2, 61, 122} : Finset ℕ) := by
      rw [← hd]
      exact Nat.mem_divisors.mpr ⟨by simpa using hp, by decide⟩
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm
    rcases hm with he | he | he | he
    · have heq : q = 2 := by omega
      subst q
      norm_num at *
    · have heq : q = 3 := by omega
      subst q
      norm_num at *
    · have heq : q = 62 := by omega
      subst q
      norm_num at *
    · have heq : q = 123 := by omega
      subst q
      norm_num at *
  · apply kappa_dvd_of_prime_divisors
    intro q hq hp
    have hq2 := hq.two_le
    have hd : (134 : ℕ).divisors = ({1, 2, 67, 134} : Finset ℕ) := by decide +kernel
    have hm : q - 1 ∈ ({1, 2, 67, 134} : Finset ℕ) := by
      rw [← hd]
      exact Nat.mem_divisors.mpr ⟨by simpa using hp, by decide⟩
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm
    rcases hm with he | he | he | he
    · have heq : q = 2 := by omega
      subst q
      norm_num at *
    · have heq : q = 3 := by omega
      subst q
      norm_num at *
    · have heq : q = 68 := by omega
      subst q
      norm_num at *
    · have heq : q = 135 := by omega
      subst q
      norm_num at *
  · apply kappa_dvd_of_prime_divisors
    intro q hq hp
    have hq2 := hq.two_le
    have hd : (146 : ℕ).divisors = ({1, 2, 73, 146} : Finset ℕ) := by decide +kernel
    have hm : q - 1 ∈ ({1, 2, 73, 146} : Finset ℕ) := by
      rw [← hd]
      exact Nat.mem_divisors.mpr ⟨by simpa using hp, by decide⟩
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm
    rcases hm with he | he | he | he
    · have heq : q = 2 := by omega
      subst q
      norm_num at *
    · have heq : q = 3 := by omega
      subst q
      norm_num at *
    · have heq : q = 74 := by omega
      subst q
      norm_num at *
    · have heq : q = 147 := by omega
      subst q
      norm_num at *
  · apply kappa_dvd_of_prime_divisors
    intro q hq hp
    have hq2 := hq.two_le
    have hd : (158 : ℕ).divisors = ({1, 2, 79, 158} : Finset ℕ) := by decide +kernel
    have hm : q - 1 ∈ ({1, 2, 79, 158} : Finset ℕ) := by
      rw [← hd]
      exact Nat.mem_divisors.mpr ⟨by simpa using hp, by decide⟩
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm
    rcases hm with he | he | he | he
    · have heq : q = 2 := by omega
      subst q
      norm_num at *
    · have heq : q = 3 := by omega
      subst q
      norm_num at *
    · have heq : q = 80 := by omega
      subst q
      norm_num at *
    · have heq : q = 159 := by omega
      subst q
      norm_num at *
  · apply kappa_dvd_of_prime_divisors
    intro q hq hp
    have hq2 := hq.two_le
    have hd : (182 : ℕ).divisors = ({1, 2, 7, 13, 14, 26, 91, 182} : Finset ℕ) := by decide +kernel
    have hm : q - 1 ∈ ({1, 2, 7, 13, 14, 26, 91, 182} : Finset ℕ) := by
      rw [← hd]
      exact Nat.mem_divisors.mpr ⟨by simpa using hp, by decide⟩
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm
    rcases hm with he | he | he | he | he | he | he | he
    · have heq : q = 2 := by omega
      subst q
      norm_num at *
    · have heq : q = 3 := by omega
      subst q
      norm_num at *
    · have heq : q = 8 := by omega
      subst q
      norm_num at *
    · have heq : q = 14 := by omega
      subst q
      norm_num at *
    · have heq : q = 15 := by omega
      subst q
      norm_num at *
    · have heq : q = 27 := by omega
      subst q
      norm_num at *
    · have heq : q = 92 := by omega
      subst q
      norm_num at *
    · have heq : q = 183 := by omega
      subst q
      norm_num at *
  · apply kappa_dvd_of_prime_divisors
    intro q hq hp
    have hq2 := hq.two_le
    have hd : (194 : ℕ).divisors = ({1, 2, 97, 194} : Finset ℕ) := by decide +kernel
    have hm : q - 1 ∈ ({1, 2, 97, 194} : Finset ℕ) := by
      rw [← hd]
      exact Nat.mem_divisors.mpr ⟨by simpa using hp, by decide⟩
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm
    rcases hm with he | he | he | he
    · have heq : q = 2 := by omega
      subst q
      norm_num at *
    · have heq : q = 3 := by omega
      subst q
      norm_num at *
    · have heq : q = 98 := by omega
      subst q
      norm_num at *
    · have heq : q = 195 := by omega
      subst q
      norm_num at *
#print axioms Paper7Corollary31.kappa_allowed_values

theorem kappa_under_200 (b : ℕ) (hb : 3 ≤ b) (h200 : b < 200) (ho : Odd b) :
    kappa b ∣ 2*b ↔
      b ∈ ({3, 15, 27, 39, 63, 75, 87, 99, 123, 135, 147, 159, 183, 195} : Finset ℕ) := by
  constructor
  · intro hk
    have hthree := three_dvd_of_kappa b hb ho hk
    obtain ⟨u, hu⟩ := ho
    obtain ⟨v, hv⟩ := hthree
    have hform : b = 6*(b/6)+3 := by omega
    obtain ⟨j, hj, rfl⟩ : ∃ j : ℕ, j ≤ 32 ∧ b = 6*j+3 :=
      ⟨b/6, by omega, hform⟩
    interval_cases j <;> norm_num
    all_goals first
      | solve | refine kappa_prime_obstruction _ 5 ?_ ?_ ?_ ?_ hk <;> norm_num
      | solve | refine kappa_prime_obstruction _ 11 ?_ ?_ ?_ ?_ hk <;> norm_num
      | solve | refine kappa_prime_obstruction _ 23 ?_ ?_ ?_ ?_ hk <;> norm_num
      | solve | refine kappa_prime_obstruction _ 53 ?_ ?_ ?_ ?_ hk <;> norm_num
      | solve | refine kappa_prime_obstruction _ 83 ?_ ?_ ?_ ?_ hk <;> norm_num
  · exact kappa_allowed_values b
#print axioms Paper7Corollary31.kappa_under_200

end Paper7Corollary31
