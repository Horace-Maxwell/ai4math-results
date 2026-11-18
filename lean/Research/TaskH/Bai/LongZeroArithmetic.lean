import Mathlib
set_option autoImplicit false
namespace TaskH.Bai

/-- A positive bounded shift reaches a genuine next multiple, including residue zero. -/
theorem next_multiple_positive_offset (k A : ℕ) (hk : 0 < k) :
    ∃ j : ℕ, 0 < j ∧ j ≤ k ∧ k ∣ A + j := by
  let j := k - A % k
  have hr := Nat.mod_lt A hk
  have hq := Nat.mod_add_div A k
  have hs := Nat.sub_add_cancel (Nat.le_of_lt hr)
  refine ⟨j, by dsimp [j]; omega, by dsimp [j]; omega, ?_⟩
  refine ⟨A / k + 1, ?_⟩
  dsimp [j]
  nlinarith

/-- For odd k the actual step-one/two AP has a multiple strictly above k. -/
theorem odd_ap_long_zero (k A d : ℕ) (hk : 4 ≤ k) (hodd : k % 2 = 1)
    (hA : 3 ≤ A) (hd : d = 1 ∨ d = 2) :
    ∃ i : ℕ, i < 2 * k - 2 ∧ k ∣ A + i * d ∧ k < A + i * d := by
  rcases hd with rfl | rfl
  · by_cases hsmall : A ≤ 2 * k
    · let i := 2 * k - A
      have he : A + i * 1 = 2 * k := by dsimp [i]; omega
      refine ⟨i, by dsimp [i]; omega, ?_, by omega⟩
      rw [he]
      exact ⟨2, by omega⟩
    · obtain ⟨j, _hjpos, hj, hdiv⟩ := next_multiple_positive_offset k A (by omega)
      exact ⟨j, by omega, by simpa only [Nat.mul_one] using hdiv, by omega⟩
  · by_cases hsmall : A ≤ k
    · by_cases hAe : A % 2 = 0
      · let i := (2 * k - A) / 2
        have he : A + i * 2 = 2 * k := by dsimp [i]; omega
        refine ⟨i, by omega, ?_, by omega⟩
        rw [he]
        exact ⟨2, by omega⟩
      · have hAo : A % 2 = 1 := by omega
        let i := (3 * k - A) / 2
        have he : A + i * 2 = 3 * k := by dsimp [i]; omega
        refine ⟨i, by omega, ?_, by omega⟩
        rw [he]
        exact ⟨3, by omega⟩
    · obtain ⟨j, _hjpos, hj, hdiv⟩ := next_multiple_positive_offset k A (by omega)
      by_cases hje : j % 2 = 0
      · let i := j / 2
        have he : i * 2 = j := by dsimp [i]; omega
        refine ⟨i, by omega, ?_, by omega⟩
        simpa only [he] using hdiv
      · have hjo : j % 2 = 1 := by omega
        let i := (j + k) / 2
        have he : i * 2 = j + k := by dsimp [i]; omega
        have hdiv' : k ∣ A + j + k := dvd_add hdiv (dvd_refl k)
        refine ⟨i, by omega, ?_, by omega⟩
        simpa only [he, Nat.add_assoc] using hdiv'

/-- A sufficiently long consecutive interval above two meets a multiple above q. -/
theorem consecutive_long_zero (q c : ℕ) (hq : 2 ≤ q) (hc : 2 ≤ c) :
    ∃ i : ℕ, i < 2 * q - 1 ∧ q ∣ c + i ∧ q < c + i := by
  by_cases hs : c ≤ 2 * q
  · let i := 2 * q - c
    have he : c + i = 2 * q := by dsimp [i]; omega
    refine ⟨i, by dsimp [i]; omega, ?_, by omega⟩
    rw [he]
    exact ⟨2, by omega⟩
  · obtain ⟨j, _hjpos, hj, hdiv⟩ := next_multiple_positive_offset q c (by omega)
    exact ⟨j, by omega, hdiv, by omega⟩

/-- Even cycle base and step two give a real k-multiple longer than k. -/
theorem even_ap_long_zero (k A : ℕ) (hk : 4 ≤ k) (hke : k % 2 = 0)
    (hA : 3 ≤ A) (hAe : A % 2 = 0) :
    ∃ i : ℕ, i < k - 1 ∧ k ∣ A + i * 2 ∧ k < A + i * 2 := by
  let q := k / 2
  let c := A / 2
  have hkq : k = 2 * q := by dsimp [q]; omega
  have hAc : A = 2 * c := by dsimp [c]; omega
  obtain ⟨i, hi, hdiv, hlong⟩ := consecutive_long_zero q c (by omega) (by omega)
  refine ⟨i, by omega, ?_, by omega⟩
  obtain ⟨m, hm⟩ := hdiv
  refine ⟨m, ?_⟩
  calc
    A + i * 2 = 2 * (c + i) := by omega
    _ = 2 * (q * m) := by rw [hm]
    _ = k * m := by rw [hkq]; ring

#print axioms next_multiple_positive_offset
#print axioms odd_ap_long_zero
#print axioms consecutive_long_zero
#print axioms even_ap_long_zero
end TaskH.Bai
