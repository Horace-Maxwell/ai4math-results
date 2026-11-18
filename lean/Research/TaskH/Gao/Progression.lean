import Research.TaskH.Gao.Challenge

/-! Explicit finite arithmetic-progression sum witnesses. These are symbolic
natural-number proofs for arbitrary sizes, not an enumerated sumset table. -/
set_option autoImplicit false
namespace TaskH.Gao

theorem sum_indices_unit {s t : ℕ} (hs : 1 ≤ s) (ht : 1 ≤ t)
    (n : ℕ) (hn : n < s + t - 1) :
    ∃ i < s, ∃ j < t, n = i + j := by
  by_cases hns : n < s
  · exact ⟨n, hns, 0, by omega, by omega⟩
  · exact ⟨s - 1, by omega, n - (s - 1), by omega, by omega⟩

/-- A unit-step progression of size at least two fills the gaps between
successive translates of the step-two progression. -/
theorem sum_indices_one_two {s t : ℕ} (hs : 2 ≤ s) (ht : 1 ≤ t)
    (n : ℕ) (hn : n < s + t - 1) :
    ∃ i < s, ∃ j < t, n = i + 2 * j := by
  have hrem : n % 2 < 2 := Nat.mod_lt n (by omega)
  have hdiv : n % 2 + 2 * (n / 2) = n := Nat.mod_add_div n 2
  by_cases hnt : n < 2 * t
  · exact ⟨n % 2, by omega, n / 2, by omega, by omega⟩
  · exact ⟨n - 2 * (t - 1), by omega, t - 1, by omega, by omega⟩

/-- The first s+t-1 terms of a genuine admissible sum progression have
explicit witnesses in the two original finite progressions. Singleton
progressions choose the other step rather than assuming both steps agree. -/
theorem admissible_sum_indices {s t : ℕ} (hs : 1 ≤ s) (ht : 1 ≤ t)
    (d e : ℕ) (hd : d = 1 ∨ d = 2) (he : e = 1 ∨ e = 2) :
    ∃ step : ℕ, (step = 1 ∨ step = 2) ∧
      ∀ n : ℕ, n < s + t - 1 → ∃ i < s, ∃ j < t, n * step = i * d + j * e := by
  by_cases hs1 : s = 1
  · subst s
    refine ⟨e, he, ?_⟩
    intro n hn
    exact ⟨0, by omega, n, by omega, by simp⟩
  by_cases ht1 : t = 1
  · subst t
    refine ⟨d, hd, ?_⟩
    intro n hn
    exact ⟨n, by omega, 0, by omega, by simp⟩
  have hs2 : 2 ≤ s := by omega
  have ht2 : 2 ≤ t := by omega
  rcases hd with rfl | rfl
  · rcases he with rfl | rfl
    · refine ⟨1, Or.inl rfl, ?_⟩
      intro n hn
      obtain ⟨i, hi, j, hj, hij⟩ := sum_indices_unit hs ht n hn
      exact ⟨i, hi, j, hj, by omega⟩
    · refine ⟨1, Or.inl rfl, ?_⟩
      intro n hn
      obtain ⟨i, hi, j, hj, hij⟩ := sum_indices_one_two hs2 ht n hn
      exact ⟨i, hi, j, hj, by omega⟩
  · rcases he with rfl | rfl
    · refine ⟨1, Or.inl rfl, ?_⟩
      intro n hn
      obtain ⟨j, hj, i, hi, hij⟩ := sum_indices_one_two ht2 hs n (by omega)
      exact ⟨i, hi, j, hj, by omega⟩
    · refine ⟨2, Or.inr rfl, ?_⟩
      intro n hn
      obtain ⟨i, hi, j, hj, hij⟩ := sum_indices_unit hs ht n hn
      exact ⟨i, hi, j, hj, by omega⟩

#print axioms sum_indices_unit
#print axioms sum_indices_one_two
#print axioms admissible_sum_indices
end TaskH.Gao
