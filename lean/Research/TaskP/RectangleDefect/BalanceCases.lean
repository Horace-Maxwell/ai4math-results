import Research.TaskP.RectangleDefect.BalanceConstruction
import Research.TaskP.RectangleDefect.UpperCount

namespace TaskP.RectangleDefect

open Challenge

/-- Rounding every multiplicity down to half leaves a bounded width still to fill. -/
theorem half_gap {k n : ℕ} (m : Counts k) (ha : area m = 2*n) :
    ∃ h ≤ lengthBudget k, area (fun i => m i / 2) + h = n := by
  let b := area (fun i => m i / 2)
  have lower : 2*b ≤ area m := by
    dsimp [b,area]
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    have hh : 2*(m i/2) ≤ m i := by omega
    calc 2*((i.val+1)*(m i/2)) = (i.val+1)*(2*(m i/2)) := by ring
         _ ≤ _ := Nat.mul_le_mul_left _ hh
  have upper : area m ≤ 2*b + lengthBudget k := by
    dsimp [b,area,lengthBudget]
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro i _
    have hh : m i ≤ 2*(m i/2)+1 := by omega
    calc (i.val+1)*m i ≤ (i.val+1)*(2*(m i/2)+1) := Nat.mul_le_mul_left _ hh
         _ = _ := by ring
  exact ⟨n-b, by omega, by omega⟩

theorem fail_gcd (k : ℕ) :
    ∃ T > 0, ∀ n (m : Counts k), area m=2*n → ¬ RowSplit m n → (heavy T m).Nonempty →
      3 ≤ (heavy T m).gcd (fun i => i.val+1) ∨
        ((heavy T m).gcd (fun i => i.val+1) = 2 ∧ ∀ i ∈ heavy T m, i.val+1 ≠ 2) := by
  classical
  obtain ⟨B, uniform⟩ := bounded_combination k
  refine ⟨2*B+4, by omega, ?_⟩
  intro n m hm fails hex
  let J := heavy (2*B+4) m
  let g := J.gcd (fun i => i.val+1)
  have nz : g ≠ 0 := by
    intro hg
    obtain ⟨i,hi⟩ := hex
    have he := (Finset.gcd_eq_zero_iff.mp hg) i hi
    omega
  obtain ⟨h,hbound,hgap⟩ := half_gap m hm
  have fill (v : Counts k) (vsize : ∀ i, v i ≠ 0 → i.val+1=2)
      (vle : ∀ i, v i ≤ 1) (vsupp : ∀ i, m i < 2*B+4 → v i=0)
      (vtotal : (∑ i, v i) ≤ h) (dvd : g ∣ h - ∑ i, v i) : False := by
    obtain ⟨c,cs,cb,ce⟩ := uniform J (h - ∑ i, v i) (by omega) dvd
    apply fails
    refine split_of_correction hm v vsize vle vsupp c ?_ cb ?_
    · intro i hi
      apply cs i
      simpa only [J,heavy,Finset.mem_filter,Finset.mem_univ,true_and,not_le] using hi
    · have hd : h - (∑ i, v i) + (∑ i, v i) = h := Nat.sub_add_cancel vtotal
      rw [ce]
      exact_mod_cast (show area (fun i => m i / 2) + (h-(∑ i, v i)) + (∑ i, v i) = n by omega)
  by_cases three : 3 ≤ g
  · exact Or.inl three
  by_cases one : g = 1
  · exfalso
    apply fill (fun _ => 0) (by simp) (by simp) (by simp) (by simp)
    simp [one]
  have two : g = 2 := by omega
  refine Or.inr ⟨two,?_⟩
  intro j hj hsize
  let v : Counts k := fun i => if i=j then h%2 else 0
  have total : (∑ i, v i) = h%2 := by simp [v]
  apply fill v
  · intro i hi
    by_cases e : i = j
    · simpa only [e] using hsize
    · simp [v,e] at hi
  · intro i
    dsimp only [v]
    split <;> omega
  · intro i hi
    have hmj := (Finset.mem_filter.mp hj).2
    have ne : i ≠ j := by intro eq; subst i; omega
    simp [v,ne]
  · rw [total]
    omega
  · rw [two,total]
    omega

end TaskP.RectangleDefect
