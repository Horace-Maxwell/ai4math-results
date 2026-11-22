import Research.TaskP.RectangleDefect.BoundedBezout

namespace TaskP.RectangleDefect

open Challenge

theorem split_of_correction {k n B : ℕ} {m : Counts k} (hm : area m = 2*n) (vert : Counts k)
    (vsize : ∀ i, vert i ≠ 0 → i.val+1=2) (vle : ∀ i, vert i ≤ 1)
    (hv : ∀ i, m i < 2*B+4 → vert i=0) (c : Fin k → ℤ)
    (hs : ∀ i, m i < 2*B+4 → c i=0) (hb : ∀ i, (c i).natAbs ≤ B)
    (eqn : (area (fun i => m i / 2) : ℤ) + weighted c + (∑ i, vert i : ℕ) = n) :
    RowSplit m n := by
  let a (i : Fin k) : ℤ := (m i / 2 : ℕ) + c i
  have range_a (i : Fin k) : 0 ≤ a i ∧ a i + vert i ≤ m i := by
    dsimp [a]
    by_cases h : m i < 2*B+4
    · rw [hv i h, hs i h]
      omega
    · have hc := hb i
      have hvi := vle i
      omega
  let top (i : Fin k) := (a i).toNat
  let bottom (i : Fin k) := m i - top i - vert i
  have casttop (i : Fin k) : (top i : ℤ) = a i := Int.toNat_of_nonneg (range_a i).1
  have split (i : Fin k) : top i + bottom i + vert i = m i := by
    dsimp [bottom]
    have h := (range_a i).2
    rw [← casttop] at h
    omega
  have areat : (area top : ℤ) = (area (fun i => m i / 2) : ℤ) + weighted c := by
    unfold area weighted
    push_cast
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [casttop]
    dsimp [a]
    ring
  have topok : area top + (∑ i, vert i) = n := by omega
  have areav : area vert = 2 * ∑ i, vert i := by
    rw [area, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    by_cases h : vert i = 0
    · simp [h]
    · rw [vsize i h]
  have conservation : area top + area bottom + area vert = area m := by
    unfold area
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [← Nat.mul_add, ← Nat.mul_add, split]
  exact ⟨top, bottom, vert, split, vsize, topok, by omega⟩

end TaskP.RectangleDefect
