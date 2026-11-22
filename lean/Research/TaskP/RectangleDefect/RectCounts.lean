import Research.TaskP.RectangleDefect.Challenge

namespace TaskP.RectangleDefect
open Challenge

theorem entry_le_area {k : ℕ} (m : Counts k) (i : Fin k) : m i ≤ area m := by
  have ht : (i.val+1)*m i ≤ area m :=
    Finset.single_le_sum (fun j _ => Nat.zero_le ((j.val+1)*m j)) (Finset.mem_univ i)
  exact le_trans (by nlinarith [Nat.zero_le (i.val * m i)]) ht

theorem multisets_finite (k n : ℕ) : (multisets k n).Finite := by
  apply (Set.finite_Icc (0 : Counts k) (fun _ => 2*n)).subset
  intro m hm
  exact ⟨fun _ => Nat.zero_le _,fun i => (entry_le_area m i).trans_eq hm⟩

def failures (k n : ℕ) : Set (Counts k) := {m ∈ multisets k n | ¬ tiles m n}

theorem defect_eq_failures (k n : ℕ) : defect k n = (failures k n).ncard := by
  classical
  have sub : {m ∈ multisets k n | tiles m n} ⊆ multisets k n := fun _ h => h.1
  have he : failures k n = multisets k n \ {m ∈ multisets k n | tiles m n} := by
    ext m
    simp [failures]
  rw [he,Set.ncard_sdiff sub ((multisets_finite k n).subset sub)]
  rfl

end TaskP.RectangleDefect
