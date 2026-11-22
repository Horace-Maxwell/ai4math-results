import Research.TaskP.RectangleDefect.Challenge

namespace TaskP.RectangleDefect

open Challenge

def RowSplit {k : ℕ} (m : Counts k) (n : ℕ) : Prop :=
  ∃ top bottom vert : Counts k,
    (∀ i, top i + bottom i + vert i = m i) ∧
    (∀ i, vert i ≠ 0 → i.val + 1 = 2) ∧
    area top + (∑ i, vert i) = n ∧ area bottom + (∑ i, vert i) = n

end TaskP.RectangleDefect
