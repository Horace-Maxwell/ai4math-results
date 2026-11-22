import Mathlib

namespace TaskP.RectangleDefect.Challenge

abbrev Counts (k : ℕ) := Fin k → ℕ

def area {k : ℕ} (m : Counts k) : ℕ := ∑ i, (i.val + 1) * m i

abbrev Tile {k : ℕ} (m : Counts k) := (i : Fin k) × Fin (m i)

def tileSize {k : ℕ} {m : Counts k} (vertical : Tile m → Bool) (t : Tile m) : ℝ × ℝ :=
  if vertical t then ((t.1.val + 1 : ℕ), 1) else (1, (t.1.val + 1 : ℕ))

/-- A geometric partition by axis-parallel closed rectangles, with real anchors.
    Only the interiors of distinct occurrences must be disjoint. -/
def tiles {k : ℕ} (m : Counts k) (n : ℕ) : Prop :=
  ∃ (anchor : Tile m → ℝ × ℝ) (vertical : Tile m → Bool),
    let closed := fun t : Tile m =>
      Set.Icc (anchor t).1 ((anchor t).1 + (tileSize vertical t).1) ×ˢ
      Set.Icc (anchor t).2 ((anchor t).2 + (tileSize vertical t).2)
    let inside := fun t : Tile m =>
      Set.Ioo (anchor t).1 ((anchor t).1 + (tileSize vertical t).1) ×ˢ
      Set.Ioo (anchor t).2 ((anchor t).2 + (tileSize vertical t).2)
    (⋃ t, closed t) = Set.Icc 0 2 ×ˢ Set.Icc 0 (n : ℝ) ∧
      ∀ t u : Tile m, t ≠ u → Disjoint (inside t) (inside u)

def multisets (k n : ℕ) : Set (Counts k) := {m | area m = 2 * n}

noncomputable def defect (k n : ℕ) : ℕ :=
  (multisets k n).ncard - {m ∈ multisets k n | tiles m n}.ncard

def exponent (k : ℕ) : ℕ := k / 2 - 2

def SharpBound : Prop :=
  (∀ k n, (multisets k n).Finite) ∧
  (∀ k n, 1 ≤ k → k ≤ 2 → 0 < n → defect k n = 0) ∧
  ∀ k, 3 ≤ k →
    (∃ C : ℕ, 0 < C ∧ ∀ n, 0 < n → defect k n ≤ C * (n + 1) ^ exponent k) ∧
    (∃ C : ℕ, 0 < C ∧ ∀ N, ∃ n ≥ N, (n + 1) ^ exponent k ≤ C * defect k n) ∧
    (6 ≤ k → ∃ C N : ℕ, 0 < C ∧ ∀ n ≥ N, Odd n →
      (n + 1) ^ exponent k ≤ C * defect k n)

end TaskP.RectangleDefect.Challenge
