import Research.Backfill.Paper7.CycleFourier
import Mathlib

/-! Source-only author candidate by Codex subagent p6_binding_spotcheck.
This connects the actual Fin-indexed cycle adjacency matrix to the Fourier
operator and its full complex characteristic polynomial. The distinct-neighbour
argument follows the accepted Lemma22ExceptionalOffsets.cycle_adjacency_entry
source, with complex entries and direct Fin subtraction/addition. No compilation
or kernel acceptance of this candidate is claimed. -/

set_option autoImplicit false
noncomputable section

open scoped Matrix BigOperators
open Polynomial

namespace Paper7Lemma41

/-- A cycle of at least three vertices has exactly these two distinct neighbours. -/
theorem cycle_complex_adjacency_entry (n : ℕ) (k j : Fin (n + 3)) :
    (SimpleGraph.cycleGraph (n + 3)).adjMatrix ℂ k j =
      (if j = k - 1 then 1 else 0) + (if j = k + 1 then 1 else 0) := by
  classical
  have hne : k - 1 ≠ k + 1 := by
    simp only [ne_eq, sub_eq_iff_eq_add, add_assoc k, left_eq_add]
    exact ne_of_beq_false rfl
  have hadj : (SimpleGraph.cycleGraph (n + 3)).Adj k j ↔
      j = k - 1 ∨ j = k + 1 := by
    change j ∈ (SimpleGraph.cycleGraph (n + 3)).neighborSet k ↔ _
    rw [SimpleGraph.cycleGraph_neighborSet]
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  simp only [SimpleGraph.adjMatrix_apply, hadj]
  by_cases hp : j = k - 1
  · have hn : j ≠ k + 1 := fun h => hne (hp.symm.trans h)
    rw [ite_eq_left (Or.inl hp), ite_eq_left hp, ite_eq_right hn, add_zero]
  · by_cases hn : j = k + 1
    · rw [ite_eq_left (Or.inr hn), ite_eq_right hp, ite_eq_left hn, zero_add]
    · rw [ite_eq_right (not_or.mpr ⟨hp, hn⟩), ite_eq_right hp, ite_eq_right hn, add_zero]
#print axioms Paper7Lemma41.cycle_complex_adjacency_entry

/-- Multiplication by the actual complex adjacency matrix is the neighbour sum. -/
theorem cycle_complex_mulVec_entry (n : ℕ) (y : Fin (n + 3) → ℂ)
    (k : Fin (n + 3)) :
    ((SimpleGraph.cycleGraph (n + 3)).adjMatrix ℂ *ᵥ y) k =
      y (k - 1) + y (k + 1) := by
  classical
  simp only [Matrix.mulVec_apply_eq_sum, cycle_complex_adjacency_entry,
    add_mul, ite_mul, one_mul, zero_mul, Finset.sum_add_distrib]
  simp
#print axioms Paper7Lemma41.cycle_complex_mulVec_entry

/-- For a positive modulus, ZMod and Fin have the same underlying index type. -/
theorem cycle_complex_toLin_eq (n : ℕ) :
    ((SimpleGraph.cycleGraph (n + 3)).adjMatrix ℂ).toLin' =
      cycleZModOperator (n + 3) := by
  apply LinearMap.ext
  intro y
  funext k
  change ((SimpleGraph.cycleGraph (n + 3)).adjMatrix ℂ *ᵥ y) k =
    y (k - 1) + y (k + 1)
  exact cycle_complex_mulVec_entry n y k
#print axioms Paper7Lemma41.cycle_complex_toLin_eq

/-- The actual cycle characteristic polynomial, with all Fourier frequencies.
The typeclass assumption only supplies the finite ZMod index type; `hb` implies it. -/
theorem cycleGraph_charpoly_complex (b : ℕ) [NeZero b] (hb : 3 ≤ b) :
    ((SimpleGraph.cycleGraph b).adjMatrix ℂ).charpoly =
      ∏ k : ZMod b, (X - C (ZMod.stdAddChar k + ZMod.stdAddChar (-k))) := by
  obtain ⟨n, rfl⟩ : ∃ n, b = n + 3 := ⟨b - 3, by omega⟩
  rw [← Matrix.charpoly_toLin', cycle_complex_toLin_eq]
  exact cycleZModOperator_charpoly (n + 3)
#print axioms Paper7Lemma41.cycleGraph_charpoly_complex

end Paper7Lemma41
