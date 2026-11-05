import Research.Backfill.Paper7.CycleCountArithmetic
import Mathlib

/-! Source-only author candidate by Codex subagent p6_binding_spotcheck.
The strict finite frequency condition is identified with two disjoint Fin
intervals, including the empty upper interval when (b - 1) / 6 = 0.
No spectral formula is assumed here. No compilation or kernel acceptance
of this candidate is claimed. -/

set_option autoImplicit false
noncomputable section

namespace Paper7Lemma41

/-- Exact cardinality of the finite frequencies satisfying the strict threshold. -/
theorem cycle_frequency_card (b : ℕ) (hb : 3 ≤ b) :
    (Finset.univ.filter (fun j : Fin b =>
      6 * j.val < b ∨ 6 * (b - j.val) < b)).card =
        2 * ((b + 5) / 6) - 1 := by
  classical
  let k : ℕ := (b - 1) / 6
  have hk : 6 * k ≤ b - 1 ∧ b - 1 < 6 * (k + 1) := by
    dsimp only [k]
    omega
  have hkb : k < b := by omega
  have hcut : b - 1 - k < b := by omega
  have hset :
      Finset.univ.filter (fun j : Fin b =>
        6 * j.val < b ∨ 6 * (b - j.val) < b) =
      Finset.Iic (⟨k, hkb⟩ : Fin b) ∪
        Finset.Ioi (⟨b - 1 - k, hcut⟩ : Fin b) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_union, Finset.mem_Iic, Finset.mem_Ioi]
    change (6 * j.val < b ∨ 6 * (b - j.val) < b) ↔
      j.val ≤ k ∨ b - 1 - k < j.val
    have hj : j.val < b := j.isLt
    omega
  have hdisj : Disjoint (Finset.Iic (⟨k, hkb⟩ : Fin b))
      (Finset.Ioi (⟨b - 1 - k, hcut⟩ : Fin b)) := by
    apply Finset.disjoint_left.mpr
    intro j hjlow hjhigh
    have hlo := Finset.mem_Iic.mp hjlow
    have hhi := Finset.mem_Ioi.mp hjhigh
    change j.val ≤ k at hlo
    change b - 1 - k < j.val at hhi
    omega
  rw [hset, Finset.card_union_of_disjoint hdisj, Fin.card_Iic, Fin.card_Ioi]
  change (k + 1) + (b - 1 - (b - 1 - k)) = 2 * ((b + 5) / 6) - 1
  have htail : b - 1 - (b - 1 - k) = k := by omega
  rw [htail]
  dsimp only [k]
  omega
#print axioms Paper7Lemma41.cycle_frequency_card

end Paper7Lemma41
