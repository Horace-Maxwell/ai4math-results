import Research.Backfill.Paper7.ChallengeV2

/-! Integer counting and final arithmetic used by Lemma41. These statements do
not assert that the cycle characteristic-root multiset has already been identified. -/
set_option autoImplicit false
noncomputable section
namespace Paper7Lemma41

/-- Integer frequencies satisfying the paper's centered strict inequality. -/
def centeredFrequencies (b : ℕ) : Finset ℤ :=
  Finset.Icc (-(((b - 1) / 6 : ℕ) : ℤ)) (((b - 1) / 6 : ℕ) : ℤ)
#print axioms Paper7Lemma41.centeredFrequencies

theorem mem_centeredFrequencies (b : ℕ) (hb : 1 ≤ b) (j : ℤ) :
    j ∈ centeredFrequencies b ↔ 6 * |j| < (b : ℤ) := by
  rw [centeredFrequencies, Finset.mem_Icc, ← abs_le]
  omega
#print axioms Paper7Lemma41.mem_centeredFrequencies

theorem centeredFrequencies_card (b : ℕ) (hb : 1 ≤ b) :
    (centeredFrequencies b).card = 2 * ((b + 5) / 6) - 1 := by
  rw [centeredFrequencies, Int.card_Icc]
  omega
#print axioms Paper7Lemma41.centeredFrequencies_card

theorem ceil_six_count_pos (b : ℕ) (hb : 3 ≤ b) :
    1 ≤ 2 * ((b + 5) / 6) - 1 := by omega
#print axioms Paper7Lemma41.ceil_six_count_pos

/-- Pure arithmetic, to be instantiated only after the true spectral lower bound. -/
theorem cycle_length_le_twelve_of_count (b s : ℕ) (_hb : 3 ≤ b)
    (hlower : 2 * ((b + 5) / 6) - 1 ≤ s) (hupper : s ≤ 4) : b ≤ 12 := by omega
#print axioms Paper7Lemma41.cycle_length_le_twelve_of_count

theorem cycle_length_le_eighteen_of_count (b s : ℕ) (_hb : 3 ≤ b)
    (hlower : 2 * ((b + 5) / 6) - 1 ≤ s) (hupper : s ≤ 5) : b ≤ 18 := by omega
#print axioms Paper7Lemma41.cycle_length_le_eighteen_of_count

theorem count_eq_five_at_fourteen_sixteen_eighteen (b s : ℕ)
    (hb : b = 14 ∨ b = 16 ∨ b = 18)
    (hlower : 2 * ((b + 5) / 6) - 1 ≤ s) (hupper : s ≤ 5) : s = 5 := by
  rcases hb with rfl | rfl | rfl <;> omega
#print axioms Paper7Lemma41.count_eq_five_at_fourteen_sixteen_eighteen

theorem mod_four_two_cycle_cases (b : ℕ) (hb : 3 ≤ b) (hupper : b ≤ 18)
    (hmod : b % 4 = 2) : b = 6 ∨ b = 10 ∨ b = 14 ∨ b = 18 := by omega
#print axioms Paper7Lemma41.mod_four_two_cycle_cases

end Paper7Lemma41
