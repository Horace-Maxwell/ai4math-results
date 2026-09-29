import Research.HKOTriameter
import Research.Backfill.Paper4.Proof.Readings

/-! The complete frozen TheoremA_i, TheoremA_ii and TheoremB_ii.
The old module supplies certified graph distances and median witnesses.
This module supplies the additional uniqueness statements and reading clauses.
Compilation and acceptance evidence is recorded separately. -/
set_option autoImplicit false

namespace CodexPaper4
open BackfillPaper4

namespace ConcreteCore

/-- The concrete graphs have exactly the same definitions, including edge lists. -/
lemma G1_eq : Challenge.G1 = HKOTriameter.G1 := rfl
lemma G2_eq : Challenge.G2 = HKOTriameter.G2 := rfl

lemma G1_connected : Challenge.G1.Connected := HKOTriameter.G1_connected
lemma G2_connected : Challenge.G2.Connected := HKOTriameter.G2_connected
lemma G1_median : Challenge.IsMedian Challenge.G1 := HKOTriameter.G1_median
lemma G2_median : Challenge.IsMedian Challenge.G2 := HKOTriameter.G2_median
lemma G1_diam : Challenge.G1.diam = 4 := HKOTriameter.G1_diam
lemma G2_diam : Challenge.G2.diam = 4 := HKOTriameter.G2_diam
lemma G1_triameter : Challenge.triameter Challenge.G1 = 8 := HKOTriameter.G1_triameter
lemma G2_triameter : Challenge.triameter Challenge.G2 = 12 := HKOTriameter.G2_triameter

lemma G1_diametral_iff (u v : Fin 8) :
    Challenge.IsDiametral Challenge.G1 u v ↔
      (u = 3 ∧ v = 7) ∨ (u = 7 ∧ v = 3) := by
  change HKOTriameter.G1.dist u v = HKOTriameter.G1.diam ↔ _
  rw [HKOTriameter.G1_dist, HKOTriameter.G1_diam]
  revert u v
  decide +kernel

lemma G1_peripheral_iff (u : Fin 8) :
    Challenge.IsPeripheral Challenge.G1 u ↔ u = 3 ∨ u = 7 := by
  rw [Readings.peripheral_iff_pair Challenge.G1 G1_connected u]
  constructor
  · rintro ⟨v, hv⟩
    rcases (G1_diametral_iff u v).mp hv with h | h
    · exact Or.inl h.1
    · exact Or.inr h.1
  · rintro (hu | hu)
    · exact ⟨7, (G1_diametral_iff u 7).mpr (Or.inl ⟨hu, rfl⟩)⟩
    · exact ⟨3, (G1_diametral_iff u 3).mpr (Or.inr ⟨hu, rfl⟩)⟩

lemma G1_triameter_twice_diam :
    Challenge.triameter Challenge.G1 = 2 * Challenge.G1.diam := by
  rw [G1_triameter, G1_diam]

lemma G1_question4 : Challenge.Question4 Challenge.G1 := by
  intro x y hxy
  exact ⟨0, Readings.triametral_of_two Challenge.G1 G1_connected
    G1_triameter_twice_diam hxy 0⟩

lemma G1_question4Strong : Challenge.Question4Strong Challenge.G1 :=
  (check_Sec2_readings_Q4 (Fin 8) Challenge.G1 G1_connected (by decide)).1.mp G1_question4

lemma G1_not_question3'Distinct : ¬ Challenge.Question3'Distinct Challenge.G1 := by
  intro h
  exact HKOTriameter.not_question3'_G1
    ((check_Sec2_readings_Q3 (Fin 8) Challenge.G1 G1_connected).2.mpr h)

/-- Every ordered triametral triple is a permutation of 1,4,7; repetitions are excluded. -/
lemma G2_triametral_iff (a b c : Fin 8) :
    Challenge.IsTriametral Challenge.G2 a b c ↔
      ({a, b, c} : Finset (Fin 8)) = {1, 4, 7} := by
  change HKOTriameter.IsTriametral HKOTriameter.G2 a b c ↔ _
  rw [HKOTriameter.IsTriametral, HKOTriameter.G2_triameter, HKOTriameter.G2_triDist]
  revert a b c
  decide +kernel

lemma G2_peripheral_5 : Challenge.IsPeripheral Challenge.G2 5 :=
  Readings.peripheral_of_diametral Challenge.G2 G2_connected HKOTriameter.G2_diametral_57

lemma G2_no_triple_through_5 :
    ∀ y z, ¬ Challenge.IsTriametral Challenge.G2 5 y z := by
  have hb : ∀ y z : Fin 8,
      HKOTriameter.D2 5 y + HKOTriameter.D2 5 z + HKOTriameter.D2 y z ≤ 10 := by
    decide +kernel
  intro y z h
  change HKOTriameter.IsTriametral HKOTriameter.G2 5 y z at h
  rw [HKOTriameter.IsTriametral, HKOTriameter.G2_triameter, HKOTriameter.G2_triDist] at h
  have hh := hb y z
  omega

lemma G2_question3 : Challenge.Question3 Challenge.G2 := by
  intro a b c ht
  have hab := MetricBounds.dist_le_diameter Challenge.G2 G2_connected a b
  have hac := MetricBounds.dist_le_diameter Challenge.G2 G2_connected a c
  have hbc := MetricBounds.dist_le_diameter Challenge.G2 G2_connected b c
  change Challenge.triDist Challenge.G2 a b c = Challenge.triameter Challenge.G2 at ht
  rw [G2_triameter] at ht
  rw [G2_diam] at hab hac hbc
  unfold Challenge.triDist at ht
  left
  change Challenge.G2.dist a b = Challenge.G2.diam
  rw [G2_diam]
  omega

lemma G2_not_question4Strong : ¬ Challenge.Question4Strong Challenge.G2 := by
  intro h
  exact HKOTriameter.not_question4_G2
    ((check_Sec2_readings_Q4 (Fin 8) Challenge.G2 G2_connected (by decide)).1.mpr h)

lemma G2_not_question4'Strong : ¬ Challenge.Question4'Strong Challenge.G2 := by
  intro h
  exact HKOTriameter.not_question4'_G2
    ((check_Sec2_readings_Q4 (Fin 8) Challenge.G2 G2_connected (by decide)).2.mpr h)

end ConcreteCore

theorem check_TheoremA_i : Challenge.TheoremA_i := by
  exact ⟨ConcreteCore.G1_median, ConcreteCore.G1_diam, ConcreteCore.G1_triameter,
    ConcreteCore.G1_peripheral_iff, HKOTriameter.G1_triametral_156,
    HKOTriameter.not_question3'_G1, HKOTriameter.not_question3'Pair_G1,
    ConcreteCore.G1_not_question3'Distinct,
    HKOTriameter.not_problem1Claim, HKOTriameter.not_problem1ClaimPair⟩

theorem check_TheoremA_ii : Challenge.TheoremA_ii := by
  refine ⟨ConcreteCore.G1_diametral_iff, ?_, ?_, ?_, HKOTriameter.not_question3_G1,
    ConcreteCore.G1_triameter_twice_diam, ConcreteCore.G1_question4,
    ConcreteCore.G1_question4Strong⟩
  · change HKOTriameter.G1.dist 1 5 = 3
    rw [HKOTriameter.G1_dist]
    decide
  · change HKOTriameter.G1.dist 1 6 = 2
    rw [HKOTriameter.G1_dist]
    decide
  · change HKOTriameter.G1.dist 5 6 = 3
    rw [HKOTriameter.G1_dist]
    decide

theorem check_TheoremB_ii : Challenge.TheoremB_ii := by
  refine ⟨?_, ?_, ?_, HKOTriameter.G2_diametral_57, HKOTriameter.G2_not_extendable_57,
    ConcreteCore.G2_peripheral_5, ConcreteCore.G2_no_triple_through_5,
    HKOTriameter.not_question4_G2, HKOTriameter.not_question4'_G2,
    ConcreteCore.G2_not_question4Strong, ConcreteCore.G2_not_question4'Strong,
    ConcreteCore.G2_question3, HKOTriameter.not_problem2Claim,
    HKOTriameter.not_problem2ClaimWeak⟩
  · change HKOTriameter.G2.dist 1 4 = 4
    rw [HKOTriameter.G2_dist]
    decide
  · change HKOTriameter.G2.dist 1 7 = 4
    rw [HKOTriameter.G2_dist]
    decide
  · change HKOTriameter.G2.dist 4 7 = 4
    rw [HKOTriameter.G2_dist]
    decide

#print axioms ConcreteCore.G2_triametral_iff
#print axioms check_TheoremA_i
#print axioms check_TheoremA_ii
#print axioms check_TheoremB_ii
end CodexPaper4
