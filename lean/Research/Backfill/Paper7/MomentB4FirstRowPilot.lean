import Research.Backfill.Paper7.MomentQTableCertificate
import Research.Backfill.Paper7.MomentB4FeatureCatalog
import Research.Backfill.Paper7.ZQBudgetCoordinates

/-! Tiny source-only pilot for actual saved candidate index 7. Its finite table
and acceptance predicate are checked below, not taken from JSON as hypotheses.
It asserts one row contribution only, not the full candidate-set cardinality.
No Lean or native evaluation was run while authoring this source. -/
set_option autoImplicit false
noncomputable section
namespace Paper7MomentCertificate
open Paper7MomentDP Paper7MomentCounts
open BackfillPaper7.Challenge BackfillPaper7.Challenge.Legacy
open scoped BigOperators

def pilotZ7 : Fin 4 → ℕ := ![0, 0, 0, 7]
#print axioms Paper7MomentCertificate.pilotZ7

/-- Exact compact description of all 5 by 19 entries in saved row 7. -/
def pilotL7 (k : Fin 5) (t : Fin 19) : ℕ :=
  if k.val = 4 then (if t.val ≤ 7 then 1 else 0)
  else (if t.val = 0 then 1 else 0)
#print axioms Paper7MomentCertificate.pilotL7

/-- This small decision checks the initial row and every successor cell;
it never evaluates the unmemoized boundedQDP recurrence. -/
theorem pilotL7_valid : QTableValid pilotZ7 pilotL7 := by
  unfold QTableValid
  decide
#print axioms Paper7MomentCertificate.pilotL7_valid

theorem pilot7_boundedQDP : boundedQDP 4 pilotZ7 7 = 1 := by
  have h : 1 = boundedQDP 4 pilotZ7 7 :=
    qTable_last_eq pilotZ7 pilotL7 pilotL7_valid ⟨7, by decide⟩
  exact h.symm
#print axioms Paper7MomentCertificate.pilot7_boundedQDP

/-- The catalogue replaces an existential feature predicate, not its witness count. -/
theorem b4_evenFeature_catalog_iff (W Q : ℕ) (T : ℤ) :
    (∃ a : Counts, evenFeatureCondition 4 41 W Q T a) ↔
      ∃ sm ∈ b4FeatureCatalog, sm.2 = T + 4 ∧
        sm.1 ≤ (4 + W : ℤ) ∧ (4 + W : ℤ) - max (Q : ℤ) 2 ≤ sm.1 := by
  have hfour : (4 : ℕ) = 4 := rfl
  constructor
  · rintro ⟨a, htop, hbound, hm, hu, hl⟩
    refine ⟨(s2 4 (a, 0), m4 4 (a, 0)),
      b4Feature_mem_catalog a ⟨htop, hbound⟩, ?_, hu, hl⟩
    simpa only [ite_eq_left hfour, ite_true] using hm
  · rintro ⟨⟨S, M⟩, hmem, hm, hu, hl⟩
    obtain ⟨a, hcore, hs, hmoment⟩ := (b4FeatureCatalog_iff S M).mp hmem
    refine ⟨a, hcore.1, hcore.2, ?_, ?_, ?_⟩
    · rw [hmoment]
      simpa only [ite_eq_left hfour, ite_true] using hm
    · rw [hs]
      exact hu
    · rw [hs]
      exact hl
#print axioms Paper7MomentCertificate.b4_evenFeature_catalog_iff

/-- Native row 7 has Z=7 and theta=78+2Q. All original guards remain explicit. -/
def pilot7Accept (Q : Fin 19) : Prop :=
  Q.val ≤ 7 ∧ 0 < 7 + Q.val ∧ 4 + (7 + Q.val) ≤ 41 ∧
    ∃ a : Counts, evenFeatureCondition 4 41 (7 + Q.val) Q.val
      (78 + 2 * (Q.val : ℤ)) a
#print axioms Paper7MomentCertificate.pilot7Accept

/-- All nineteen possible Q values, including the rejected ones, are checked. -/
theorem pilot7_accept_iff (Q : Fin 19) : pilot7Accept Q ↔ Q = 7 := by
  unfold pilot7Accept
  rw [b4_evenFeature_catalog_iff]
  fin_cases Q <;> norm_num [b4FeatureCatalog]
#print axioms Paper7MomentCertificate.pilot7_accept_iff

open scoped Classical

/-- Sum once per Q, never once per feature witness. This is a single-row pilot. -/
theorem pilot7_contribution :
    (∑ Q : Fin 19, if pilot7Accept Q then boundedQDP 4 pilotZ7 Q.val else 0) = 1 := by
  classical
  calc
    (∑ Q : Fin 19, if pilot7Accept Q then boundedQDP 4 pilotZ7 Q.val else 0) =
        if pilot7Accept (7 : Fin 19) then boundedQDP 4 pilotZ7 (7 : Fin 19).val else 0 := by
      apply Finset.sum_eq_single (7 : Fin 19)
      · intro Q _ hQ
        exact ite_eq_right (fun h => hQ ((pilot7_accept_iff Q).mp h))
      · intro h
        exact False.elim (h (Finset.mem_univ _))
    _ = 1 := by
      rw [ite_eq_left ((pilot7_accept_iff (7 : Fin 19)).mpr rfl)]
      exact pilot7_boundedQDP
#print axioms Paper7MomentCertificate.pilot7_contribution

end Paper7MomentCertificate
