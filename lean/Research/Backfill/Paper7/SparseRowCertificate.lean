import Research.Backfill.Paper7.MomentB4RowCertificateBridge

/-! A finite proof-checking relation for sparse row certificates. All nineteen
Q decisions must agree with the original acceptance predicate. Only accepted
Q values carry a full, genuine prefix-DP table. Data files and their flags are
not proof premises; this module does not run a Boolean or native checker. -/
set_option autoImplicit false
noncomputable section
namespace Paper7MomentCertificate
open Paper7MomentCounts Paper7MomentDP
open scoped BigOperators Classical

abbrev SparseRowTables (S : Finset (Fin 19)) :=
  {Q : Fin 19 // Q ∈ S} → Fin 5 → Fin 19 → ℕ
#print axioms Paper7MomentCertificate.SparseRowTables

/-- The first conjunct includes every rejected Q as well as every accepted Q.
The second demands all initial and successor table cells for each accepted Q. -/
def SparseRowValid (z : Fin 4 → ℕ) (S : Finset (Fin 19)) (L : SparseRowTables S) : Prop :=
  (∀ Q : Fin 19, B4CatalogRowAccept z Q.val ↔ Q ∈ S) ∧
    ∀ Q : {Q : Fin 19 // Q ∈ S}, QTableValid z (L Q)
#print axioms Paper7MomentCertificate.SparseRowValid

/-- Iterate over Fin19, so a Q contributes at most once. No feature witness
is counted and no table is demanded for a rejected Q. -/
def sparseRowValue (S : Finset (Fin 19)) (L : SparseRowTables S) : ℕ :=
  ∑ Q : Fin 19, if hQ : Q ∈ S then L ⟨Q, hQ⟩ (Fin.last 4) Q else 0
#print axioms Paper7MomentCertificate.sparseRowValue

theorem sparseRow_rejected_original_term (z : Fin 4 → ℕ) (S : Finset (Fin 19))
    (L : SparseRowTables S) (h : SparseRowValid z S L) (Q : Fin 19) (hQ : Q ∉ S) :
    (if B4RowAccept z Q.val then boundedQDP 4 z Q.val else 0) = 0 := by
  rw [b4_insert_total_guard, b4_guarded_catalog_iff]
  exact ite_eq_right (fun ha => hQ ((h.1 Q).mp ha))
#print axioms Paper7MomentCertificate.sparseRow_rejected_original_term

theorem sparseRow_accepted_original_term (z : Fin 4 → ℕ) (S : Finset (Fin 19))
    (L : SparseRowTables S) (h : SparseRowValid z S L) (Q : Fin 19) (hQ : Q ∈ S) :
    (if B4RowAccept z Q.val then boundedQDP 4 z Q.val else 0) =
      L ⟨Q, hQ⟩ (Fin.last 4) Q := by
  rw [b4_insert_total_guard, b4_guarded_catalog_iff, ite_eq_left ((h.1 Q).mpr hQ)]
  exact (qTable_last_eq z (L ⟨Q, hQ⟩) (h.2 ⟨Q, hQ⟩) Q).symm
#print axioms Paper7MomentCertificate.sparseRow_accepted_original_term

theorem sparseRow_sound (z : Fin 4 → ℕ) (S : Finset (Fin 19))
    (L : SparseRowTables S) (h : SparseRowValid z S L) :
    b4RowContribution z = sparseRowValue S L := by
  unfold b4RowContribution sparseRowValue
  apply Finset.sum_congr rfl
  intro Q _
  by_cases hQ : Q ∈ S
  · rw [dite_eq_left hQ, ite_eq_left ((h.1 Q).mpr hQ)]
    exact (qTable_last_eq z (L ⟨Q, hQ⟩) (h.2 ⟨Q, hQ⟩) Q).symm
  · rw [dite_eq_right hQ, ite_eq_right (fun ha => hQ ((h.1 Q).mp ha))]
#print axioms Paper7MomentCertificate.sparseRow_sound

theorem rowContribution_zero_of_rejected (z : Fin 4 → ℕ)
    (h : ∀ Q : Fin 19, ¬ B4CatalogRowAccept z Q.val) : b4RowContribution z = 0 := by
  unfold b4RowContribution
  apply Finset.sum_eq_zero
  intro Q _
  exact ite_eq_right (h Q)
#print axioms Paper7MomentCertificate.rowContribution_zero_of_rejected

def sparseRow7Tables : SparseRowTables ({7} : Finset (Fin 19)) := fun _ => pilotL7
#print axioms Paper7MomentCertificate.sparseRow7Tables

/-- A small certificate for the actual saved row7: singleton accepted-Q data,
all nineteen decisions proved, and the actual full table validated. -/
theorem sparseRow7_valid :
    SparseRowValid pilotZ7 ({7} : Finset (Fin 19)) sparseRow7Tables := by
  constructor
  · intro Q
    rw [← b4_guarded_catalog_iff pilotZ7 Q.val, b4_pilot_guarded_iff Q, pilot7_accept_iff Q,
      Finset.mem_singleton]
  · intro _Q
    exact pilotL7_valid
#print axioms Paper7MomentCertificate.sparseRow7_valid

theorem sparseRow7_value : sparseRowValue ({7} : Finset (Fin 19)) sparseRow7Tables = 1 := by
  calc
    sparseRowValue ({7} : Finset (Fin 19)) sparseRow7Tables = b4RowContribution pilotZ7 :=
      (sparseRow_sound pilotZ7 {7} sparseRow7Tables sparseRow7_valid).symm
    _ = 1 := b4RowContribution_pilot7
#print axioms Paper7MomentCertificate.sparseRow7_value

end Paper7MomentCertificate
