import Research.Backfill.Paper7.CandidateRootRows
import Research.Backfill.Paper7.ResidualCertificatePatterns

/-! Both literal rows force parameter sum0. These proofs do not use the
generator's parameter search or assume that its table is exhaustive. -/
set_option autoImplicit false
noncomputable section
namespace Paper7CycleThreeCertificate
open Polynomial Paper7CycleThree

theorem oneQ_reject_candidate_row (p : Fin 3 → ℕ) (q : ℕ)
    (hpos : 0 < p 0 + p 1 + p 2 + q) (a : List ℤ) (ha : a ∈ candidateRows) :
    triangleResidualOneQ p q ≠ (a.map (fun z => X-C z)).prod := by
  intro hpoly
  obtain ⟨_h7, h6, _h5, _h4, h3, _h1, _h0⟩ := oneQ_coefficient_data p q
  have hc3 := (rootCoefficient_eq a 3).trans
    (congrArg (fun H : Polynomial ℤ => H.coeff 3) hpoly).symm
  have hc6 := (rootCoefficient_eq a 6).trans
    (congrArg (fun H : Polynomial ℤ => H.coeff 6) hpoly).symm
  rw [h3] at hc3
  rw [h6] at hc6
  have hp : (0 : ℤ) < p 0 + p 1 + p 2 + q := by exact_mod_cast hpos
  rcases candidateRows_key_coefficients a ha with h | h <;> omega
#print axioms Paper7CycleThreeCertificate.oneQ_reject_candidate_row

theorem offZero_reject_candidate_row (b c u v : ℕ)
    (hpos : 0 < b + c + u + v) (a : List ℤ) (ha : a ∈ candidateRows) :
    triangleResidualOffZero b c u v ≠ (a.map (fun z => X-C z)).prod := by
  intro hpoly
  obtain ⟨_h7, h6, _h5, h3, _h1, _h0⟩ := offZero_coefficient_data b c u v
  have hc3 := (rootCoefficient_eq a 3).trans
    (congrArg (fun H : Polynomial ℤ => H.coeff 3) hpoly).symm
  have hc6 := (rootCoefficient_eq a 6).trans
    (congrArg (fun H : Polynomial ℤ => H.coeff 6) hpoly).symm
  rw [h3] at hc3
  rw [h6] at hc6
  have hp : (0 : ℤ) < b + c + u + v := by exact_mod_cast hpos
  rcases candidateRows_key_coefficients a ha with h | h <;> omega
#print axioms Paper7CycleThreeCertificate.offZero_reject_candidate_row

theorem atZero_reject_candidate_row (a b u v : ℕ)
    (hpos : 0 < a + b + u + v) (w : List ℤ) (hw : w ∈ candidateRows) :
    triangleResidualAtZero a b u v ≠ (w.map (fun z => X-C z)).prod := by
  intro hpoly
  obtain ⟨_h7, h6, _h5, _h4, h3, _h1, _h0⟩ := atZero_coefficient_data a b u v
  have hc3 := (rootCoefficient_eq w 3).trans
    (congrArg (fun H : Polynomial ℤ => H.coeff 3) hpoly).symm
  have hc6 := (rootCoefficient_eq w 6).trans
    (congrArg (fun H : Polynomial ℤ => H.coeff 6) hpoly).symm
  rw [h3] at hc3
  rw [h6] at hc6
  have hp : (0 : ℤ) < a + b + u + v := by exact_mod_cast hpos
  rcases candidateRows_key_coefficients w hw with h | h <;> omega
#print axioms Paper7CycleThreeCertificate.atZero_reject_candidate_row

end Paper7CycleThreeCertificate
