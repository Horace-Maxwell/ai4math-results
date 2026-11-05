import Research.Backfill.Paper7.MomentB4CycleTypeCounts

/-! Source-only repair of the complete constant-pair subcase. The finite
certificate retains all p in Fin 10 and q in Fin 5, including their zero
boundaries and the original catalogue guards. Only the four-term sums are
expanded before kernel decision; no catalogue is expanded in fifty tactic
branches. This source has not been compiled or accepted. -/
set_option autoImplicit false
noncomputable section
namespace Paper7MomentCanonicalNumeric
open BackfillPaper7.Challenge.Legacy Paper7MomentCounts Paper7MomentCertificate
open scoped BigOperators Classical

theorem b4_constant_catalog_certificate :
    ∀ p : Fin 10, ∀ q : Fin 5,
      ¬ B4CatalogRowAccept (fun _ : Fin 4 => p.val + q.val) (4 * q.val) := by
  simp only [B4CatalogRowAccept, b4Theta, Fin.sum_univ_four]
  decide +kernel
#print axioms Paper7MomentCanonicalNumeric.b4_constant_catalog_certificate

theorem b4_constant_candidate_impossible (p q : ℕ) :
    ((fun _ : Fin 4 => p), (fun _ : Fin 4 => q)) ∉ CandB1 4 41 := by
  intro hx
  have hw := hx.1.2
  change 4 + ((∑ _ : Fin 4, p) + 2 * (∑ _ : Fin 4, q)) ≤ 41 at hw
  rw [Fin.sum_univ_four, Fin.sum_univ_four] at hw
  have hp : p ≤ 9 := by omega
  have hq : q ≤ 4 := by omega
  have hsum : qSum ((fun _ : Fin 4 => p), (fun _ : Fin 4 => q)) = 4 * q := by
    change (∑ _ : Fin 4, q) = 4 * q
    rw [Fin.sum_univ_four]
    omega
  have he := b4_encode_accept ((fun _ : Fin 4 => p), (fun _ : Fin 4 => q)) hx
  rw [hsum] at he
  have hg : B4GuardedRowAccept (fun _ : Fin 4 => p + q) (4 * q) := by
    refine ⟨?_, he⟩
    rw [Fin.sum_univ_four]
    omega
  have hc := (b4_guarded_catalog_iff (fun _ : Fin 4 => p + q) (4 * q)).mp hg
  exact b4_constant_catalog_certificate
    ⟨p, Nat.lt_succ_of_le hp⟩ ⟨q, Nat.lt_succ_of_le hq⟩ hc
#print axioms Paper7MomentCanonicalNumeric.b4_constant_candidate_impossible

theorem b4_type4_empty : IsEmpty B4Type4 := by
  refine ⟨fun a => ?_⟩
  exact b4_constant_candidate_impossible a.val.1.val a.val.2.val a.property
#print axioms Paper7MomentCanonicalNumeric.b4_type4_empty

theorem b4_type4_card : Fintype.card B4Type4 = 0 := by
  let : IsEmpty B4Type4 := b4_type4_empty
  exact Fintype.card_of_isEmpty
#print axioms Paper7MomentCanonicalNumeric.b4_type4_card

theorem b4_quarter_turn_fixed_count : b4FixedCount (b4Rotation 1) = 0 ∧
    b4FixedCount (b4Rotation 3) = 0 := by
  have h : b4FixedCount (b4Rotation 1) = 0 := by
    rw [b4_fixed_count_eq_word_count, Fintype.card_congr b4Type4Equiv, b4_type4_card]
  exact ⟨h, b4_rotation_three_count.trans h⟩
#print axioms Paper7MomentCanonicalNumeric.b4_quarter_turn_fixed_count

theorem b4_canonical_clauses_iff_two_types :
    ((canonB1 4 41).Finite ∧ (canonB1 4 41).ncard = 52641) ∧
      ((canonD2 4 41).Finite ∧ (canonD2 4 41).ncard = 52641) ↔
        3 * Fintype.card B4Type22 + 2 * Fintype.card B4Type112 = 10584 := by
  rw [b4_canonical_clauses_iff_cycle_types, b4_type4_card]
  simp only [mul_zero, zero_add]
#print axioms Paper7MomentCanonicalNumeric.b4_canonical_clauses_iff_two_types

end Paper7MomentCanonicalNumeric
