import Research.Backfill.Paper7.MomentB6FeatureGuard

/-! Pending exact zero count for the original full constant-row fibre.
This is the numeric six-cycle contribution required by the b6 dihedral
count, before transport to the actual rotations. No full labelled or
canonical numerical target is assumed. -/
set_option autoImplicit false
noncomputable section
namespace Paper7MomentCounts
open BackfillPaper7.Challenge BackfillPaper7.Challenge.Legacy
open scoped BigOperators

theorem b6_constant_row_features (p q : ℕ) :
    weight ((fun _ : Fin 6 => p), (fun _ : Fin 6 => q)) = 6 * p + 12 * q ∧
    qSum ((fun _ : Fin 6 => p), (fun _ : Fin 6 => q)) = 6 * q ∧
    theta ((fun _ : Fin 6 => p), (fun _ : Fin 6 => q)) =
      6 * (((p : ℤ) + q + 1) * ((p : ℤ) + q + 2) + 2 * q) := by
  constructor
  · simp [weight, pSum, qSum]
    ring
  constructor
  · simp [qSum]
  · simp [theta, thetaV]
    ring
#print axioms Paper7MomentCounts.b6_constant_row_features

theorem b6_constant_guard_small_certificate :
    ∀ p : Fin 7, ∀ q : Fin 4,
      ¬ (0 < 6 * p.val + 12 * q.val ∧ 6 * p.val + 12 * q.val ≤ 36 ∧
        b6FeatureGuard (6 * p.val + 12 * q.val) (6 * q.val)
          (6 * (((p.val : ℤ) + q.val + 1) * ((p.val : ℤ) + q.val + 2) +
            2 * q.val))) := by
  let accepted (p q : ℕ) : Bool :=
    let W := 6 * p + 12 * q
    let Q := 6 * q
    let T := 6 * (((p : ℤ) + q + 1) * ((p : ℤ) + q + 2) + 2 * q)
    decide (0 < W ∧ W ≤ 36) &&
      decide (∃ sm ∈ b6FeatureCatalog, sm.2 = T ∧
        sm.1 ≤ (6 + W : ℤ) ∧ (6 + W : ℤ) - max (Q : ℤ) 2 ≤ sm.1)
  have reflect (p q : ℕ) : accepted p q = true ↔
      (0 < 6 * p + 12 * q ∧ 6 * p + 12 * q ≤ 36 ∧
        b6FeatureGuard (6 * p + 12 * q) (6 * q)
          (6 * (((p : ℤ) + q + 1) * ((p : ℤ) + q + 2) + 2 * q))) := by
    simp only [accepted, Bool.and_eq_true, decide_eq_true_eq, b6FeatureGuard, and_assoc]
  have certificate : ∀ p : Fin 7, ∀ q : Fin 4,
      accepted p.val q.val = false := by
    decide +kernel
  intro p q h
  have htrue := (reflect p.val q.val).mpr h
  rw [certificate p q] at htrue
  contradiction
#print axioms Paper7MomentCounts.b6_constant_guard_small_certificate

theorem b6_constant_guard_impossible (p q : ℕ) :
    ¬ b6CandidateGuard ((fun _ : Fin 6 => p), (fun _ : Fin 6 => q)) := by
  intro hg
  have hf := b6_constant_row_features p q
  unfold b6CandidateGuard at hg
  rw [hf.1, hf.2.1, hf.2.2] at hg
  have hp : p < 7 := by omega
  have hq : q < 4 := by omega
  exact b6_constant_guard_small_certificate ⟨p,hp⟩ ⟨q,hq⟩ hg
#print axioms Paper7MomentCounts.b6_constant_guard_impossible

theorem b6_constant_candB1_impossible (p q : ℕ) :
    ((fun _ : Fin 6 => p), (fun _ : Fin 6 => q)) ∉ CandB1 6 42 := by
  rw [b6_candB1_iff_guard]
  exact b6_constant_guard_impossible p q
#print axioms Paper7MomentCounts.b6_constant_candB1_impossible

theorem b6_constant_candD2_impossible (p q : ℕ) :
    ((fun _ : Fin 6 => p), (fun _ : Fin 6 => q)) ∉ CandD2 6 42 := by
  rw [b6_candD2_iff_guard]
  exact b6_constant_guard_impossible p q
#print axioms Paper7MomentCounts.b6_constant_candD2_impossible

theorem b6_constant_candB1_fibre_empty :
    {x : PQ 6 | x ∈ CandB1 6 42 ∧
      ∃ p q : ℕ, x = ((fun _ : Fin 6 => p), (fun _ : Fin 6 => q))} = ∅ := by
  ext x
  constructor
  · rintro ⟨hx, p, q, rfl⟩
    exact b6_constant_candB1_impossible p q hx
  · simp
#print axioms Paper7MomentCounts.b6_constant_candB1_fibre_empty

theorem b6_constant_candD2_fibre_empty :
    {x : PQ 6 | x ∈ CandD2 6 42 ∧
      ∃ p q : ℕ, x = ((fun _ : Fin 6 => p), (fun _ : Fin 6 => q))} = ∅ := by
  ext x
  constructor
  · rintro ⟨hx, p, q, rfl⟩
    exact b6_constant_candD2_impossible p q hx
  · simp
#print axioms Paper7MomentCounts.b6_constant_candD2_fibre_empty

theorem b6_constant_candB1_ncard :
    {x : PQ 6 | x ∈ CandB1 6 42 ∧
      ∃ p q : ℕ, x = ((fun _ : Fin 6 => p), (fun _ : Fin 6 => q))}.ncard = 0 := by
  rw [b6_constant_candB1_fibre_empty]
  simp
#print axioms Paper7MomentCounts.b6_constant_candB1_ncard

theorem b6_constant_candD2_ncard :
    {x : PQ 6 | x ∈ CandD2 6 42 ∧
      ∃ p q : ℕ, x = ((fun _ : Fin 6 => p), (fun _ : Fin 6 => q))}.ncard = 0 := by
  rw [b6_constant_candD2_fibre_empty]
  simp
#print axioms Paper7MomentCounts.b6_constant_candD2_ncard

end Paper7MomentCounts
