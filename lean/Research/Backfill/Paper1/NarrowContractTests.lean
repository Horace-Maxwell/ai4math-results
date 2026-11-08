import Research.Backfill.Paper1.SupplementStatements

/-!
Candidate regressions, not yet run. The h-parameter examples check interfaces
and quantifier ranges only; they are not proofs of Theorem5MinTwo or MaxEnergy.
All 84 original examples and triple_eq_matrix remain in ChallengeTests.lean.
-/
set_option autoImplicit false
noncomputable section
namespace BackfillPaper1.NarrowContractTests
open Challenge NarrowSupplement

example : min 3 3 > 2 ∧ min 1 1000001 ≤ 2 ∧ min 1000000 2 ≤ 2 := by decide

example (h : Theorem5MinTwo) (b : ℕ) (hb : 1 ≤ b) (hpar : Even (1 + b)) :
    EqualParityClaim 1 b :=
  h 1 b (by omega) hb hpar (le_trans (Nat.min_le_left _ _) (by norm_num))

example (h : Theorem5MinTwo) (a : ℕ) (ha : 1 ≤ a) (hpar : Even (a + 1)) :
    EqualParityClaim a 1 :=
  h a 1 ha (by omega) hpar (le_trans (Nat.min_le_right _ _) (by norm_num))

example (h : Theorem5MinTwo) (b : ℕ) (hb : 1 ≤ b) (hpar : Even (2 + b)) :
    EqualParityClaim 2 b :=
  h 2 b (by omega) hb hpar (le_trans (Nat.min_le_left _ _) (by norm_num))

example (h : Theorem5MinTwo) (a : ℕ) (ha : 1 ≤ a) (hpar : Even (a + 2)) :
    EqualParityClaim a 2 :=
  h a 2 ha (by omega) hpar (le_trans (Nat.min_le_right _ _) (by norm_num))

example (h : Theorem5MinTwo) : EqualParityClaim 1 1000001 :=
  h 1 1000001 (by decide) (by decide) (by decide) (by decide)

example (h : Theorem5MinTwo) : EqualParityClaim 1000000 2 :=
  h 1000000 2 (by decide) (by decide) (by decide) (by decide)

example (h : EqualParityClaim 2 2) (p q : ℕ) (hpq : DistinctOddPrimes p q) :
    MaxEnergy (p ^ 2 * q ^ 2)
      ((((p ^ 2 * q ^ 2 : ℕ) : ℝ) + dClosed 2 p * dClosed 2 q) / 2 -
        deltaK 2 p * deltaK 2 q)
      {oddSet p q 2 2, (evenSet p q 2 2).erase (p ^ 2 * q ^ 2)} :=
  h p q hpq

example (n : ℕ) (V : ℝ) (S : Set (Finset ℕ)) (D : Finset ℕ)
    (h : MaxEnergy n V S) (hD : IsConnSet n D) :
    energy n D = V ↔ D ∈ S := (h.2 D hD).2

example (n : ℕ) (V : ℝ) (S : Set (Finset ℕ)) (D : Finset ℕ)
    (h : MaxEnergy n V S) (hD : D ∈ S) : IsConnSet n D := h.1 D hD

/-- Required positive spectral-energy calibration (old review T4).
Its theorem proof and executable positive example must be supplied before acceptance;
an h-parameter interface test does not discharge it. -/
def PositiveEnergyCalibration : Prop := energy 3 {1} = 4

end BackfillPaper1.NarrowContractTests
