import Mathlib

/-! Partial Fourier entropy–influence bounds on a finite uniform Boolean cube.
A point is its set of negative coordinates. The value true denotes the sign -1. -/
namespace Fei
open Finset

abbrev Cube (n : ℕ) := Finset (Fin n)

noncomputable def value {n : ℕ} (f : Cube n → Bool) (x : Cube n) : ℝ :=
  if f x then -1 else 1

noncomputable def character {n : ℕ} (s x : Cube n) : ℝ :=
  ∏ i ∈ x, if i ∈ s then (-1 : ℝ) else 1

noncomputable def coeff {n : ℕ} (f : Cube n → Bool) (s : Cube n) : ℝ :=
  (∑ x : Cube n, value f x * character s x) / 2 ^ n

noncomputable def support {n : ℕ} (f : Cube n → Bool) : Finset (Cube n) := by
  classical exact univ.filter fun s => coeff f s ≠ 0

noncomputable def mass {n : ℕ} (f : Cube n → Bool) (s : Cube n) := (coeff f s) ^ 2

noncomputable def entropy {n : ℕ} (f : Cube n → Bool) : ℝ :=
  ∑ s ∈ support f, mass f s * (-Real.logb 2 (mass f s))

noncomputable def influence {n : ℕ} (f : Cube n → Bool) : ℝ :=
  ∑ s ∈ support f, mass f s * s.card

noncomputable def weightSum {n : ℕ} (f : Cube n → Bool) : ℕ :=
  ∑ s ∈ support f, s.card

noncomputable def nonemptyCount {n : ℕ} (f : Cube n → Bool) : ℕ :=
  ((support f).erase ∅).card

def SignedProduct : Prop :=
  ∀ (n : ℕ) (f : Cube n → Bool), ∃ z : ℤ, z ≠ 0 ∧
    (2 : ℝ) ^ (2 * weightSum f) * (∏ s ∈ support f, coeff f s) =
      (2 : ℝ) ^ nonemptyCount f * (z : ℝ)

def SupportEntropy : Prop :=
  ∀ (n : ℕ) (f : Cube n → Bool),
    entropy f ≤ Real.logb 2 (support f).card ∧
    (support f).card * Real.logb 2 (support f).card ≤
      ∑ s ∈ support f, -Real.logb 2 (mass f s) ∧
    (∑ s ∈ support f, -Real.logb 2 (mass f s)) + 2 * nonemptyCount f ≤
      (4 : ℝ) * weightSum f

def LowerMassFEI : Prop :=
  ∀ (n : ℕ) (f : Cube n → Bool) (δ : ℝ), 0 < δ →
    (∀ s ∈ support f, δ ≤ (support f).card * mass f s) →
    δ * (entropy f + (2 : ℝ) * (nonemptyCount f : ℝ) / ((support f).card : ℝ)) ≤ 4 * influence f

def BoundedRatioFEI : Prop :=
  ∀ (n : ℕ) (f : Cube n → Bool) (M : ℝ), 1 ≤ M →
    (∀ s ∈ support f, ∀ t ∈ support f, |coeff f s| ≤ M * |coeff f t|) →
    entropy f ≤ 4 * M ^ 2 * influence f

end Fei
