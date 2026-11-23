import Research.TaskV.FEI.Challenge

namespace Fei
open Finset

def UpperProduct : Prop :=
  ∀ (n : ℕ) (f : Cube n → Bool) (V : Finset (Cube n)),
    V ⊆ support f →
    (∀ s ∈ V, ∀ w ∈ support f, s ⊆ w → w ∈ V) →
    ∃ z : ℤ, z ≠ 0 ∧
      (2 : ℝ) ^ (2 * ∑ s ∈ V, s.card) * (∏ s ∈ V, coeff f s) =
        (2 : ℝ) ^ (V.erase ∅).card * (z : ℝ)

def ComparableMassFEI : Prop :=
  ∀ (n : ℕ) (f : Cube n → Bool) (L : ℝ), 1 ≤ L →
    (∀ s ∈ (support f).erase ∅, ∀ t ∈ (support f).erase ∅, s ⊆ t →
      mass f s ≤ L * mass f t) →
    entropy f ≤ 4 * L * influence f

end Fei
