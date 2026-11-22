import Research.TaskU.H5.Challenge
import Research.TaskU.H5.Cyc5

namespace TaskU.H5.ChallengeB

/-- Congruence modulo the ideal 5ℤ[ζ₅] in the integral power basis. -/
def congrFive (x y : Cyc5.V) : Prop :=
  x.a ≡ y.a [ZMOD 5] ∧ x.b ≡ y.b [ZMOD 5] ∧
  x.c ≡ y.c [ZMOD 5] ∧ x.d ≡ y.d [ZMOD 5]

/-- A residue comes from a global unit of the integer cyclotomic ring. -/
def unitImage (x : Cyc5.V) : Prop :=
  ∃ u v : Cyc5.V, Cyc5.mul u v = Cyc5.scalar 1 ∧ congrFive x u

/-- A split rational prime with a prime generator outside the global unit image. -/
def visible (q : ℕ) : Prop :=
  q.Prime ∧ q % 5 = 1 ∧ ∃ x : Cyc5.V, Cyc5.norm x = (q : ℤ) ∧ ¬ unitImage x

/-- The full spectrum on signed integer coefficients of the original regular matrix. -/
def fullSpectrum : Prop :=
  ∀ m : ℤ, (∃ f : H → ℤ, groupDet f = m) ↔
    (m ^ 4 ≡ 1 [ZMOD 125]) ∨ (5 ^ 33 : ℤ) ∣ m ∨
      ∃ n : ℤ, n ≠ 0 ∧ m = 5 ^ 28 * n ∧ ∃ q : ℕ, visible q ∧ (q : ℤ) ∣ n

end TaskU.H5.ChallengeB
