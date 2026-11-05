import Mathlib

/-! UNCOMPILED arithmetic candidates by /root/moment_b6_labelled_symbolic_2310.
Scalar discriminant/reconstruction for sorted capacity triples. No candidate
enumeration, numerical table, complete count, or new coverage assumption. -/
set_option autoImplicit false
noncomputable section
namespace Paper7MomentCounts
open scoped BigOperators Classical

def labelledTripleDiscriminant (A B c : ℕ) : ℤ :=
  2 * (B : ℤ) - 2 * (c : ℤ)^2 - ((A : ℤ) - c)^2
#print axioms Paper7MomentCounts.labelledTripleDiscriminant

def labelledTripleRoot (A B c : ℕ) : ℕ :=
  Nat.sqrt (labelledTripleDiscriminant A B c).toNat
#print axioms Paper7MomentCounts.labelledTripleRoot

def labelledTripleHigh (A B c : ℕ) : ℕ :=
  (A - c + labelledTripleRoot A B c) / 2
#print axioms Paper7MomentCounts.labelledTripleHigh

def labelledTripleLow (A B c : ℕ) : ℕ :=
  (A - c - labelledTripleRoot A B c) / 2
#print axioms Paper7MomentCounts.labelledTripleLow

def B6SortedTripleDiscriminantAccept (A B c : ℕ) : Prop :=
  c ≤ A ∧ labelledTripleRoot A B c ≤ A - c ∧
    A + labelledTripleRoot A B c ≤ 3 * c ∧
    (A - c) % 2 = labelledTripleRoot A B c % 2 ∧
    labelledTripleRoot A B c ^ 2 + (A - c)^2 + 2*c^2 = 2*B
#print axioms Paper7MomentCounts.B6SortedTripleDiscriminantAccept

theorem labelled_pair_halves_double (s d : ℕ) (hd : d ≤ s)
    (hpar : s % 2 = d % 2) :
    2 * ((s + d) / 2) = s + d ∧ 2 * ((s - d) / 2) = s - d := by
  omega
#print axioms Paper7MomentCounts.labelled_pair_halves_double

theorem labelled_pair_squares_from_halves (s d a b : ℕ) (hd : d ≤ s)
    (ha : 2*a = s+d) (hb : 2*b = s-d) :
    2*(a^2+b^2) = s^2+d^2 := by
  have hs : a+b = s := by omega
  have hdiff : b+d = a := by omega
  calc
    2*(a^2+b^2) = 2*((b+d)^2+b^2) := by rw [hdiff]
    _ = ((b+d)+b)^2+d^2 := by ring
    _ = s^2+d^2 := by rw [hdiff, hs]
#print axioms Paper7MomentCounts.labelled_pair_squares_from_halves

theorem labelled_sorted_triple_decode_sound (A B c : ℕ)
    (h : B6SortedTripleDiscriminantAccept A B c) :
    labelledTripleLow A B c ≤ labelledTripleHigh A B c ∧
    labelledTripleHigh A B c ≤ c ∧
    c + labelledTripleHigh A B c + labelledTripleLow A B c = A ∧
    c^2 + labelledTripleHigh A B c ^ 2 + labelledTripleLow A B c ^ 2 = B := by
  let d := labelledTripleRoot A B c
  let a := labelledTripleHigh A B c
  let b := labelledTripleLow A B c
  change c ≤ A ∧ d ≤ A-c ∧ A+d ≤ 3*c ∧
    (A-c)%2 = d%2 ∧ d^2+(A-c)^2+2*c^2 = 2*B at h
  obtain ⟨hc, hd, hmax, hpar, hsq⟩ := h
  have hh := labelled_pair_halves_double (A-c) d hd hpar
  have ha : 2*a = A-c+d := hh.1
  have hb : 2*b = A-c-d := hh.2
  have hp := labelled_pair_squares_from_halves (A-c) d a b hd ha hb
  change b ≤ a ∧ a ≤ c ∧ c+a+b = A ∧ c^2+a^2+b^2 = B
  exact ⟨by omega, by omega, by omega, by nlinarith⟩
#print axioms Paper7MomentCounts.labelled_sorted_triple_decode_sound

theorem labelled_sorted_triple_root_recovers (a b c : ℕ) (hba : b ≤ a) :
    labelledTripleRoot (a+b+c) (a^2+b^2+c^2) c = a-b := by
  have hs : (a : ℤ) = ((a-b : ℕ) : ℤ) + (b : ℤ) := by
    exact_mod_cast (Nat.sub_add_cancel hba).symm
  have hD : labelledTripleDiscriminant (a+b+c) (a^2+b^2+c^2) c =
      (((a-b)^2 : ℕ) : ℤ) := by
    unfold labelledTripleDiscriminant
    push_cast
    simp only [hs]
    ring
  unfold labelledTripleRoot
  rw [hD, Int.toNat_natCast]
  exact Nat.sqrt_eq' (a-b)
#print axioms Paper7MomentCounts.labelled_sorted_triple_root_recovers

theorem labelledTripleDiscriminant_window_identity (A B c : ℕ) :
    3 * labelledTripleDiscriminant A B c =
      2 * (3*(B : ℤ) - (A : ℤ)^2) - (3*(c : ℤ) - A)^2 := by
  unfold labelledTripleDiscriminant
  ring
#print axioms Paper7MomentCounts.labelledTripleDiscriminant_window_identity

theorem labelled_sorted_triple_scalar_width_le_twenty_five (A : ℕ) (hA : A ≤ 36) :
    A + 1 - (A + 2) / 3 ≤ 25 := by
  omega
#print axioms Paper7MomentCounts.labelled_sorted_triple_scalar_width_le_twenty_five

end Paper7MomentCounts
