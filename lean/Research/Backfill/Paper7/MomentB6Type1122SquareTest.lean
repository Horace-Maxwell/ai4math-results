import Mathlib

/-!
An analytical square discriminator for the second difference coordinate in the
1122 reflection branch. This source is pending compilation. It performs no
numerical classification and gives no value for the original counting targets.
-/

namespace Paper7MomentCounts

open scoped BigOperators

/-- The only possible nonnegative second difference. -/
def b6Type1122SquareE (D : ℕ) (R : ℤ) : ℕ :=
  Nat.sqrt ((R - (D : ℤ) ^ 2).toNat / 2)

#print axioms Paper7MomentCounts.b6Type1122SquareE

/-- Nonnegative, even remainder; exact square; bound; and parity. -/
def b6Type1122SquareTest (D B : ℕ) (R : ℤ) : Prop :=
  0 ≤ R - (D : ℤ) ^ 2 ∧
    (R - (D : ℤ) ^ 2).toNat % 2 = 0 ∧
    b6Type1122SquareE D R ^ 2 = (R - (D : ℤ) ^ 2).toNat / 2 ∧
    b6Type1122SquareE D R ≤ B ∧
    b6Type1122SquareE D R % 2 = B % 2

#print axioms Paper7MomentCounts.b6Type1122SquareTest

instance b6Type1122SquareTestDecidable (D B : ℕ) (R : ℤ) :
    Decidable (b6Type1122SquareTest D B R) := by
  unfold b6Type1122SquareTest
  infer_instance

#print axioms Paper7MomentCounts.b6Type1122SquareTestDecidable

theorem b6_type1122_square_remainder (D E : ℕ) (R : ℤ)
    (h : (D : ℤ) ^ 2 + 2 * (E : ℤ) ^ 2 = R) :
    0 ≤ R - (D : ℤ) ^ 2 ∧
      (R - (D : ℤ) ^ 2).toNat % 2 = 0 ∧
      (R - (D : ℤ) ^ 2).toNat / 2 = E ^ 2 := by
  have hrem : R - (D : ℤ) ^ 2 = ((2 * E ^ 2 : ℕ) : ℤ) := by
    push_cast
    linarith
  have hnat : (R - (D : ℤ) ^ 2).toNat = 2 * E ^ 2 := by
    exact congrArg Int.toNat hrem
  refine ⟨?_, ?_, ?_⟩
  · exact hrem.symm ▸ Int.natCast_nonneg (2 * E ^ 2)
  · rw [hnat]
    omega
  · rw [hnat]
    omega

#print axioms Paper7MomentCounts.b6_type1122_square_remainder

theorem b6_type1122_square_recovered (D E : ℕ) (R : ℤ)
    (h : (D : ℤ) ^ 2 + 2 * (E : ℤ) ^ 2 = R) :
    b6Type1122SquareE D R = E := by
  unfold b6Type1122SquareE
  rw [(b6_type1122_square_remainder D E R h).2.2, Nat.sqrt_eq']

#print axioms Paper7MomentCounts.b6_type1122_square_recovered

theorem b6_type1122_square_from_test (D B : ℕ) (R : ℤ)
    (h : b6Type1122SquareTest D B R) :
    (D : ℤ) ^ 2 + 2 * (b6Type1122SquareE D R : ℤ) ^ 2 = R ∧
      b6Type1122SquareE D R ≤ B ∧
      b6Type1122SquareE D R % 2 = B % 2 := by
  rcases h with ⟨hnonneg, heven, hsquare, hbound, hparity⟩
  have hdivision := Nat.mod_add_div (R - (D : ℤ) ^ 2).toNat 2
  have hnat : (R - (D : ℤ) ^ 2).toNat =
      2 * b6Type1122SquareE D R ^ 2 := by
    omega
  have hint : ((R - (D : ℤ) ^ 2).toNat : ℤ) =
      2 * (b6Type1122SquareE D R : ℤ) ^ 2 := by
    exact_mod_cast hnat
  rw [Int.toNat_of_nonneg hnonneg] at hint
  refine ⟨?_, hbound, hparity⟩
  linarith

#print axioms Paper7MomentCounts.b6_type1122_square_from_test

theorem b6_type1122_square_row_iff (D B E : ℕ) (R : ℤ) :
    ((D : ℤ) ^ 2 + 2 * (E : ℤ) ^ 2 = R ∧ E ≤ B ∧ E % 2 = B % 2) ↔
      b6Type1122SquareTest D B R ∧ E = b6Type1122SquareE D R := by
  constructor
  · rintro ⟨heq, hbound, hparity⟩
    have hrem := b6_type1122_square_remainder D E R heq
    have hrec := b6_type1122_square_recovered D E R heq
    refine ⟨?_, hrec.symm⟩
    refine ⟨hrem.1, hrem.2.1, ?_, ?_, ?_⟩
    · exact (congrArg (fun n : ℕ => n ^ 2) hrec).trans hrem.2.2.symm
    · exact hrec.symm ▸ hbound
    · exact hrec.symm ▸ hparity
  · rintro ⟨htest, rfl⟩
    exact b6_type1122_square_from_test D B R htest

#print axioms Paper7MomentCounts.b6_type1122_square_row_iff

theorem b6_type1122_square_exists_unique_iff (D B : ℕ) (R : ℤ) :
    (∃! E : ℕ,
      (D : ℤ) ^ 2 + 2 * (E : ℤ) ^ 2 = R ∧ E ≤ B ∧ E % 2 = B % 2) ↔
      b6Type1122SquareTest D B R := by
  constructor
  · rintro ⟨E, hE, _⟩
    exact ((b6_type1122_square_row_iff D B E R).1 hE).1
  · intro htest
    refine ⟨b6Type1122SquareE D R, b6_type1122_square_from_test D B R htest, ?_⟩
    intro E hE
    exact (b6_type1122_square_recovered D E R hE.1).symm

#print axioms Paper7MomentCounts.b6_type1122_square_exists_unique_iff

/-- The actual bounded second-difference fibre, including its parity. -/
abbrev b6Type1122SquareFibre (D B : ℕ) (R : ℤ) : Type :=
  {e : Fin (B + 1) //
    (D : ℤ) ^ 2 + 2 * (e.val : ℤ) ^ 2 = R ∧ e.val % 2 = B % 2}

#print axioms Paper7MomentCounts.b6Type1122SquareFibre

theorem b6_type1122_square_fibre_subsingleton (D B : ℕ) (R : ℤ) :
    Subsingleton (b6Type1122SquareFibre D B R) := by
  refine ⟨?_⟩
  intro e f
  apply Subtype.ext
  apply Fin.ext
  exact (b6_type1122_square_recovered D e.val.val R e.property.1).symm.trans
    (b6_type1122_square_recovered D f.val.val R f.property.1)

#print axioms Paper7MomentCounts.b6_type1122_square_fibre_subsingleton

theorem b6_type1122_square_fibre_nonempty_iff (D B : ℕ) (R : ℤ) :
    Nonempty (b6Type1122SquareFibre D B R) ↔ b6Type1122SquareTest D B R := by
  constructor
  · rintro ⟨e⟩
    exact ((b6_type1122_square_row_iff D B e.val.val R).1
      ⟨e.property.1, Nat.le_of_lt_succ e.val.isLt, e.property.2⟩).1
  · intro htest
    have h := b6_type1122_square_from_test D B R htest
    exact ⟨⟨⟨b6Type1122SquareE D R, Nat.lt_succ_iff.mpr h.2.1⟩, h.1, h.2.2⟩⟩

#print axioms Paper7MomentCounts.b6_type1122_square_fibre_nonempty_iff

theorem b6_type1122_square_weighted_sum {M : Type*} [AddCommMonoid M]
    (D B : ℕ) (R : ℤ) (w : ℕ → M) :
    (∑ e : Fin (B + 1),
      if (D : ℤ) ^ 2 + 2 * (e.val : ℤ) ^ 2 = R ∧ e.val % 2 = B % 2
      then w e.val else 0) =
      if b6Type1122SquareTest D B R then w (b6Type1122SquareE D R) else 0 := by
  classical
  by_cases htest : b6Type1122SquareTest D B R
  · rw [ite_eq_left htest]
    obtain ⟨heq, hbound, hparity⟩ := b6_type1122_square_from_test D B R htest
    let e₀ : Fin (B + 1) :=
      ⟨b6Type1122SquareE D R, Nat.lt_succ_iff.mpr hbound⟩
    have hpred : ∀ e : Fin (B + 1),
        ((D : ℤ) ^ 2 + 2 * (e.val : ℤ) ^ 2 = R ∧ e.val % 2 = B % 2) ↔ e = e₀ := by
      intro e
      constructor
      · intro h
        apply Fin.ext
        exact (b6_type1122_square_recovered D e.val R h.1).symm
      · rintro rfl
        exact ⟨heq, hparity⟩
    simp_rw [hpred]
    exact Fintype.sum_ite_eq' e₀ (fun e => w e.val)
  · rw [ite_eq_right htest]
    apply Finset.sum_eq_zero
    intro e _
    apply ite_eq_right
    intro he
    exact htest (((b6_type1122_square_row_iff D B e.val R).1
      ⟨he.1, Nat.le_of_lt_succ e.isLt, he.2⟩).1)

#print axioms Paper7MomentCounts.b6_type1122_square_weighted_sum

theorem b6_type1122_square_fibre_weighted_sum {M : Type*} [AddCommMonoid M]
    (D B : ℕ) (R : ℤ) (w : ℕ → M) :
    (∑ e : b6Type1122SquareFibre D B R, w e.val.val) =
      if b6Type1122SquareTest D B R then w (b6Type1122SquareE D R) else 0 := by
  classical
  by_cases htest : b6Type1122SquareTest D B R
  · rw [ite_eq_left htest]
    have h := b6_type1122_square_from_test D B R htest
    let e₀ : b6Type1122SquareFibre D B R :=
      ⟨⟨b6Type1122SquareE D R, Nat.lt_succ_iff.mpr h.2.1⟩, h.1, h.2.2⟩
    calc
      (∑ e : b6Type1122SquareFibre D B R, w e.val.val) = w e₀.val.val := by
        apply Finset.sum_eq_single_of_mem e₀ (Finset.mem_univ e₀)
        intro e _ hne
        exact False.elim (hne ((b6_type1122_square_fibre_subsingleton D B R).elim e e₀))
      _ = w (b6Type1122SquareE D R) := rfl
  · rw [ite_eq_right htest]
    apply Finset.sum_eq_zero
    intro e _
    exact False.elim (htest ((b6_type1122_square_fibre_nonempty_iff D B R).1 ⟨e⟩))

#print axioms Paper7MomentCounts.b6_type1122_square_fibre_weighted_sum

theorem b6_type1122_square_fibre_card (D B : ℕ) (R : ℤ) :
    Fintype.card (b6Type1122SquareFibre D B R) =
      if b6Type1122SquareTest D B R then 1 else 0 := by
  simpa using b6_type1122_square_fibre_weighted_sum D B R (fun _ => (1 : ℕ))

#print axioms Paper7MomentCounts.b6_type1122_square_fibre_card

end Paper7MomentCounts
