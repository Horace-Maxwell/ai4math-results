import Research.Backfill.Paper7.C61DoubleRootMonodromy
import Research.Backfill.Paper7.C61ThreeUnitWitness
import Research.Backfill.Paper7.C61ThreeQpositiveAlgebra
import Research.Backfill.Paper7.C61FinSixIndexSimp

/-! NEW SOURCE ONLY. Multiplicity-one trace and multiplicity-two monodromy
constraints, with coordinate-preserving cyclic transport. -/
set_option autoImplicit false
noncomputable section
namespace Paper7C61Four
open BackfillPaper7.Challenge BackfillPaper7.Challenge.Legacy.Algebra
open Paper7C61Profile Paper7C61Three
open scoped Matrix Classical

def TraceTwo (p q : Fin 6 → ℕ) : Prop :=
  (realSixProduct (coefficientTwo p q 0) (coefficientTwo p q 1)
    (coefficientTwo p q 2) (coefficientTwo p q 3)
    (coefficientTwo p q 4) (coefficientTwo p q 5)).trace = 2
#print axioms Paper7C61Four.TraceTwo

def coefficientThree (p q : Fin 6 → ℕ) (k : Fin 6) : ℝ :=
  3 - (p k : ℝ) / 3 - 3 * (q k : ℝ) / 8
#print axioms Paper7C61Four.coefficientThree

def PairThree (p q : Fin 6 → ℕ) : Prop :=
  coefficientThree p q 0 * coefficientThree p q 1 +
    coefficientThree p q 3 * coefficientThree p q 4 = 2 ∧
  coefficientThree p q 1 * coefficientThree p q 2 +
    coefficientThree p q 4 * coefficientThree p q 5 = 2 ∧
  coefficientThree p q 2 * coefficientThree p q 3 +
    coefficientThree p q 5 * coefficientThree p q 0 = 2
#print axioms Paper7C61Four.PairThree

def ThreeCardData (p q : Fin 6 → ℕ) : Prop :=
  (TraceTwo p q ∧ totalP 6 p + totalQ 6 q = 23) ∨
  (PairThree p q ∧ totalP 6 p + totalQ 6 q = 28)
#print axioms Paper7C61Four.ThreeCardData

theorem real_six_trace_rotate (a b c d e f : ℝ) :
    (realSixProduct b c d e f a).trace = (realSixProduct a b c d e f).trace := by
  simpa [realSixProduct, mul_assoc] using
    Matrix.trace_mul_comm (realTransfer a)
      (realTransfer f * realTransfer e * realTransfer d * realTransfer c * realTransfer b)
#print axioms Paper7C61Four.real_six_trace_rotate

theorem trace_two_shift (p q : Fin 6 → ℕ) (h : TraceTwo p q) :
    TraceTwo (shiftSix p) (shiftSix q) := by
  unfold TraceTwo at h ⊢
  have hh := (real_six_trace_rotate (coefficientTwo p q 0) (coefficientTwo p q 1)
    (coefficientTwo p q 2) (coefficientTwo p q 3)
    (coefficientTwo p q 4) (coefficientTwo p q 5)).trans h
  simpa [coefficientTwo, shiftSix] using hh
#print axioms Paper7C61Four.trace_two_shift

theorem pair_three_shift (p q : Fin 6 → ℕ) (h : PairThree p q) :
    PairThree (shiftSix p) (shiftSix q) := by
  obtain ⟨h0, h1, h2⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · simpa [coefficientThree, shiftSix] using h1
  · simpa [coefficientThree, shiftSix] using h2
  · simpa [coefficientThree, shiftSix, add_comm] using h0
#print axioms Paper7C61Four.pair_three_shift

theorem three_card_data_shift (p q : Fin 6 → ℕ) (h : ThreeCardData p q) :
    ThreeCardData (shiftSix p) (shiftSix q) := by
  rcases h with ⟨ht, hs⟩ | ⟨hp, hs⟩
  · exact Or.inl ⟨trace_two_shift p q ht, by rw [total_shift]; exact hs⟩
  · exact Or.inr ⟨pair_three_shift p q hp, by rw [total_shift]; exact hs⟩
#print axioms Paper7C61Four.three_card_data_shift

theorem actual_two_once_trace (p q : Fin 6 → ℕ)
    (h : (actual p q 0).val = 1) : TraceTwo p q := by
  have hm : mult (SG 6 p q) 2 = 1 := by
    have hi := actual_eq_mult p q (0 : Fin 5)
    norm_num [value] at hi
    omega
  have ht := ((Paper7Lemma22Periodic.lemma22_ordinary_clause 6 p q (by decide)
    2 (by norm_num) (by norm_num) (by norm_num)).2.2.2.mp hm).2
  rwa [mono_two_six_product] at ht
#print axioms Paper7C61Four.actual_two_once_trace

theorem actual_three_twice_pair_three (p q : Fin 6 → ℕ)
    (h : (actual p q 1).val = 2) : PairThree p q := by
  obtain ⟨h0, h1, h2⟩ := ordinary_monodromy_pairs p q 3 (actual_three_monodromy p q h)
  norm_num [fk] at h0 h1 h2
  unfold PairThree coefficientThree
  exact ⟨by nlinarith only [h0], by nlinarith only [h1], by nlinarith only [h2]⟩
#print axioms Paper7C61Four.actual_three_twice_pair_three

end Paper7C61Four
