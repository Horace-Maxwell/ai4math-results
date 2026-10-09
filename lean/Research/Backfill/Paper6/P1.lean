import Research.Backfill.Paper6.ChallengeV3

/-!
# Paper 6 V3: parity, the coefficient identity, and complement weights

This candidate proves all four conjuncts of the frozen `BackfillPaper6.V3.P1`.
The Hamming norm cast to ZMod 2 is the sum of function values. Summing a
monomial over all binary points factors coordinatewise: a missing variable
contributes 0, and a positive exponent contributes 1. Thus only monomials
involving every variable contribute to the coefficient formula. A polynomial
of total degree less than m has no such monomial and has even Hamming weight.
Adding one swaps zero and nonzero values and preserves every nonnegative
degree bound; its weight is the complementary weight, also in the same code.

No restriction is added at m = 0 or r = 0. The frozen first conjunct already
contains r < m; the remaining three conjuncts have no positivity restriction.

Frozen manifest SHA-256:
bd2a50001623f163ad304a88b2ae484434924c97820e9373f8a83517c1d59f61.
This source is a draft pending root-controlled compilation and acceptance.
-/

set_option autoImplicit false

namespace Paper6Parity

open BackfillPaper6.V3

/-- Over the binary field, Hamming weight modulo two is the sum of all values. -/
theorem hammingNorm_cast_eq_sum {ι : Type*} [Fintype ι] (f : ι → ZMod 2) :
    ((hammingNorm f : ℕ) : ZMod 2) = ∑ i, f i := by
  classical
  rw [hammingNorm, Finset.card_filter, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro i _hi
  have hbit : ∀ z : ZMod 2, ((if z ≠ 0 then 1 else 0 : ℕ) : ZMod 2) = z := by
    decide
  exact hbit (f i)

/-- A zero exponent sums to zero over the binary field, and a positive one to one. -/
theorem binary_power_sum (n : ℕ) :
    (∑ z : ZMod 2, z ^ n) = if n ≠ 0 then 1 else 0 := by
  classical
  rw [show (Finset.univ : Finset (ZMod 2)) = {0, 1} from rfl]
  by_cases hn : n = 0
  · subst n
    decide
  · simp [hn]

/-- The sum of a monomial over all points detects whether every variable occurs. -/
theorem sum_monomial_values {m : ℕ} (d : Fin m →₀ ℕ) :
    (∑ x : Pt m, ∏ i : Fin m, x i ^ d i) =
      if ∀ i : Fin m, d i ≠ 0 then (1 : ZMod 2) else 0 := by
  classical
  calc
    (∑ x : Pt m, ∏ i : Fin m, x i ^ d i) =
        ∏ i : Fin m, ∑ z : ZMod 2, z ^ d i :=
      (Fintype.prod_sum (fun i : Fin m => fun z : ZMod 2 => z ^ d i)).symm
    _ = ∏ i : Fin m, (if d i ≠ 0 then (1 : ZMod 2) else 0) := by
      apply Finset.prod_congr rfl
      intro i _hi
      exact binary_power_sum (d i)
    _ = (if ∀ i : Fin m, d i ≠ 0 then (1 : ZMod 2) else 0) := by
      by_cases hfull : ∀ i : Fin m, d i ≠ 0
      · have hprod : (∏ i : Fin m, (if d i ≠ 0 then (1 : ZMod 2) else 0)) = 1 := by
          apply Finset.prod_eq_one
          intro i _hi
          simp [hfull i]
        exact hprod.trans (ite_eq_left hfull).symm
      · obtain ⟨i, hi⟩ : ∃ i : Fin m, d i = 0 := by
          simpa only [not_forall, ne_eq, not_not] using hfull
        have hprod : (∏ i : Fin m, (if d i ≠ 0 then (1 : ZMod 2) else 0)) = 0 :=
          Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])
        simpa only [hfull, ↓reduceIte] using hprod

/-- Summing polynomial evaluation keeps precisely the full-variable-support coefficients. -/
theorem sum_eval_eq_full_coeff_sum (m : ℕ)
    (p : MvPolynomial (Fin m) (ZMod 2)) :
    (∑ x : Pt m, MvPolynomial.eval x p) =
      ∑ d ∈ p.support.filter (fun d => ∀ i, d i ≠ 0), p.coeff d := by
  classical
  calc
    (∑ x : Pt m, MvPolynomial.eval x p) =
        ∑ x : Pt m, ∑ d ∈ p.support, p.coeff d * ∏ i : Fin m, x i ^ d i := by
      simp_rw [MvPolynomial.eval_eq']
    _ = ∑ d ∈ p.support, ∑ x : Pt m, p.coeff d * ∏ i : Fin m, x i ^ d i :=
      Finset.sum_comm
    _ = ∑ d ∈ p.support, p.coeff d *
        (if ∀ i : Fin m, d i ≠ 0 then (1 : ZMod 2) else 0) := by
      apply Finset.sum_congr rfl
      intro d _hd
      rw [← Finset.mul_sum, sum_monomial_values]
    _ = _ := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro d _hd
      by_cases hd : ∀ i : Fin m, d i ≠ 0 <;> simp [hd]

/-- The exact coefficient identity of the frozen P1, without positivity hypotheses. -/
theorem coefficient_formula (m : ℕ)
    (p : MvPolynomial (Fin m) (ZMod 2)) :
    ((hammingNorm (evalFun p) : ℕ) : ZMod 2) =
      ∑ d ∈ p.support.filter (fun d => ∀ i, d i ≠ 0), p.coeff d := by
  rw [hammingNorm_cast_eq_sum]
  change (∑ x : Pt m, MvPolynomial.eval x p) = _
  exact sum_eval_eq_full_coeff_sum m p

/-- Total degree below the number of variables excludes every full-support monomial. -/
theorem full_support_filter_eq_empty {m : ℕ}
    (p : MvPolynomial (Fin m) (ZMod 2)) (hp : p.totalDegree < m) :
    p.support.filter (fun d => ∀ i, d i ≠ 0) = ∅ := by
  classical
  apply Finset.filter_eq_empty_iff.mpr
  intro d hd hfull
  have hp' : p.totalDegree < 1 * Fintype.card (Fin m) := by
    simpa only [one_mul, Fintype.card_fin] using hp
  obtain ⟨i, hi⟩ := MvPolynomial.exists_degree_lt p 1 hp' hd
  exact hfull i (by omega)

/-- Every codeword of order strictly below the number of variables has even weight. -/
theorem even_weight (r m : ℕ) (hr : r < m)
    (f : BFun m) (hf : f ∈ RM r m) : Even (hammingNorm f) := by
  rcases hf with ⟨p, hp, rfl⟩
  apply ZMod.natCast_eq_zero_iff_even.mp
  rw [coefficient_formula,
    full_support_filter_eq_empty p (lt_of_le_of_lt hp hr), Finset.sum_empty]

/-- There are exactly 2^m points, including the singleton space at m = 0. -/
theorem card_points (m : ℕ) : Fintype.card (Pt m) = 2 ^ m := by
  change Fintype.card (Fin m → ZMod 2) = 2 ^ m
  rw [Fintype.card_pi_const, ZMod.card]

/-- The Hamming weight of any binary function is bounded by the number of points. -/
theorem hammingNorm_le_points (m : ℕ) (f : BFun m) : hammingNorm f ≤ 2 ^ m := by
  simpa only [card_points] using (hammingNorm_le_card_fintype (x := f))

/-- Adding one swaps the zero and nonzero sets and hence complements the weight. -/
theorem hammingNorm_add_one (m : ℕ) (f : BFun m) :
    hammingNorm (f + 1) = 2 ^ m - hammingNorm f := by
  classical
  have hbit : ∀ z : ZMod 2, z + 1 ≠ 0 ↔ z = 0 := by decide
  have hcomp : hammingNorm (f + 1) =
      (Finset.univ.filter (fun x : Pt m => f x = 0)).card := by
    unfold hammingNorm
    congr 1
    apply Finset.filter_congr
    intro x _hx
    change f x + 1 ≠ 0 ↔ f x = 0
    exact hbit (f x)
  have hsum : hammingNorm f + hammingNorm (f + 1) = 2 ^ m := by
    rw [hcomp]
    have hpartition := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (Pt m))) (fun x : Pt m => f x ≠ 0)
    simpa only [hammingNorm, not_not, Finset.card_univ, card_points] using hpartition
  omega

/-- The concrete polynomial p + 1 preserves any degree bound, including order zero. -/
theorem add_one_mem_RM (r m : ℕ) (f : BFun m) (hf : f ∈ RM r m) :
    (f + 1) ∈ RM r m := by
  rcases hf with ⟨p, hp, rfl⟩
  refine ⟨p + 1, ?_, ?_⟩
  · exact (MvPolynomial.totalDegree_add _ _).trans (max_le hp (by simp))
  · funext x
    change MvPolynomial.eval x p + 1 = MvPolynomial.eval x (p + 1)
    rw [MvPolynomial.eval_add, map_one]

/-- Every attained weight has its complementary attained weight in the same code. -/
theorem complement_weight (r m w : ℕ) (hw : IsWeight r m w) :
    w ≤ 2 ^ m ∧ IsWeight r m (2 ^ m - w) := by
  rcases hw with ⟨f, hf, hweight⟩
  constructor
  · rw [← hweight]
    exact hammingNorm_le_points m f
  · refine ⟨f + 1, add_one_mem_RM r m f hf, ?_⟩
    rw [hammingNorm_add_one, hweight]

/-- All four conjuncts of the exact frozen V3 P1 contract. -/
theorem p1 : BackfillPaper6.V3.P1 := by
  refine ⟨even_weight, coefficient_formula, ?_, complement_weight⟩
  intro r m f hf
  exact ⟨add_one_mem_RM r m f hf, hammingNorm_add_one m f⟩

/-- Exact contract check; the alias is not a separate mathematical target. -/
theorem check_P1 : BackfillPaper6.V3.P1 := p1

end Paper6Parity

#print axioms Paper6Parity.hammingNorm_cast_eq_sum
#print axioms Paper6Parity.binary_power_sum
#print axioms Paper6Parity.sum_monomial_values
#print axioms Paper6Parity.sum_eval_eq_full_coeff_sum
#print axioms Paper6Parity.coefficient_formula
#print axioms Paper6Parity.full_support_filter_eq_empty
#print axioms Paper6Parity.even_weight
#print axioms Paper6Parity.card_points
#print axioms Paper6Parity.hammingNorm_le_points
#print axioms Paper6Parity.hammingNorm_add_one
#print axioms Paper6Parity.add_one_mem_RM
#print axioms Paper6Parity.complement_weight
#print axioms Paper6Parity.p1
#print axioms Paper6Parity.check_P1
#print Paper6Parity.check_P1
