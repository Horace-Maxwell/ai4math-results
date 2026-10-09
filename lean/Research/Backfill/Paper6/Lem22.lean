import Research.Backfill.Paper6.ChallengeV3
import Research.Backfill.Paper6.Cat4Weight

/-!
# Paper 6 V3: the complete binary half-decomposition lemma

All five conjuncts of the frozen `BackfillPaper6.V3.Lem22` are retained.
For the difficult code-membership direction, rotate the last variable to the
first variable and apply `MvPolynomial.finSuccEquiv`. The zero slice is the
constant coefficient, and the sum of the two slices is the sum of all positive
coefficients. Mathlib bounds the degree of coefficient i plus i by the degree
of the original polynomial, giving the required one-degree decrease.

The reverse direction explicitly constructs p + X_last q after renaming the
smaller variable set. The counting statements follow from structural binary
slicing and a four-case scalar indicator identity. No positivity assumption
on m or r and no multilinearity assumption are added.

Frozen manifest SHA-256:
bd2a50001623f163ad304a88b2ae484434924c97820e9373f8a83517c1d59f61.
Draft only: compilation and acceptance are controlled by the root agent.
-/

set_option autoImplicit false

namespace Paper6HalfDecomposition

open BackfillPaper6.V3

/-- Reconstruction from the two binary slices, valid for every binary function. -/
theorem reconstruct (m : ℕ) (f : BFun (m + 1)) (y : Pt (m + 1)) :
    f y = half0 f (Fin.init y) + y (Fin.last m) *
      (half0 f (Fin.init y) + half1 f (Fin.init y)) := by
  have hbit : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide
  rcases hbit (y (Fin.last m)) with h | h
  · have hy : Fin.snoc (α := fun _ => ZMod 2) (Fin.init y) 0 = y := by
      simpa only [h] using Fin.snoc_init_self y
    simp only [h, zero_mul, add_zero, half0, hy]
  · have hy : Fin.snoc (α := fun _ => ZMod 2) (Fin.init y) 1 = y := by
      simpa only [h] using Fin.snoc_init_self y
    simp only [h, one_mul, half0, half1, hy, CharTwo.add_cancel_left]

/-- View the last variable as a univariate variable with coefficients in the first m variables. -/
noncomputable def coefficientPolynomial {m : ℕ}
    (p : MvPolynomial (Fin (m + 1)) (ZMod 2)) :
    Polynomial (MvPolynomial (Fin m) (ZMod 2)) :=
  MvPolynomial.finSuccEquiv (ZMod 2) m
    (MvPolynomial.rename (finRotate (m + 1)) p)

/-- The first polynomial witness is the constant coefficient in the last variable. -/
noncomputable def zeroPart {m : ℕ}
    (p : MvPolynomial (Fin (m + 1)) (ZMod 2)) : MvPolynomial (Fin m) (ZMod 2) :=
  (coefficientPolynomial p).coeff 0

/-- The second witness sums all positive-degree coefficients in the last variable. -/
noncomputable def deltaPart {m : ℕ}
    (p : MvPolynomial (Fin (m + 1)) (ZMod 2)) : MvPolynomial (Fin m) (ZMod 2) :=
  ∑ i ∈ (coefficientPolynomial p).support.erase 0, (coefficientPolynomial p).coeff i

/-- Evaluation after rotating variables agrees with evaluating the actual last-coordinate slice. -/
theorem eval_coefficientPolynomial_slice {m : ℕ}
    (p : MvPolynomial (Fin (m + 1)) (ZMod 2)) (x : Pt m) (c : ZMod 2) :
    MvPolynomial.eval x ((coefficientPolynomial p).eval (MvPolynomial.C c)) =
      MvPolynomial.eval (Fin.snoc (α := fun _ => ZMod 2) x c) p := by
  unfold coefficientPolynomial
  rw [MvPolynomial.eval_polynomial_eval_finSuccEquiv,
    MvPolynomial.eval_C, MvPolynomial.eval_rename, Fin.snoc_eq_cons_rotate]
  rfl

/-- The degree of a nonzero coefficient decreases by at least its index. -/
theorem coefficient_degree_add_le {m : ℕ}
    (p : MvPolynomial (Fin (m + 1)) (ZMod 2)) (i : ℕ)
    (hi : (coefficientPolynomial p).coeff i ≠ 0) :
    ((coefficientPolynomial p).coeff i).totalDegree + i ≤ p.totalDegree := by
  exact
    (MvPolynomial.totalDegree_coeff_finSuccEquiv_add_le
      (MvPolynomial.rename (finRotate (m + 1)) p) i hi).trans
      (MvPolynomial.totalDegree_rename_le (finRotate (m + 1)) p)

/-- Restricting the last coordinate to zero cannot increase total degree. -/
theorem zeroPart_degree_le {m : ℕ}
    (p : MvPolynomial (Fin (m + 1)) (ZMod 2)) :
    (zeroPart p).totalDegree ≤ p.totalDegree := by
  classical
  by_cases hzero : (coefficientPolynomial p).coeff 0 = 0
  · simp only [zeroPart, hzero, MvPolynomial.totalDegree_zero]
    exact Nat.zero_le _
  · simpa only [zeroPart, add_zero] using coefficient_degree_add_le p 0 hzero

/-- The difference of the two slices has degree at most r when p has degree at most r+1. -/
theorem deltaPart_degree_le {m : ℕ}
    (p : MvPolynomial (Fin (m + 1)) (ZMod 2)) (r : ℕ)
    (hp : p.totalDegree ≤ r + 1) : (deltaPart p).totalDegree ≤ r := by
  classical
  unfold deltaPart
  apply MvPolynomial.totalDegree_finsetSum_le
  intro i hi
  have hi' := Finset.mem_erase.mp hi
  have hcoeff : (coefficientPolynomial p).coeff i ≠ 0 :=
    Polynomial.mem_support_iff.mp hi'.2
  have hdegree := coefficient_degree_add_le p i hcoeff
  omega

/-- Splitting the evaluation at one into its constant term and positive-index terms. -/
theorem eval_one_eq_coeff_zero_add_sum_erase {m : ℕ}
    (q : Polynomial (MvPolynomial (Fin m) (ZMod 2))) :
    q.eval 1 = q.coeff 0 + ∑ i ∈ q.support.erase 0, q.coeff i := by
  classical
  simp only [Polynomial.eval_eq_sum, Polynomial.sum_def, one_pow, mul_one]
  by_cases hzero : 0 ∈ q.support
  · exact (Finset.add_sum_erase q.support q.coeff hzero).symm
  · have hc : q.coeff 0 = 0 := Polynomial.notMem_support_iff.mp hzero
    simp only [Finset.erase_eq_of_notMem hzero, hc, zero_add]

/-- Evaluating the constant coefficient gives the zero slice. -/
theorem eval_zeroPart {m : ℕ}
    (p : MvPolynomial (Fin (m + 1)) (ZMod 2)) (x : Pt m) :
    MvPolynomial.eval x (zeroPart p) =
      MvPolynomial.eval (Fin.snoc (α := fun _ => ZMod 2) x 0) p := by
  unfold zeroPart
  rw [Polynomial.coeff_zero_eq_eval_zero]
  simpa only [MvPolynomial.C_0] using eval_coefficientPolynomial_slice p x 0

/-- Evaluating the positive coefficient sum gives the sum of the zero and one slices. -/
theorem eval_deltaPart {m : ℕ}
    (p : MvPolynomial (Fin (m + 1)) (ZMod 2)) (x : Pt m) :
    MvPolynomial.eval x (deltaPart p) =
      MvPolynomial.eval (Fin.snoc (α := fun _ => ZMod 2) x 0) p +
      MvPolynomial.eval (Fin.snoc (α := fun _ => ZMod 2) x 1) p := by
  have hsplit := congrArg (MvPolynomial.eval x)
    (eval_one_eq_coeff_zero_add_sum_erase (coefficientPolynomial p))
  rw [MvPolynomial.eval_add] at hsplit
  have hzero : MvPolynomial.eval x ((coefficientPolynomial p).coeff 0) =
      MvPolynomial.eval (Fin.snoc (α := fun _ => ZMod 2) x 0) p :=
    eval_zeroPart p x
  have hone : MvPolynomial.eval x ((coefficientPolynomial p).eval 1) =
      MvPolynomial.eval (Fin.snoc (α := fun _ => ZMod 2) x 1) p := by
    simpa only [MvPolynomial.C_1] using eval_coefficientPolynomial_slice p x 1
  rw [hzero, hone] at hsplit
  have hflip : ∀ a b c : ZMod 2, b = a + c → c = a + b := by decide
  exact hflip _ _ _ hsplit

/-- The zero slice is represented by the constructed zeroPart polynomial. -/
theorem half0_evalFun {m : ℕ}
    (p : MvPolynomial (Fin (m + 1)) (ZMod 2)) :
    half0 (evalFun p) = evalFun (zeroPart p) := by
  funext x
  exact (eval_zeroPart p x).symm

/-- The sum of the two slices is represented by the constructed deltaPart polynomial. -/
theorem halves_sum_evalFun {m : ℕ}
    (p : MvPolynomial (Fin (m + 1)) (ZMod 2)) :
    half0 (evalFun p) + half1 (evalFun p) = evalFun (deltaPart p) := by
  funext x
  exact (eval_deltaPart p x).symm

/-- The full forward implication, including the one-degree decrease. -/
theorem rm_slices_of_mem (m r : ℕ) (f : BFun (m + 1))
    (hf : f ∈ RM (r + 1) (m + 1)) :
    half0 f ∈ RM (r + 1) m ∧ (half0 f + half1 f) ∈ RM r m := by
  rcases hf with ⟨p, hp, rfl⟩
  exact
    ⟨⟨zeroPart p, (zeroPart_degree_le p).trans hp, half0_evalFun p⟩,
      ⟨deltaPart p, deltaPart_degree_le p r hp, halves_sum_evalFun p⟩⟩

/-- The actual larger polynomial used to combine the two lower-dimensional witnesses. -/
noncomputable def combinePolynomial {m : ℕ}
    (p q : MvPolynomial (Fin m) (ZMod 2)) : MvPolynomial (Fin (m + 1)) (ZMod 2) :=
  MvPolynomial.rename Fin.castSucc p +
    MvPolynomial.X (Fin.last m) * MvPolynomial.rename Fin.castSucc q

/-- Degree bound for the reverse construction. -/
theorem combinePolynomial_degree_le {m : ℕ}
    (p q : MvPolynomial (Fin m) (ZMod 2)) (r : ℕ)
    (hp : p.totalDegree ≤ r + 1) (hq : q.totalDegree ≤ r) :
    (combinePolynomial p q).totalDegree ≤ r + 1 := by
  have hp' := MvPolynomial.totalDegree_rename_le Fin.castSucc p
  have hq' := MvPolynomial.totalDegree_rename_le Fin.castSucc q
  have hmul :
      ((MvPolynomial.X (Fin.last m) : MvPolynomial (Fin (m + 1)) (ZMod 2)) *
        MvPolynomial.rename Fin.castSucc q).totalDegree ≤ r + 1 := by
    refine (MvPolynomial.totalDegree_mul _ _).trans ?_
    rw [MvPolynomial.totalDegree_X]
    omega
  exact (MvPolynomial.totalDegree_add _ _).trans (max_le (hp'.trans hp) hmul)

/-- Evaluation of the reverse construction has the required last-variable formula. -/
theorem eval_combinePolynomial {m : ℕ}
    (p q : MvPolynomial (Fin m) (ZMod 2)) (y : Pt (m + 1)) :
    evalFun (combinePolynomial p q) y =
      evalFun p (Fin.init y) + y (Fin.last m) * evalFun q (Fin.init y) := by
  simp only [evalFun, combinePolynomial, MvPolynomial.eval_add,
    MvPolynomial.eval_mul, MvPolynomial.eval_X, MvPolynomial.eval_rename]
  rfl

/-- The reverse implication constructs a polynomial of the exact required degree. -/
theorem rm_mem_of_slices (m r : ℕ) (f : BFun (m + 1))
    (hzero : half0 f ∈ RM (r + 1) m)
    (hdelta : (half0 f + half1 f) ∈ RM r m) :
    f ∈ RM (r + 1) (m + 1) := by
  rcases hzero with ⟨p, hp, hzero⟩
  rcases hdelta with ⟨q, hq, hdelta⟩
  refine ⟨combinePolynomial p q, combinePolynomial_degree_le p q r hp hq, ?_⟩
  funext y
  calc
    f y = half0 f (Fin.init y) + y (Fin.last m) *
        (half0 f (Fin.init y) + half1 f (Fin.init y)) := reconstruct m f y
    _ = evalFun p (Fin.init y) + y (Fin.last m) * evalFun q (Fin.init y) := by
      change half0 f (Fin.init y) + y (Fin.last m) *
        ((half0 f + half1 f) (Fin.init y)) = _
      rw [hdelta, hzero]
    _ = evalFun (combinePolynomial p q) y := (eval_combinePolynomial p q y).symm

/-- Exact code-membership equivalence with no extra boundary assumptions. -/
theorem rm_iff_slices (m r : ℕ) (f : BFun (m + 1)) :
    f ∈ RM (r + 1) (m + 1) ↔
      half0 f ∈ RM (r + 1) m ∧ (half0 f + half1 f) ∈ RM r m :=
  ⟨rm_slices_of_mem m r f, fun h => rm_mem_of_slices m r f h.1 h.2⟩

/-- Structural splitting of Hamming weight, reusing the previously accepted generic lemma. -/
theorem weight_slices (m : ℕ) (f : BFun (m + 1)) :
    hammingNorm f = hammingNorm (half0 f) + hammingNorm (half1 f) := by
  change hammingNorm f =
    hammingNorm (fun x : Pt m => f (Fin.snoc (α := fun _ => ZMod 2) x 0)) +
    hammingNorm (fun x : Pt m => f (Fin.snoc (α := fun _ => ZMod 2) x 1))
  exact Paper6Cat4Weight.hammingNorm_snoc f

/-- Convert support-intersection ncard to a finite count of simultaneous nonzero values. -/
theorem support_inter_ncard_eq_count {ι : Type*} [Fintype ι] (g h : ι → ZMod 2) :
    (Function.support g ∩ Function.support h).ncard =
      (Finset.univ.filter (fun x : ι => g x ≠ 0 ∧ h x ≠ 0)).card := by
  classical
  have hset : Function.support g ∩ Function.support h =
      ((Finset.univ.filter (fun x : ι => g x ≠ 0 ∧ h x ≠ 0)) : Set ι) := by
    ext x
    change (g x ≠ 0 ∧ h x ≠ 0) ↔
      x ∈ Finset.univ.filter (fun x : ι => g x ≠ 0 ∧ h x ≠ 0)
    simp
  rw [hset, Set.ncard_coe_finset]

/-- Weight of a binary sum, with the intersection correction as an exact natural-number equality. -/
theorem weight_add_with_intersection {ι : Type*} [Fintype ι] (g h : ι → ZMod 2) :
    hammingNorm g + hammingNorm h = hammingNorm (g + h) +
      2 * (Function.support g ∩ Function.support h).ncard := by
  classical
  have hbit : ∀ a b : ZMod 2,
      (if a ≠ 0 then 1 else 0 : ℕ) + (if b ≠ 0 then 1 else 0 : ℕ) =
        (if a + b ≠ 0 then 1 else 0 : ℕ) +
          2 * (if a ≠ 0 ∧ b ≠ 0 then 1 else 0 : ℕ) := by decide
  rw [support_inter_ncard_eq_count]
  simp only [hammingNorm, Finset.card_filter, Pi.add_apply]
  calc
    _ = ∑ x : ι, ((if g x ≠ 0 then 1 else 0 : ℕ) +
        (if h x ≠ 0 then 1 else 0 : ℕ)) := Finset.sum_add_distrib.symm
    _ = ∑ x : ι, ((if g x + h x ≠ 0 then 1 else 0 : ℕ) +
        2 * (if g x ≠ 0 ∧ h x ≠ 0 then 1 else 0 : ℕ)) := by
      apply Finset.sum_congr rfl
      intro x _hx
      exact hbit (g x) (h x)
    _ = _ := by rw [Finset.sum_add_distrib, ← Finset.mul_sum]

/-- Over the binary field, the support intersection is the indicated support difference. -/
theorem support_inter_eq_sdiff {ι : Type*} (g h : ι → ZMod 2) :
    Function.support g ∩ Function.support h =
      Function.support g \ Function.support (g + h) := by
  have hbit : ∀ a b : ZMod 2,
      (a ≠ 0 ∧ b ≠ 0) ↔ (a ≠ 0 ∧ ¬ (a + b ≠ 0)) := by decide
  ext x
  change (g x ≠ 0 ∧ h x ≠ 0) ↔ (g x ≠ 0 ∧ ¬ (g x + h x ≠ 0))
  exact hbit (g x) (h x)

/-- All five conjuncts of the unchanged frozen lemma. -/
theorem lem22 : BackfillPaper6.V3.Lem22 := by
  intro m r f
  refine ⟨reconstruct m f, rm_iff_slices m r f, weight_slices m f, ?_,
    support_inter_eq_sdiff (half0 f) (half1 f)⟩
  exact (weight_slices m f).trans
    (weight_add_with_intersection (half0 f) (half1 f))

/-- Exact frozen-type check; not an additional mathematical result. -/
theorem check_Lem22 : BackfillPaper6.V3.Lem22 := lem22

end Paper6HalfDecomposition

#print axioms Paper6HalfDecomposition.reconstruct
#print axioms Paper6HalfDecomposition.eval_coefficientPolynomial_slice
#print axioms Paper6HalfDecomposition.coefficient_degree_add_le
#print axioms Paper6HalfDecomposition.zeroPart_degree_le
#print axioms Paper6HalfDecomposition.deltaPart_degree_le
#print axioms Paper6HalfDecomposition.eval_one_eq_coeff_zero_add_sum_erase
#print axioms Paper6HalfDecomposition.eval_zeroPart
#print axioms Paper6HalfDecomposition.eval_deltaPart
#print axioms Paper6HalfDecomposition.half0_evalFun
#print axioms Paper6HalfDecomposition.halves_sum_evalFun
#print axioms Paper6HalfDecomposition.rm_slices_of_mem
#print axioms Paper6HalfDecomposition.combinePolynomial_degree_le
#print axioms Paper6HalfDecomposition.eval_combinePolynomial
#print axioms Paper6HalfDecomposition.rm_mem_of_slices
#print axioms Paper6HalfDecomposition.rm_iff_slices
#print axioms Paper6HalfDecomposition.weight_slices
#print axioms Paper6HalfDecomposition.support_inter_ncard_eq_count
#print axioms Paper6HalfDecomposition.weight_add_with_intersection
#print axioms Paper6HalfDecomposition.support_inter_eq_sdiff
#print axioms Paper6HalfDecomposition.lem22
#print axioms Paper6HalfDecomposition.check_Lem22
#print Paper6HalfDecomposition.check_Lem22
