import Research.Backfill.Paper6.LiteralNumeric
import Research.Backfill.Paper6.LouWang
import Research.Backfill.Paper6.P1
import Research.Backfill.Paper6.MinDist

/-! Source-only semantic bridge for the exact literal Lou–Wang construction.
Repeated indices and both arbitrary binary constants are retained. No small-weight
classification or exclusion of 322 is assumed in this module. -/

set_option autoImplicit false

namespace Paper6LiteralLouWang

open BackfillPaper6.V3

def sequenceSet (i : Fin 6 → Fin 12) : Finset (Fin 12) := Finset.univ.image i

theorem sequenceSet_card (i : Fin 6 → Fin 12) : (sequenceSet i).card ≤ 6 := by
  simpa [sequenceSet] using Finset.card_image_le (s := Finset.univ) (f := i)

/-- A repeated-index product has exactly the same values as its image-set product. -/
theorem prodSeq_as_set (i : Fin 6 → Fin 12) :
    prodSeq i = fun x => ∏ j ∈ sequenceSet i, x j := by
  funext x
  have hbinary : ∀ a b : ZMod 2, (a = 1 ↔ b = 1) → a = b := by decide
  apply hbinary
  unfold prodSeq sequenceSet
  rw [Paper6InclusionExclusion.binary_prod_one_iff,
    Paper6InclusionExclusion.binary_prod_one_iff]
  simp only [Finset.mem_univ, forall_true_left]
  constructor
  · intro h j hj
    obtain ⟨a, _ha, rfl⟩ := Finset.mem_image.mp hj
    exact h a
  · intro h a
    exact h (i a) (Finset.mem_image.mpr ⟨a, Finset.mem_univ a, rfl⟩)

def tripleFunction (i j : Fin 6 → Fin 12) : BFun 12 := x16 + prodSeq i + prodSeq j

theorem triple_as_sum (i j : Fin 6 → Fin 12) :
    tripleFunction i j = fun x : Pt 12 =>
      ∑ a : Fin 3, ∏ b ∈ (![({0, 1, 2, 3, 4, 5} : Finset (Fin 12)),
        sequenceSet i, sequenceSet j] a), x b := by
  rw [tripleFunction, prodSeq_as_set i, prodSeq_as_set j]
  funext x
  simp [Fin.sum_univ_succ, x16, add_assoc]

theorem cancel_common_scalar (a b c d e : ZMod 2) :
    (a + b + c) + (a + d + e) = b + c + d + e := by
  revert a b c d e
  decide

theorem triples_sum_as_four (i1 i2 i3 i4 : Fin 6 → Fin 12) :
    tripleFunction i1 i2 + tripleFunction i3 i4 = fun x : Pt 12 =>
      ∑ a : Fin 4, ∏ b ∈ (![sequenceSet i1, sequenceSet i2,
        sequenceSet i3, sequenceSet i4] a), x b := by
  have h : tripleFunction i1 i2 + tripleFunction i3 i4 =
      prodSeq i1 + prodSeq i2 + prodSeq i3 + prodSeq i4 := by
    funext x
    exact cancel_common_scalar (x16 x) (prodSeq i1 x) (prodSeq i2 x)
      (prodSeq i3 x) (prodSeq i4 x)
  rw [h, prodSeq_as_set i1, prodSeq_as_set i2, prodSeq_as_set i3, prodSeq_as_set i4]
  funext x
  simp [Fin.sum_univ_succ, add_assoc]

theorem literal_weight (i1 i2 i3 i4 : Fin 6 → Fin 12) (a1 a2 : ZMod 2) :
    hammingNorm (lwG i1 i2 i3 i4 a1 a2) =
      hammingNorm (tripleFunction i1 i2 + fun _ => a1) +
      hammingNorm (tripleFunction i3 i4) +
      hammingNorm (tripleFunction i1 i2 + tripleFunction i3 i4 + fun _ => a2) := by
  simpa only [lwG, tripleFunction, hammingNorm_zero, zero_add] using
    Paper6Cat4Weight.check_Cat4Weight 0
      (tripleFunction i1 i2 + fun _ => a1) (tripleFunction i3 i4)
      (tripleFunction i1 i2 + tripleFunction i3 i4 + fun _ => a2)

theorem weight_triangle (f g : BFun 12) :
    hammingNorm (f + g) ≤ hammingNorm f + hammingNorm g := by
  have h := Paper6HalfDecomposition.weight_add_with_intersection f g
  omega

theorem binary_double_cancel (f g : BFun 12) : f + (f + g) = g := by
  funext x
  have h : ∀ a b : ZMod 2, a + (a + b) = b := by decide
  exact h (f x) (g x)

theorem triangle_three (f g : BFun 12) :
    hammingNorm f ≤ hammingNorm g + hammingNorm (f + g) ∧
    hammingNorm g ≤ hammingNorm f + hammingNorm (f + g) ∧
    hammingNorm (f + g) ≤ hammingNorm f + hammingNorm g := by
  have hf := weight_triangle g (g + f)
  rw [binary_double_cancel, add_comm g f] at hf
  have hg := weight_triangle f (f + g)
  rw [binary_double_cancel] at hg
  exact ⟨hf, hg, weight_triangle f g⟩

/-- A nonzero cubic vanishing outside points where all three summands of g1 vanish. -/
noncomputable def zeroCylinder (i j : Fin 6 → Fin 12) :
    MvPolynomial (Fin 12) (ZMod 2) :=
  (1 + MvPolynomial.X 0) * (1 + MvPolynomial.X (i 0)) *
    (1 + MvPolynomial.X (j 0))

theorem zeroCylinder_degree (i j : Fin 6 → Fin 12) :
    (zeroCylinder i j).totalDegree ≤ 3 := by
  have hfactor (a : Fin 12) :
      ((1 : MvPolynomial (Fin 12) (ZMod 2)) + MvPolynomial.X a).totalDegree ≤ 1 := by
    simpa only [MvPolynomial.totalDegree_one, MvPolynomial.totalDegree_X,
      max_eq_right (by decide : (0 : ℕ) ≤ 1)] using
      (MvPolynomial.totalDegree_add (1 : MvPolynomial (Fin 12) (ZMod 2))
        (MvPolynomial.X a))
  have hpair :
      (((1 : MvPolynomial (Fin 12) (ZMod 2)) + MvPolynomial.X 0) *
        (1 + MvPolynomial.X (i 0))).totalDegree ≤ 2 :=
    (MvPolynomial.totalDegree_mul _ _).trans (Nat.add_le_add (hfactor 0) (hfactor (i 0)))
  exact (MvPolynomial.totalDegree_mul _ _).trans
    (Nat.add_le_add hpair (hfactor (j 0)))

theorem eval_zeroCylinder (i j : Fin 6 → Fin 12) (x : Pt 12) :
    evalFun (zeroCylinder i j) x = (1 + x 0) * (1 + x (i 0)) * (1 + x (j 0)) := by
  simp only [evalFun, zeroCylinder, MvPolynomial.eval_mul, MvPolynomial.eval_add,
    map_one, MvPolynomial.eval_X]

theorem zeroCylinder_nonzero (i j : Fin 6 → Fin 12) :
    evalFun (zeroCylinder i j) ≠ 0 := by
  intro hz
  have h := congrFun hz (0 : Pt 12)
  rw [eval_zeroCylinder] at h
  norm_num at h

theorem zeroCylinder_support (i j : Fin 6 → Fin 12) (x : Pt 12)
    (hx : evalFun (zeroCylinder i j) x ≠ 0) : tripleFunction i j x = 0 := by
  rw [eval_zeroCylinder] at hx
  have hbinary : ∀ a b c : ZMod 2,
      (1 + a) * (1 + b) * (1 + c) ≠ 0 → a = 0 ∧ b = 0 ∧ c = 0 := by decide
  obtain ⟨h0, hi, hj⟩ := hbinary (x 0) (x (i 0)) (x (j 0)) hx
  have hb : x16 x = 0 := by
    unfold x16
    exact Finset.prod_eq_zero (by decide : (0 : Fin 12) ∈ ({0, 1, 2, 3, 4, 5} : Finset (Fin 12))) h0
  have hpi : prodSeq i x = 0 := by
    unfold prodSeq
    exact Finset.prod_eq_zero (Finset.mem_univ (0 : Fin 6)) hi
  have hpj : prodSeq j x = 0 := by
    unfold prodSeq
    exact Finset.prod_eq_zero (Finset.mem_univ (0 : Fin 6)) hj
  simp only [tripleFunction, Pi.add_apply, hb, hpi, hpj, zero_add]

theorem weight_support_mono (f g : BFun 12)
    (h : ∀ x, f x ≠ 0 → g x ≠ 0) : hammingNorm f ≤ hammingNorm g := by
  classical
  unfold hammingNorm
  apply Finset.card_le_card
  intro x hx
  exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hx).1,
    h x (Finset.mem_filter.mp hx).2⟩

/-- All choices of repeated indices are covered; coincident zero constraints only help. -/
theorem triple_complement_lower (i j : Fin 6 → Fin 12) :
    512 ≤ hammingNorm (tripleFunction i j + 1) := by
  have hlower : 512 ≤ hammingNorm (evalFun (zeroCylinder i j)) := by
    have h := Paper6MinDistance.nonzero_weight_lower_bound 12 3 (by decide)
      (evalFun (zeroCylinder i j))
      ⟨zeroCylinder i j, zeroCylinder_degree i j, rfl⟩ (zeroCylinder_nonzero i j)
    simpa using h
  apply hlower.trans
  apply weight_support_mono
  intro x hx
  have hz := zeroCylinder_support i j x hx
  change tripleFunction i j x + 1 ≠ 0
  rw [hz, zero_add]
  exact one_ne_zero

end Paper6LiteralLouWang

#print axioms Paper6LiteralLouWang.sequenceSet
#print axioms Paper6LiteralLouWang.sequenceSet_card
#print axioms Paper6LiteralLouWang.prodSeq_as_set
#print axioms Paper6LiteralLouWang.tripleFunction
#print axioms Paper6LiteralLouWang.triple_as_sum
#print axioms Paper6LiteralLouWang.cancel_common_scalar
#print axioms Paper6LiteralLouWang.triples_sum_as_four
#print axioms Paper6LiteralLouWang.literal_weight
#print axioms Paper6LiteralLouWang.weight_triangle
#print axioms Paper6LiteralLouWang.binary_double_cancel
#print axioms Paper6LiteralLouWang.triangle_three
#print axioms Paper6LiteralLouWang.zeroCylinder
#print axioms Paper6LiteralLouWang.zeroCylinder_degree
#print axioms Paper6LiteralLouWang.eval_zeroCylinder
#print axioms Paper6LiteralLouWang.zeroCylinder_nonzero
#print axioms Paper6LiteralLouWang.zeroCylinder_support
#print axioms Paper6LiteralLouWang.weight_support_mono
#print axioms Paper6LiteralLouWang.triple_complement_lower
