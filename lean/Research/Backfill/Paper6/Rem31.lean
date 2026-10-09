import Research.Backfill.Paper6.ChallengeV3
import Research.Backfill.Paper6.InclusionExclusion

/-!
# Paper 6 V3: all three parts of the direct-sum remark

Every binary function on m variables is interpolated by a genuine multivariable
polynomial of degree at most m, using Mathlib's point indicators. Two arbitrary
seven-variable functions therefore give a degree-at-most-seven polynomial on
two disjoint coordinate blocks. The character sum factors over the product of
the two blocks, yielding the exact integer weight formula. Finite subsets of
any cardinality from zero to 128 supply the requested functions, and hence the
entire integer interval of weights in the frozen final conjunct.

Frozen manifest SHA-256:
bd2a50001623f163ad304a88b2ae484434924c97820e9373f8a83517c1d59f61.
Candidate source only; compilation and acceptance are root-controlled.
-/

set_option autoImplicit false

namespace Paper6DirectSums

open BackfillPaper6.V3
open Paper6InclusionExclusion

/-- A binary point indicator has total degree at most the number of coordinates. -/
theorem indicator_degree_le {m : ℕ} (a : Pt m) :
    (MvPolynomial.indicator a).totalDegree ≤ m := by
  classical
  have hfactor (i : Fin m) :
      ((1 : MvPolynomial (Fin m) (ZMod 2)) -
        (MvPolynomial.X i - MvPolynomial.C (a i))).totalDegree ≤ 1 := by
    have hsub : (MvPolynomial.X i - MvPolynomial.C (a i)).totalDegree ≤ 1 :=
      (MvPolynomial.totalDegree_sub_C_le _ _).trans_eq (MvPolynomial.totalDegree_X i)
    exact (MvPolynomial.totalDegree_sub _ _).trans (max_le (by simp) hsub)
  have hprod :
      (∏ i : Fin m, ((1 : MvPolynomial (Fin m) (ZMod 2)) -
        (MvPolynomial.X i - MvPolynomial.C (a i)))).totalDegree ≤ m := by
    calc
      (∏ i : Fin m, ((1 : MvPolynomial (Fin m) (ZMod 2)) -
          (MvPolynomial.X i - MvPolynomial.C (a i)))).totalDegree ≤ ∑ i : Fin m,
          ((1 : MvPolynomial (Fin m) (ZMod 2)) -
            (MvPolynomial.X i - MvPolynomial.C (a i))).totalDegree :=
        MvPolynomial.totalDegree_finsetProd Finset.univ
          (fun i : Fin m => (1 : MvPolynomial (Fin m) (ZMod 2)) -
            (MvPolynomial.X i - MvPolynomial.C (a i)))
      _ ≤ ∑ _i : Fin m, (1 : ℕ) :=
        Finset.sum_le_sum
          (f := fun i : Fin m => ((1 : MvPolynomial (Fin m) (ZMod 2)) -
            (MvPolynomial.X i - MvPolynomial.C (a i))).totalDegree)
          (fun i _hi => hfactor i)
      _ = m := by simp
  have hind : MvPolynomial.indicator a =
      ∏ i : Fin m, ((1 : MvPolynomial (Fin m) (ZMod 2)) -
        (MvPolynomial.X i - MvPolynomial.C (a i))) := by
    unfold MvPolynomial.indicator
    rw [ZMod.card]
    simp only [show (2 : ℕ) - 1 = 1 from by decide, pow_one]
  rw [hind]
  exact hprod

/-- Explicit interpolation by a finite sum of point indicator polynomials. -/
noncomputable def interpolation {m : ℕ} (f : BFun m) : MvPolynomial (Fin m) (ZMod 2) :=
  ∑ a : Pt m, f a • MvPolynomial.indicator a

/-- Interpolation preserves the ambient degree bound. -/
theorem interpolation_degree_le {m : ℕ} (f : BFun m) :
    (interpolation f).totalDegree ≤ m := by
  classical
  unfold interpolation
  apply MvPolynomial.totalDegree_finsetSum_le
  intro a _ha
  exact (MvPolynomial.totalDegree_smul_le (f a) (MvPolynomial.indicator a)).trans
    (indicator_degree_le a)

/-- Evaluation of the explicit interpolation is the original arbitrary function. -/
theorem evalFun_interpolation {m : ℕ} (f : BFun m) : evalFun (interpolation f) = f := by
  classical
  funext y
  change MvPolynomial.eval y (∑ a : Pt m, f a • MvPolynomial.indicator a) = f y
  calc
    _ = ∑ a : Pt m, f a * MvPolynomial.eval y (MvPolynomial.indicator a) := by
      simp only [map_sum, MvPolynomial.smul_eval]
    _ = f y * MvPolynomial.eval y (MvPolynomial.indicator y) := by
      apply Finset.sum_eq_single y
      · intro b _hb hby
        rw [MvPolynomial.eval_indicator_apply_eq_zero y b (Ne.symm hby), mul_zero]
      · intro hy
        exact (hy (Finset.mem_univ y)).elim
    _ = f y := by rw [MvPolynomial.eval_indicator_apply_eq_one, mul_one]

/-- Every binary function is represented by a polynomial of degree at most its number of variables. -/
theorem every_function_mem_RM (m : ℕ) (f : BFun m) : f ∈ RM m m :=
  ⟨interpolation f, interpolation_degree_le f, (evalFun_interpolation f).symm⟩

/-- A polynomial on two disjoint blocks of seven variables. -/
noncomputable def directPolynomial
    (p q : MvPolynomial (Fin 7) (ZMod 2)) : MvPolynomial (Fin 14) (ZMod 2) :=
  MvPolynomial.rename (Fin.castAdd 7) p + MvPolynomial.rename (Fin.natAdd 7) q

/-- Variable renaming and addition keep the degree bound seven. -/
theorem directPolynomial_degree_le (p q : MvPolynomial (Fin 7) (ZMod 2))
    (hp : p.totalDegree ≤ 7) (hq : q.totalDegree ≤ 7) :
    (directPolynomial p q).totalDegree ≤ 7 := by
  have hp' := (MvPolynomial.totalDegree_rename_le (Fin.castAdd 7) p).trans hp
  have hq' := (MvPolynomial.totalDegree_rename_le (Fin.natAdd 7) q).trans hq
  exact (MvPolynomial.totalDegree_add _ _).trans (max_le hp' hq')

/-- The constructed polynomial evaluates to the exact frozen direct-sum function. -/
theorem evalFun_directPolynomial (p q : MvPolynomial (Fin 7) (ZMod 2)) :
    evalFun (directPolynomial p q) = dsum (evalFun p) (evalFun q) := by
  funext y
  change MvPolynomial.eval y
      (MvPolynomial.rename (Fin.castAdd 7) p + MvPolynomial.rename (Fin.natAdd 7) q) =
    MvPolynomial.eval (fun i => y (Fin.castAdd 7 i)) p +
      MvPolynomial.eval (fun i => y (Fin.natAdd 7 i)) q
  rw [MvPolynomial.eval_add, MvPolynomial.eval_rename, MvPolynomial.eval_rename]
  rfl

/-- Code membership holds for arbitrary seven-variable functions, with no assumptions on A or B. -/
theorem dsum_mem_RM (A B : BFun 7) : dsum A B ∈ RM 7 14 := by
  obtain ⟨p, hp, hA⟩ := every_function_mem_RM 7 A
  obtain ⟨q, hq, hB⟩ := every_function_mem_RM 7 B
  refine ⟨directPolynomial p q, directPolynomial_degree_le p q hp hq, ?_⟩
  rw [hA, hB]
  exact (evalFun_directPolynomial p q).symm

/-- Appending two seven-coordinate points realizes the two frozen coordinate blocks. -/
theorem dsum_append (A B : BFun 7) (x y : Pt 7) :
    dsum A B (Fin.append x y) = A x + B y := by
  simp only [dsum, Fin.append_left, Fin.append_right]

/-- The integer character sum determines the Hamming weight. -/
theorem sum_character (m : ℕ) (f : BFun m) :
    (∑ x : Pt m, character (f x)) = (2 : ℤ) ^ m - 2 * (hammingNorm f : ℤ) := by
  classical
  have hconst : (∑ _x : Pt m, (1 : ℤ)) = (2 : ℤ) ^ m := by simp [Pt]
  calc
    (∑ x : Pt m, character (f x)) =
        (∑ _x : Pt m, (1 : ℤ)) + (-2) * ∑ x : Pt m, bit (f x) := by
      simp only [character, Finset.sum_add_distrib, Finset.mul_sum]
    _ = (2 : ℤ) ^ m - 2 * (hammingNorm f : ℤ) := by
      rw [hconst, ← weight_as_sum f]
      ring

-- Development 01 reached the constructor-name linter's recursion limit on this
-- theorem. Raise only its traversal depth; all linters and kernel checks stay enabled.
set_option maxRecDepth 4096 in
/-- The character sum factors across the two independent coordinate blocks. -/
theorem character_dsum_product (A B : BFun 7) :
    (∑ y : Pt 14, character (dsum A B y)) =
      (∑ x : Pt 7, character (A x)) * (∑ y : Pt 7, character (B y)) := by
  classical
  calc
    (∑ y : Pt 14, character (dsum A B y)) =
        ∑ z : Pt 7 × Pt 7, character (dsum A B (Fin.append z.1 z.2)) :=
      ((Fin.appendEquiv (α := ZMod 2) 7 7).sum_comp
        (fun y : Pt 14 => character (dsum A B y))).symm
    _ = ∑ z : Pt 7 × Pt 7, character (A z.1) * character (B z.2) := by
      apply Finset.sum_congr rfl
      intro z _hz
      rw [dsum_append, character_add]
    _ = _ := by
      rw [Fintype.sum_prod_type]
      change (∑ x : Pt 7, ∑ y : Pt 7, character (A x) * character (B y)) =
        (∑ x : Pt 7, character (A x)) * (∑ y : Pt 7, character (B y))
      exact (Fintype.sum_mul_sum (fun x : Pt 7 => character (A x))
        (fun y : Pt 7 => character (B y))).symm

/-- The exact integer weight formula from Remark 3.1. -/
theorem dsum_weight (A B : BFun 7) :
    (hammingNorm (dsum A B) : ℤ) =
      8192 - 2 * (64 - (hammingNorm A : ℤ)) * (64 - (hammingNorm B : ℤ)) := by
  have hproduct := character_dsum_product A B
  rw [sum_character 14 (dsum A B), sum_character 7 A, sum_character 7 B] at hproduct
  norm_num at hproduct
  nlinarith [hproduct]

/-- The seven-dimensional binary domain has exactly 128 points. -/
theorem card_points_seven : Fintype.card (Pt 7) = 128 := by
  norm_num [Pt]

/-- Every cardinality up to 128 is the weight of some actual seven-variable binary function. -/
theorem every_weight_seven (a : ℕ) (ha : a ≤ 128) :
    ∃ A : BFun 7, hammingNorm A = a := by
  classical
  have hbound : a ≤ (Finset.univ : Finset (Pt 7)).card := by
    rw [Finset.card_univ, card_points_seven]
    exact ha
  obtain ⟨s, _hs, hcard⟩ := Finset.exists_subset_card_eq hbound
  refine ⟨fun x => if x ∈ s then 1 else 0, ?_⟩
  change (Finset.univ.filter
    (fun x : Pt 7 => (if x ∈ s then (1 : ZMod 2) else 0) ≠ 0)).card = a
  have hfilter : Finset.univ.filter
      (fun x : Pt 7 => (if x ∈ s then (1 : ZMod 2) else 0) ≠ 0) = s := by
    ext x
    by_cases hx : x ∈ s <;> simp [hx]
  rw [hfilter, hcard]

/-- Every integer parameter in the entire requested interval produces the requested RM weight. -/
theorem interval_weights (n : ℤ) (hn : |n| ≤ 64) :
    IsWeight 7 14 (8192 - 2 * n).toNat := by
  have hn' := abs_le.mp hn
  have ha0 : 0 ≤ 64 - n := by omega
  have ha_cast : ((64 - n).toNat : ℤ) = 64 - n := Int.toNat_of_nonneg ha0
  have ha : (64 - n).toNat ≤ 128 := by omega
  obtain ⟨A, hA⟩ := every_weight_seven (64 - n).toNat ha
  obtain ⟨B, hB⟩ := every_weight_seven 63 (by decide)
  have hcastA : (hammingNorm A : ℤ) = 64 - n := by
    rw [hA]
    exact ha_cast
  have hcastB : (hammingNorm B : ℤ) = 63 := by exact_mod_cast hB
  have hweight : (hammingNorm (dsum A B) : ℤ) = 8192 - 2 * n := by
    rw [dsum_weight, hcastA, hcastB]
    ring
  refine ⟨dsum A B, dsum_mem_RM A B, ?_⟩
  simpa only [Int.toNat_natCast] using congrArg Int.toNat hweight

/-- All three conjuncts of the exact unchanged frozen remark. -/
theorem rem31 : BackfillPaper6.V3.Rem31 :=
  ⟨fun A B => ⟨dsum_mem_RM A B, dsum_weight A B⟩, every_weight_seven, interval_weights⟩

/-- Exact contract check; this alias is not an additional result. -/
theorem check_Rem31 : BackfillPaper6.V3.Rem31 := rem31

end Paper6DirectSums

#print axioms Paper6DirectSums.indicator_degree_le
#print axioms Paper6DirectSums.interpolation_degree_le
#print axioms Paper6DirectSums.evalFun_interpolation
#print axioms Paper6DirectSums.every_function_mem_RM
#print axioms Paper6DirectSums.directPolynomial_degree_le
#print axioms Paper6DirectSums.evalFun_directPolynomial
#print axioms Paper6DirectSums.dsum_mem_RM
#print axioms Paper6DirectSums.dsum_append
#print axioms Paper6DirectSums.sum_character
#print axioms Paper6DirectSums.character_dsum_product
#print axioms Paper6DirectSums.dsum_weight
#print axioms Paper6DirectSums.card_points_seven
#print axioms Paper6DirectSums.every_weight_seven
#print axioms Paper6DirectSums.interval_weights
#print axioms Paper6DirectSums.rem31
#print axioms Paper6DirectSums.check_Rem31
#print Paper6DirectSums.check_Rem31
