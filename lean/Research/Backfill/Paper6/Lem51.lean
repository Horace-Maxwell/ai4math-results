import Research.Backfill.Paper6.AffineInvariance
import Research.Backfill.Paper6.Lem22
import Research.Backfill.Paper6.P2

/-!
# Directional support pairs and the complete Lemma 5.1

Source candidate only, not compiled or independently reviewed. The final theorem
uses the exact frozen three-clause type, including every prescribed linear
equivalence carrying the last unit vector to the given direction.
-/

set_option autoImplicit false

namespace Paper6PairDecomposition

open Finset
open BackfillPaper6.V3

abbrev lastVector : Pt 14 := Pi.single (Fin.last 13) 1

noncomputable def numerator (f : BFun 14) (a : Pt 14) : ℕ :=
  (Function.support f ∩ {x | x + a ∈ Function.support f}).ncard

def pairProduct (f : BFun 14) (a : Pt 14) : BFun 14 := fun x => f x * f (x + a)

noncomputable def supportFinset (f : BFun 14) : Finset (Pt 14) :=
  Finset.univ.filter fun x => f x ≠ 0

theorem lastVector_ne_zero : lastVector ≠ 0 := by
  intro h
  have hbad : (1 : ZMod 2) = 0 := by
    simpa [lastVector] using congrFun h (Fin.last 13)
  exact one_ne_zero hbad

/-- An isomorphism of the two one-dimensional spans extends to the whole space. -/
theorem exists_direction_equiv (a : Pt 14) (ha : a ≠ 0) :
    ∃ φ : Pt 14 ≃ₗ[ZMod 2] Pt 14, φ lastVector = a := by
  let e0 := LinearEquiv.toSpanNonzeroSingleton (ZMod 2) (Pt 14) lastVector lastVector_ne_zero
  let ea := LinearEquiv.toSpanNonzeroSingleton (ZMod 2) (Pt 14) a ha
  obtain ⟨φ, hφ⟩ := Submodule.exists_linearEquiv_restrict_eq (e0.symm.trans ea)
  refine ⟨φ, ?_⟩
  have h : (ea 1 : Pt 14) = φ (e0 1) := by
    simpa only [LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply] using hφ (e0 1)
  simpa [e0, ea] using h.symm

theorem snoc_add_last (x : Pt 13) (t : ZMod 2) :
    Fin.snoc (α := fun _ => ZMod 2) x t + lastVector =
      Fin.snoc (α := fun _ => ZMod 2) x (t + 1) := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [Pi.add_apply, lastVector, Fin.snoc_last, Pi.single_eq_same]
  · simp only [Pi.add_apply, lastVector, Fin.snoc_castSucc,
      Pi.single_eq_of_ne (Fin.castSucc_ne_last j), add_zero]

theorem weight_product {ι : Type*} [Fintype ι] (g h : ι → ZMod 2) :
    hammingNorm (fun x => g x * h x) =
      (Function.support g ∩ Function.support h).ncard := by
  classical
  rw [Paper6HalfDecomposition.support_inter_ncard_eq_count]
  unfold hammingNorm
  congr 1
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, mul_ne_zero_iff]

theorem numerator_eq_weight (f : BFun 14) (a : Pt 14) :
    numerator f a = hammingNorm (pairProduct f a) := by
  exact (weight_product f (fun x => f (x + a))).symm

/-- Both slices of the last-direction product are the common support of the two original slices. -/
theorem weight_last_product (F : BFun 14) :
    hammingNorm (pairProduct F lastVector) =
      2 * (Function.support (half0 F) ∩ Function.support (half1 F)).ncard := by
  have h0 : half0 (pairProduct F lastVector) = fun x => half0 F x * half1 F x := by
    funext x
    change F (Fin.snoc x 0) * F (Fin.snoc x 0 + lastVector) = _
    rw [snoc_add_last]
    rfl
  have h1 : half1 (pairProduct F lastVector) = fun x => half0 F x * half1 F x := by
    funext x
    change F (Fin.snoc x 1) * F (Fin.snoc x 1 + lastVector) = _
    rw [snoc_add_last, show (1 + 1 : ZMod 2) = 0 by decide]
    exact mul_comm _ _
  rw [Paper6HalfDecomposition.weight_slices 13, h0, h1]
  simp only [weight_product]
  omega

/-- This identity is proved for the given φ, not merely for some choice of coordinates. -/
theorem numerator_in_coordinates (f : BFun 14) (a : Pt 14)
    (φ : Pt 14 ≃ₗ[ZMod 2] Pt 14) (hφ : φ lastVector = a) :
    numerator f a = 2 *
      (Function.support (half0 (fun y => f (φ y))) ∩
        Function.support (half1 (fun y => f (φ y)))).ncard := by
  have hconjugate : (fun y => pairProduct f a (φ y)) =
      pairProduct (fun y => f (φ y)) lastVector := by
    funext y
    change f (φ y) * f (φ y + a) = f (φ y) * f (φ (y + lastVector))
    rw [map_add, hφ]
  calc
    numerator f a = hammingNorm (pairProduct f a) := numerator_eq_weight f a
    _ = hammingNorm (fun y => pairProduct f a (φ y)) :=
      (Paper6AffineInvariance.weight_precomposition φ.toAffineEquiv (pairProduct f a)).symm
    _ = hammingNorm (pairProduct (fun y => f (φ y)) lastVector) :=
      congrArg hammingNorm hconjugate
    _ = _ := weight_last_product (fun y => f (φ y))

theorem pairCount_in_coordinates (f : BFun 14) (a : Pt 14)
    (φ : Pt 14 ≃ₗ[ZMod 2] Pt 14) (hφ : φ lastVector = a) :
    pairCount f a =
      (Function.support (half0 (fun y => f (φ y))) ∩
        Function.support (half1 (fun y => f (φ y)))).ncard := by
  change numerator f a / 2 = _
  rw [numerator_in_coordinates f a φ hφ]
  omega

theorem numerator_twice_pairCount (f : BFun 14) (a : Pt 14) (ha : a ≠ 0) :
    numerator f a = 2 * pairCount f a := by
  obtain ⟨φ, hφ⟩ := exists_direction_equiv a ha
  rw [numerator_in_coordinates f a φ hφ, pairCount_in_coordinates f a φ hφ]

theorem numerator_eq_count (f : BFun 14) (a : Pt 14) :
    numerator f a = (Finset.univ.filter (fun x => f x ≠ 0 ∧ f (x + a) ≠ 0)).card :=
  Paper6HalfDecomposition.support_inter_ncard_eq_count f (fun x => f (x + a))

theorem numerator_zero (f : BFun 14) : numerator f 0 = hammingNorm f := by
  rw [numerator_eq_count]
  simp only [add_zero, and_self, hammingNorm]

theorem numerator_eq_sum (f : BFun 14) (a : Pt 14) :
    numerator f a = ∑ x ∈ supportFinset f, if f (x + a) ≠ 0 then 1 else 0 := by
  classical
  rw [numerator_eq_count]
  have hfilter : Finset.univ.filter (fun x => f x ≠ 0 ∧ f (x + a) ≠ 0) =
      (supportFinset f).filter (fun x => f (x + a) ≠ 0) := by
    ext x
    simp [supportFinset]
  rw [hfilter, Finset.card_filter]

theorem translated_count (f : BFun 14) (x : Pt 14) :
    (∑ a : Pt 14, if f (x + a) ≠ 0 then (1 : ℕ) else 0) = hammingNorm f := by
  classical
  rw [Finset.sum_boole]
  unfold hammingNorm
  apply Finset.card_equiv (Equiv.addLeft x)
  intro a
  simp

/-- Counting ordered pairs by their sum gives the square of the support size. -/
theorem sum_numerator (f : BFun 14) :
    (∑ a : Pt 14, numerator f a) = hammingNorm f * hammingNorm f := by
  classical
  calc
    (∑ a : Pt 14, numerator f a) =
        ∑ a : Pt 14, ∑ x ∈ supportFinset f, if f (x + a) ≠ 0 then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro a _ha
      exact numerator_eq_sum f a
    _ = ∑ x ∈ supportFinset f, ∑ a : Pt 14, if f (x + a) ≠ 0 then 1 else 0 :=
      Finset.sum_comm
    _ = ∑ _x ∈ supportFinset f, hammingNorm f := by
      apply Finset.sum_congr rfl
      intro x _hx
      exact translated_count f x
    _ = hammingNorm f * hammingNorm f := Finset.sum_const_nat (fun _ _ => rfl)

theorem sum_nonzero_numerator (f : BFun 14) :
    (∑ a ∈ Finset.univ.erase (0 : Pt 14), numerator f a) =
      hammingNorm f * (hammingNorm f - 1) := by
  classical
  have hsum := Finset.add_sum_erase (Finset.univ : Finset (Pt 14))
    (numerator f) (a := 0) (Finset.mem_univ _)
  rw [numerator_zero, sum_numerator] at hsum
  rw [Nat.mul_sub_left_distrib, Nat.mul_one]
  omega

/-- Every unordered pair has exactly two ordered presentations in its unique nonzero direction. -/
theorem sum_pairCount (f : BFun 14) :
    (∑ a ∈ Finset.univ.erase (0 : Pt 14), pairCount f a) = (hammingNorm f).choose 2 := by
  classical
  have htwice :
      2 * (∑ a ∈ Finset.univ.erase (0 : Pt 14), pairCount f a) =
        hammingNorm f * (hammingNorm f - 1) := by
    rw [Finset.mul_sum]
    calc
      (∑ a ∈ Finset.univ.erase (0 : Pt 14), 2 * pairCount f a) =
          ∑ a ∈ Finset.univ.erase (0 : Pt 14), numerator f a := by
        apply Finset.sum_congr rfl
        intro a ha
        exact (numerator_twice_pairCount f a (Finset.mem_erase.mp ha).1).symm
      _ = _ := sum_nonzero_numerator f
  rw [Nat.choose_two_right]
  calc
    (∑ a ∈ Finset.univ.erase (0 : Pt 14), pairCount f a) =
        (2 * (∑ a ∈ Finset.univ.erase (0 : Pt 14), pairCount f a)) / 2 := by omega
    _ = _ := congrArg (fun n : ℕ => n / 2) htwice

/-- Actual code-membership, reconstruction, support difference, and weight for every given φ. -/
theorem decomposition_for_equiv (f : BFun 14) (hf : f ∈ RM 7 14)
    (a : Pt 14) (φ : Pt 14 ≃ₗ[ZMod 2] Pt 14) (hφ : φ lastVector = a) :
    ∃ g ∈ RM 7 13, ∃ h ∈ RM 6 13,
      (∀ y : Pt 14, f (φ y) = g (Fin.init y) + y (Fin.last 13) * h (Fin.init y)) ∧
      pairCount f a = (Function.support g \ Function.support h).ncard ∧
      hammingNorm h + 2 * pairCount f a = hammingNorm f := by
  let F : BFun 14 := fun y => f (φ y)
  have hF : F ∈ RM 7 14 := Paper6AffineInvariance.rm_precomposition φ.toAffineEquiv f hf
  have hslices := Paper6HalfDecomposition.rm_slices_of_mem 13 6 F hF
  have hwF : hammingNorm F = hammingNorm f :=
    Paper6AffineInvariance.weight_precomposition φ.toAffineEquiv f
  have hpairs : pairCount f a =
      (Function.support (half0 F) ∩ Function.support (half1 F)).ncard :=
    pairCount_in_coordinates f a φ hφ
  refine ⟨half0 F, hslices.1, half0 F + half1 F, hslices.2, ?_, ?_, ?_⟩
  · exact Paper6HalfDecomposition.reconstruct 13 F
  · rw [hpairs, Paper6HalfDecomposition.support_inter_eq_sdiff]
  · have hw := (Paper6HalfDecomposition.weight_slices 13 F).trans
      (Paper6HalfDecomposition.weight_add_with_intersection (half0 F) (half1 F))
    rw [← hpairs, hwF] at hw
    exact hw.symm

theorem pairCount_odd (f : BFun 14) (hf : f ∈ RM 7 14)
    (hw : hammingNorm f % 4 = 2) (a : Pt 14) (ha : a ≠ 0) : Odd (pairCount f a) := by
  obtain ⟨φ, hφ⟩ := exists_direction_equiv a ha
  obtain ⟨_g, _hg, h, hh, _hreconstruct, _hpairs, hweight⟩ :=
    decomposition_for_equiv f hf a φ hφ
  obtain ⟨t, ht⟩ := Paper6Divisibility.rm613_four_dvd h hh
  refine ⟨pairCount f a / 2, ?_⟩
  omega

/-- All three clauses of the unchanged frozen Lemma 5.1. -/
theorem check_Lem51 : BackfillPaper6.V3.Lem51 := by
  intro f hf hw
  refine ⟨sum_pairCount f, pairCount_odd f hf hw, ?_⟩
  intro a _ha φ hφ
  exact decomposition_for_equiv f hf a φ hφ

end Paper6PairDecomposition

#print axioms Paper6PairDecomposition.lastVector
#print axioms Paper6PairDecomposition.numerator
#print axioms Paper6PairDecomposition.pairProduct
#print axioms Paper6PairDecomposition.supportFinset
#print axioms Paper6PairDecomposition.lastVector_ne_zero
#print axioms Paper6PairDecomposition.exists_direction_equiv
#print axioms Paper6PairDecomposition.snoc_add_last
#print axioms Paper6PairDecomposition.weight_product
#print axioms Paper6PairDecomposition.numerator_eq_weight
#print axioms Paper6PairDecomposition.weight_last_product
#print axioms Paper6PairDecomposition.numerator_in_coordinates
#print axioms Paper6PairDecomposition.pairCount_in_coordinates
#print axioms Paper6PairDecomposition.numerator_twice_pairCount
#print axioms Paper6PairDecomposition.numerator_eq_count
#print axioms Paper6PairDecomposition.numerator_zero
#print axioms Paper6PairDecomposition.numerator_eq_sum
#print axioms Paper6PairDecomposition.translated_count
#print axioms Paper6PairDecomposition.sum_numerator
#print axioms Paper6PairDecomposition.sum_nonzero_numerator
#print axioms Paper6PairDecomposition.sum_pairCount
#print axioms Paper6PairDecomposition.decomposition_for_equiv
#print axioms Paper6PairDecomposition.pairCount_odd
#print axioms Paper6PairDecomposition.check_Lem51
