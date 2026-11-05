import Research.Backfill.Paper7.ChallengeV3

/-!
# Paper 7: sound modular rejection from a true integer factorization

Source-only author candidate. Linear factors are stored in the actual list
used by the frozen contract. Induction on that list counts repeated roots
with their multiplicities; injectivity is required only on the supplied
finite set. The empty list gives the polynomial `1` and root sum zero.
-/

set_option autoImplicit false

open Polynomial Finset
open BackfillPaper7.Challenge.Legacy.Algebra

namespace BackfillPaper7.PolynomialRejectProof

noncomputable def linearProduct {R : Type*} [CommRing R] (a : List R) : Polynomial R :=
  (a.map (fun z => X - C z)).prod

theorem linearProduct_monic {R : Type*} [CommRing R] (a : List R) :
    (linearProduct a).Monic := by
  induction a with
  | nil => exact Polynomial.monic_one
  | cons z a ih => exact (Polynomial.monic_X_sub_C z).mul ih

theorem linearProduct_natDegree {R : Type*} [CommRing R] [Nontrivial R] (a : List R) :
    (linearProduct a).natDegree = a.length := by
  induction a with
  | nil => simp [linearProduct]
  | cons z a ih =>
    change ((X - C z) * linearProduct a).natDegree = a.length + 1
    rw [(Polynomial.monic_X_sub_C z).natDegree_mul (linearProduct_monic a),
      Polynomial.natDegree_X_sub_C, ih]
    omega

theorem linearProduct_map {R T : Type*} [CommRing R] [CommRing T]
    (c : R →+* T) (a : List R) :
    (linearProduct a).map c = linearProduct (a.map c) := by
  induction a with
  | nil => simp [linearProduct]
  | cons z a ih =>
    change ((X - C z) * linearProduct a).map c =
      (X - C (c z)) * linearProduct (a.map c)
    rw [Polynomial.map_mul, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, ih]

theorem linearProduct_root_sum {K : Type*} [Field K]
    (S : Finset ℤ) (c : ℤ → K) (hinj : Set.InjOn c (S : Set ℤ)) (a : List ℤ) :
    (∀ z ∈ a, z ∈ S) →
      (∑ z ∈ S, Polynomial.rootMultiplicity (c z) (linearProduct (a.map c))) = a.length := by
  classical
  induction a with
  | nil =>
    intro _
    change (∑ z ∈ S, Polynomial.rootMultiplicity (c z) (1 : Polynomial K)) = 0
    apply Finset.sum_eq_zero
    intro z _
    simpa only [Polynomial.C_1] using Polynomial.rootMultiplicity_C (1 : K) (c z)
  | cons x a ih =>
    intro hall
    have hx : x ∈ S := hall x List.mem_cons_self
    have ha : ∀ z ∈ a, z ∈ S := fun z hz => hall z (List.mem_cons_of_mem x hz)
    have hnonzero : (X - C (c x)) * linearProduct (a.map c) ≠ 0 :=
      ((Polynomial.monic_X_sub_C (c x)).mul (linearProduct_monic (a.map c))).ne_zero
    have hdelta : (∑ z ∈ S, if c z = c x then (1 : ℕ) else 0) = 1 := by
      calc
        (∑ z ∈ S, if c z = c x then (1 : ℕ) else 0) =
            ∑ z ∈ S, if z = x then (1 : ℕ) else 0 := by
          apply Finset.sum_congr rfl
          intro z hz
          have heq : c z = c x ↔ z = x :=
            ⟨fun h => hinj hz hx h, fun h => congrArg c h⟩
          simp only [heq]
        _ = 1 := by simp [hx]
    change (∑ z ∈ S, Polynomial.rootMultiplicity (c z)
      ((X - C (c x)) * linearProduct (a.map c))) = a.length + 1
    simp_rw [Polynomial.rootMultiplicity_mul hnonzero, Polynomial.rootMultiplicity_X_sub_C]
    rw [Finset.sum_add_distrib, hdelta, ih ha]
    omega

end BackfillPaper7.PolynomialRejectProof

theorem check_ModularPolynomialRejectSound :
    BackfillPaper7.Challenge.Legacy.Algebra.ModularPolynomialRejectSound := by
  classical
  intro ℓ hℓ f S hf hinj
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have hmonic : (reducePolynomial ℓ f).Monic :=
    Polynomial.Monic.map (Int.castRingHom (ZMod ℓ)) hf
  have hdegree : (reducePolynomial ℓ f).natDegree = f.natDegree :=
    hf.natDegree_map (Int.castRingHom (ZMod ℓ))
  have hroot : ∀ z : ℤ, Polynomial.rootMultiplicity z f ≤
      Polynomial.rootMultiplicity (z : ZMod ℓ) (reducePolynomial ℓ f) := by
    intro z
    exact Polynomial.le_rootMultiplicity_map hmonic.ne_zero z
  have hfactor : IntegerFactorizationOn f S → modularRootSum ℓ S f = f.natDegree := by
    rintro ⟨a, ha, hfa⟩
    have hfa' : f = BackfillPaper7.PolynomialRejectProof.linearProduct a := hfa
    rw [hfa']
    unfold modularRootSum reducePolynomial
    rw [BackfillPaper7.PolynomialRejectProof.linearProduct_map]
    change (∑ z ∈ S, Polynomial.rootMultiplicity (z : ZMod ℓ)
      (BackfillPaper7.PolynomialRejectProof.linearProduct
        (a.map (fun z : ℤ => (z : ZMod ℓ))))) =
      (BackfillPaper7.PolynomialRejectProof.linearProduct a).natDegree
    rw [BackfillPaper7.PolynomialRejectProof.linearProduct_natDegree]
    exact BackfillPaper7.PolynomialRejectProof.linearProduct_root_sum S
      (fun z : ℤ => (z : ZMod ℓ)) hinj a ha
  refine ⟨hmonic, hdegree, hroot, hfactor, ?_⟩
  intro hlt hfac
  exact (ne_of_lt hlt) (hfactor hfac)

#print axioms BackfillPaper7.PolynomialRejectProof.linearProduct
#print axioms BackfillPaper7.PolynomialRejectProof.linearProduct_monic
#print axioms BackfillPaper7.PolynomialRejectProof.linearProduct_natDegree
#print axioms BackfillPaper7.PolynomialRejectProof.linearProduct_map
#print axioms BackfillPaper7.PolynomialRejectProof.linearProduct_root_sum
#print axioms check_ModularPolynomialRejectSound
