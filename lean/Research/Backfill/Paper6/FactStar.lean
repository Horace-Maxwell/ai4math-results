import Research.Backfill.Paper6.FlatBasics
import Research.Backfill.Paper6.P1

/-!
# Quadratic support on an arbitrary affine flat

Complete source candidate for the unchanged V3.FactStar. Not compiled or reviewed.
The affine intersection may be empty. A nonempty flat is parametrized by its
direction basis. Polynomial substitution between different dimensions is proved
here without adding assumptions to the frozen target.
-/

set_option autoImplicit false

namespace Paper6FactStar

open Finset
open BackfillPaper6.V3

/-- The monomial bound allows different source and destination dimensions. -/
theorem substituted_monomial_degree_le {m n : ℕ}
    (g : Fin m → MvPolynomial (Fin n) (ZMod 2))
    (hg : ∀ i, (g i).totalDegree ≤ 1) (d : Fin m →₀ ℕ) (a : ZMod 2) :
    (MvPolynomial.eval₂ MvPolynomial.C g (MvPolynomial.monomial d a)).totalDegree ≤
      d.sum (fun _ e => e) := by
  classical
  rw [MvPolynomial.eval₂_monomial]
  change (MvPolynomial.C a * ∏ j ∈ d.support, g j ^ d j).totalDegree ≤
    ∑ j ∈ d.support, d j
  calc
    (MvPolynomial.C a * ∏ j ∈ d.support, g j ^ d j).totalDegree ≤
        (MvPolynomial.C a : MvPolynomial (Fin n) (ZMod 2)).totalDegree +
          (∏ j ∈ d.support, g j ^ d j).totalDegree :=
      MvPolynomial.totalDegree_mul _ _
    _ = (∏ j ∈ d.support, g j ^ d j).totalDegree := by
      rw [MvPolynomial.totalDegree_C, zero_add]
    _ ≤ ∑ j ∈ d.support, (g j ^ d j).totalDegree :=
      MvPolynomial.totalDegree_finsetProd d.support (fun j => g j ^ d j)
    _ ≤ ∑ j ∈ d.support, d j := by
      apply Finset.sum_le_sum
      intro j _hj
      exact (MvPolynomial.totalDegree_pow (g j) (d j)).trans
        (by simpa only [Nat.mul_one] using Nat.mul_le_mul_left (d j) (hg j))

theorem substitution_degree_le {m n : ℕ}
    (g : Fin m → MvPolynomial (Fin n) (ZMod 2))
    (hg : ∀ i, (g i).totalDegree ≤ 1) (P : MvPolynomial (Fin m) (ZMod 2)) :
    (MvPolynomial.eval₂ MvPolynomial.C g P).totalDegree ≤ P.totalDegree := by
  classical
  have hexpand := congrArg
    (fun Q : MvPolynomial (Fin m) (ZMod 2) => MvPolynomial.eval₂ MvPolynomial.C g Q)
    (MvPolynomial.as_sum P)
  rw [MvPolynomial.eval₂_sum] at hexpand
  rw [hexpand]
  apply MvPolynomial.totalDegree_finsetSum_le
  intro d hd
  exact (substituted_monomial_degree_le g hg d (P.coeff d)).trans
    (MvPolynomial.le_totalDegree hd)

/-- A coordinate of x ↦ L(x)+p, as a polynomial in the smaller parameter space. -/
noncomputable def coordinatePolynomial {m n : ℕ}
    (L : Pt n →ₗ[ZMod 2] Pt m) (p : Pt m) (i : Fin m) :
    MvPolynomial (Fin n) (ZMod 2) :=
  Paper6FlatBasics.formPolynomial ((LinearMap.proj i).comp L) 0 + MvPolynomial.C (p i)

theorem coordinatePolynomial_degree_le {m n : ℕ}
    (L : Pt n →ₗ[ZMod 2] Pt m) (p : Pt m) (i : Fin m) :
    (coordinatePolynomial L p i).totalDegree ≤ 1 := by
  unfold coordinatePolynomial
  exact (MvPolynomial.totalDegree_add _ _).trans
    (max_le (Paper6FlatBasics.formPolynomial_degree_le _ _)
      (by simpa only [MvPolynomial.totalDegree_C] using Nat.zero_le 1))

theorem eval_coordinatePolynomial {m n : ℕ}
    (L : Pt n →ₗ[ZMod 2] Pt m) (p : Pt m) (i : Fin m) (x : Pt n) :
    MvPolynomial.eval x (coordinatePolynomial L p i) = (L x + p) i := by
  simp only [coordinatePolynomial, MvPolynomial.eval_add,
    Paper6FlatBasics.eval_formPolynomial, MvPolynomial.eval_C, sub_zero,
    LinearMap.comp_apply, LinearMap.proj_apply, Pi.add_apply]

/-- The actual restriction polynomial, in n variables rather than m variables. -/
noncomputable def affinePullback {m n : ℕ}
    (L : Pt n →ₗ[ZMod 2] Pt m) (p : Pt m) (P : MvPolynomial (Fin m) (ZMod 2)) :
    MvPolynomial (Fin n) (ZMod 2) :=
  MvPolynomial.eval₂ MvPolynomial.C (coordinatePolynomial L p) P

theorem affinePullback_degree_le {m n : ℕ}
    (L : Pt n →ₗ[ZMod 2] Pt m) (p : Pt m) (P : MvPolynomial (Fin m) (ZMod 2)) :
    (affinePullback L p P).totalDegree ≤ P.totalDegree :=
  substitution_degree_le (coordinatePolynomial L p) (coordinatePolynomial_degree_le L p) P

theorem evalFun_affinePullback {m n : ℕ}
    (L : Pt n →ₗ[ZMod 2] Pt m) (p : Pt m) (P : MvPolynomial (Fin m) (ZMod 2)) :
    evalFun (affinePullback L p P) = fun x => evalFun P (L x + p) := by
  funext x
  have hcoordinates : (MvPolynomial.eval x ∘ coordinatePolynomial L p) = L x + p := by
    funext i
    exact eval_coordinatePolynomial L p i x
  change MvPolynomial.eval x (MvPolynomial.eval₂ MvPolynomial.C (coordinatePolynomial L p) P) =
    MvPolynomial.eval (L x + p) P
  rw [← MvPolynomial.eval_assoc, hcoordinates]

theorem affine_pullback_mem {r m n : ℕ}
    (L : Pt n →ₗ[ZMod 2] Pt m) (p : Pt m) (q : BFun m) (hq : q ∈ RM r m) :
    (fun x => q (L x + p)) ∈ RM r n := by
  rcases hq with ⟨P, hP, rfl⟩
  exact ⟨affinePullback L p P, (affinePullback_degree_le L p P).trans hP,
    (evalFun_affinePullback L p P).symm⟩

/-- A linear parametrization of the direction using its actual finite basis. -/
noncomputable def parameterLinear {m : ℕ} (H : AffineSubspace (ZMod 2) (Pt m)) :
    Pt (Module.finrank (ZMod 2) H.direction) →ₗ[ZMod 2] Pt m :=
  H.direction.subtype.comp
    (Module.finBasis (ZMod 2) H.direction).equivFun.symm.toLinearMap

/-- The same parametrization, with its bijectivity onto the flat recorded. -/
noncomputable def parameterEquiv {m : ℕ} (H : AffineSubspace (ZMod 2) (Pt m))
    (p : Pt m) (hp : p ∈ H) :
    Pt (Module.finrank (ZMod 2) H.direction) ≃ (H : Set (Pt m)) :=
  (Module.finBasis (ZMod 2) H.direction).equivFun.symm.toEquiv.trans
    (Paper6FlatBasics.directionEquiv H p hp).symm

theorem coe_parameterEquiv {m : ℕ} (H : AffineSubspace (ZMod 2) (Pt m))
    (p : Pt m) (hp : p ∈ H) (x : Pt (Module.finrank (ZMod 2) H.direction)) :
    ((parameterEquiv H p hp x) : Pt m) = parameterLinear H x + p := rfl

theorem support_ncard_eq_hamming {m : ℕ} (f : BFun m) :
    (Function.support f).ncard = hammingNorm f := by
  classical
  change Nat.card {x : Pt m // f x ≠ 0} = hammingNorm f
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  rfl

/-- The restriction has exactly the original support cardinality on the flat. -/
theorem restricted_weight {m : ℕ} (H : AffineSubspace (ZMod 2) (Pt m))
    (p : Pt m) (hp : p ∈ H) (q : BFun m) :
    ((H : Set (Pt m)) ∩ Function.support q).ncard =
      hammingNorm (fun x => q (parameterLinear H x + p)) := by
  classical
  have hinjective : Function.Injective (fun x => parameterLinear H x + p) := by
    intro x y hxy
    apply (parameterEquiv H p hp).injective
    apply Subtype.ext
    simpa only [coe_parameterEquiv] using hxy
  have himage :
      (fun x => parameterLinear H x + p) '' Function.support (fun x => q (parameterLinear H x + p)) =
        (H : Set (Pt m)) ∩ Function.support q := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      refine ⟨?_, hx⟩
      change parameterLinear H x + p ∈ (H : Set (Pt m))
      rw [← coe_parameterEquiv H p hp x]
      exact (parameterEquiv H p hp x).property
    · intro hy
      let yH : (H : Set (Pt m)) := ⟨y, hy.1⟩
      let x := (parameterEquiv H p hp).symm yH
      have he : parameterLinear H x + p = y := by
        rw [← coe_parameterEquiv H p hp x]
        exact congrArg Subtype.val ((parameterEquiv H p hp).apply_symm_apply yH)
      refine ⟨x, ?_, he⟩
      change q (parameterLinear H x + p) ≠ 0
      rw [he]
      exact hy.2
  calc
    ((H : Set (Pt m)) ∩ Function.support q).ncard =
        ((fun x => parameterLinear H x + p) ''
          Function.support (fun x => q (parameterLinear H x + p))).ncard :=
      congrArg Set.ncard himage.symm
    _ = (Function.support (fun x => q (parameterLinear H x + p))).ncard :=
      Set.ncard_image_of_injective _ hinjective
    _ = hammingNorm (fun x => q (parameterLinear H x + p)) := support_ncard_eq_hamming _

/-- A general flat version: no nonemptiness or dimension assumptions are required. -/
theorem quadratic_on_flat {m : ℕ} (H : AffineSubspace (ZMod 2) (Pt m))
    (q : BFun m) (hq : q ∈ RM 2 m) :
    Even (((H : Set (Pt m)) ∩ Function.support q).ncard) ∨
      ((H : Set (Pt m)) ∩ Function.support q).ncard ≤ 3 := by
  classical
  by_cases hH : (H : Set (Pt m)).Nonempty
  · obtain ⟨p, hpSet⟩ := hH
    have hp : p ∈ H := (AffineSubspace.mem_coe p H).mp hpSet
    let k := Module.finrank (ZMod 2) H.direction
    let f : BFun k := fun x => q (parameterLinear H x + p)
    have hf : f ∈ RM 2 k := affine_pullback_mem (parameterLinear H) p q hq
    have hw : ((H : Set (Pt m)) ∩ Function.support q).ncard = hammingNorm f :=
      restricted_weight H p hp q
    by_cases hk : 2 < k
    · left
      rw [hw]
      exact Paper6Parity.even_weight 2 k hk f hf
    · have hk2 : k ≤ 2 := Nat.le_of_not_gt hk
      have hbound : ((H : Set (Pt m)) ∩ Function.support q).ncard ≤ 4 := by
        calc
          ((H : Set (Pt m)) ∩ Function.support q).ncard = hammingNorm f := hw
          _ ≤ 2 ^ k := Paper6Parity.hammingNorm_le_points k f
          _ ≤ 4 := by
            simpa using Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ)) hk2
      by_cases heven : Even (((H : Set (Pt m)) ∩ Function.support q).ncard)
      · exact Or.inl heven
      · right
        have hne : ((H : Set (Pt m)) ∩ Function.support q).ncard ≠ 4 := by
          intro heq
          apply heven
          rw [heq]
          decide
        omega
  · have hempty : (H : Set (Pt m)) = ∅ := by
      ext x
      constructor
      · intro hx
        exact (hH ⟨x, hx⟩).elim
      · intro hx
        exact hx.elim
    left
    rw [hempty, Set.empty_inter, Set.ncard_empty]
    exact ⟨0, rfl⟩

/-- The exact frozen intersection statement, including empty G or E. -/
theorem check_FactStar : BackfillPaper6.V3.FactStar := by
  intro G E q hq
  simpa only [AffineSubspace.coe_inf] using quadratic_on_flat (G ⊓ E) q hq

end Paper6FactStar

#print axioms Paper6FactStar.substituted_monomial_degree_le
#print axioms Paper6FactStar.substitution_degree_le
#print axioms Paper6FactStar.coordinatePolynomial
#print axioms Paper6FactStar.coordinatePolynomial_degree_le
#print axioms Paper6FactStar.eval_coordinatePolynomial
#print axioms Paper6FactStar.affinePullback
#print axioms Paper6FactStar.affinePullback_degree_le
#print axioms Paper6FactStar.evalFun_affinePullback
#print axioms Paper6FactStar.affine_pullback_mem
#print axioms Paper6FactStar.parameterLinear
#print axioms Paper6FactStar.parameterEquiv
#print axioms Paper6FactStar.coe_parameterEquiv
#print axioms Paper6FactStar.support_ncard_eq_hamming
#print axioms Paper6FactStar.restricted_weight
#print axioms Paper6FactStar.quadratic_on_flat
#print axioms Paper6FactStar.check_FactStar
