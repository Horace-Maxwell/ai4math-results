import Research.Backfill.Paper6.AffineInvariance

/-!
# Cardinality and the actual indicator polynomial of every binary affine flat

Complete source candidate for the frozen V3.FlatBasics. Not yet compiled or
independently reviewed. The only reused paper-specific proof is the standard
coordinate expansion from AffineInvariance.

Choose p in the flat, and take coordinates in the quotient by its direction.
Each quotient coordinate of x-p is affine linear. The product of one plus these
coordinates is exactly the indicator over ZMod 2. The quotient has dimension
m-k, so this actual polynomial has total degree at most m-k.
-/

set_option autoImplicit false

namespace Paper6FlatBasics

open Finset
open BackfillPaper6.V3

/-- Translation by a chosen point identifies a nonempty flat with its direction. -/
def directionEquiv {m : ℕ} (F : AffineSubspace (ZMod 2) (Pt m))
    (p : Pt m) (hp : p ∈ F) : (F : Set (Pt m)) ≃ F.direction where
  toFun x := ⟨(x : Pt m) - p, by
    simpa only [vsub_eq_sub] using AffineSubspace.vsub_mem_direction x.property hp⟩
  invFun v := ⟨(v : Pt m) + p, by
    apply (AffineSubspace.mem_coe ((v : Pt m) + p) F).mpr
    simpa only [vadd_eq_add] using AffineSubspace.vadd_mem_of_mem_direction v.property hp⟩
  left_inv x := by
    apply Subtype.ext
    exact sub_add_cancel _ _
  right_inv v := by
    apply Subtype.ext
    exact add_sub_cancel_right _ _

theorem flat_ncard {m : ℕ} (F : AffineSubspace (ZMod 2) (Pt m))
    (p : Pt m) (hp : p ∈ F) (k : ℕ)
    (hk : Module.finrank (ZMod 2) F.direction = k) :
    (F : Set (Pt m)).ncard = 2 ^ k := by
  calc
    (F : Set (Pt m)).ncard = Nat.card (F : Set (Pt m)) := rfl
    _ = Nat.card F.direction := Nat.card_congr (directionEquiv F p hp)
    _ = Nat.card (ZMod 2) ^ Module.finrank (ZMod 2) F.direction :=
      Module.natCard_eq_pow_finrank
    _ = 2 ^ k := by rw [hk]; simp

/-- Linear functionals are reconstructed from their values on the standard coordinate vectors. -/
theorem linear_form_expansion {m : ℕ} (L : Pt m →ₗ[ZMod 2] ZMod 2) (x : Pt m) :
    L x = ∑ j : Fin m, L (Pi.single j 1) * x j := by
  calc
    L x = L (∑ j : Fin m, x j • (Pi.single j 1 : Pt m)) := by
      rw [Paper6AffineInvariance.point_basis_expansion x]
    _ = ∑ j : Fin m, x j * L (Pi.single j 1) := by
      simp only [map_sum, map_smul, smul_eq_mul]
    _ = ∑ j : Fin m, L (Pi.single j 1) * x j := by
      apply Finset.sum_congr rfl
      intro j _hj
      exact mul_comm _ _

/-- A concrete polynomial evaluating to L(x-p), with the translation retained. -/
noncomputable def formPolynomial {m : ℕ} (L : Pt m →ₗ[ZMod 2] ZMod 2)
    (p : Pt m) : MvPolynomial (Fin m) (ZMod 2) :=
  MvPolynomial.C (-L p) +
    ∑ j : Fin m, MvPolynomial.C (L (Pi.single j 1)) * MvPolynomial.X j

theorem formPolynomial_degree_le {m : ℕ} (L : Pt m →ₗ[ZMod 2] ZMod 2) (p : Pt m) :
    (formPolynomial L p).totalDegree ≤ 1 := by
  unfold formPolynomial
  apply (MvPolynomial.totalDegree_add _ _).trans
  apply max_le
  · simpa only [MvPolynomial.totalDegree_C] using Nat.zero_le 1
  · apply MvPolynomial.totalDegree_finsetSum_le
    intro j _hj
    simpa only [MvPolynomial.totalDegree_C, MvPolynomial.totalDegree_X, zero_add] using
      (MvPolynomial.totalDegree_mul
        (MvPolynomial.C (L (Pi.single j 1)) : MvPolynomial (Fin m) (ZMod 2))
        (MvPolynomial.X j))

theorem eval_formPolynomial {m : ℕ} (L : Pt m →ₗ[ZMod 2] ZMod 2)
    (p x : Pt m) : MvPolynomial.eval x (formPolynomial L p) = L (x - p) := by
  simp only [formPolynomial, MvPolynomial.eval_add, MvPolynomial.eval_sum,
    MvPolynomial.eval_mul, MvPolynomial.eval_C, MvPolynomial.eval_X]
  rw [← linear_form_expansion L x, map_sub]
  ring

/-- Coordinates of the quotient projection, viewed as linear forms on the ambient space. -/
noncomputable def quotientForm {m : ℕ} (D : Submodule (ZMod 2) (Pt m))
    (i : Fin (Module.finrank (ZMod 2) (Pt m ⧸ D))) : Pt m →ₗ[ZMod 2] ZMod 2 :=
  ((Module.finBasis (ZMod 2) (Pt m ⧸ D)).coord i).comp D.mkQ

theorem quotient_forms_zero_iff {m : ℕ} (D : Submodule (ZMod 2) (Pt m)) (x : Pt m) :
    (∀ i, quotientForm D i x = 0) ↔ x ∈ D := by
  change (∀ i, (Module.finBasis (ZMod 2) (Pt m ⧸ D)).coord i (D.mkQ x) = 0) ↔ x ∈ D
  rw [Module.Basis.forall_coord_eq_zero_iff, Submodule.mkQ_apply,
    Submodule.Quotient.mk_eq_zero]

theorem sub_mem_direction_iff {m : ℕ} (F : AffineSubspace (ZMod 2) (Pt m))
    (p : Pt m) (hp : p ∈ F) (x : Pt m) : x - p ∈ F.direction ↔ x ∈ F := by
  constructor
  · intro h
    have hv := AffineSubspace.vadd_mem_of_mem_direction h hp
    simpa only [vadd_eq_add, sub_add_cancel] using hv
  · intro h
    simpa only [vsub_eq_sub] using AffineSubspace.vsub_mem_direction h hp

/-- All quotient coordinates vanish precisely on the chosen affine flat. -/
theorem flat_equations_iff {m : ℕ} (F : AffineSubspace (ZMod 2) (Pt m))
    (p : Pt m) (hp : p ∈ F) (x : Pt m) :
    (∀ i, quotientForm F.direction i (x - p) = 0) ↔ x ∈ F := by
  rw [quotient_forms_zero_iff]
  exact sub_mem_direction_iff F p hp x

theorem quotient_dimension {m : ℕ} (F : AffineSubspace (ZMod 2) (Pt m))
    (k : ℕ) (hk : Module.finrank (ZMod 2) F.direction = k) :
    Module.finrank (ZMod 2) (Pt m ⧸ F.direction) = m - k := by
  have hsum : Module.finrank (ZMod 2) (Pt m ⧸ F.direction) + k = m := by
    calc
      Module.finrank (ZMod 2) (Pt m ⧸ F.direction) + k =
          Module.finrank (ZMod 2) (Pt m ⧸ F.direction) +
            Module.finrank (ZMod 2) F.direction := by rw [hk]
      _ = Module.finrank (ZMod 2) (Pt m) :=
        Submodule.finrank_quotient_add_finrank F.direction
      _ = m := by
        change Module.finrank (ZMod 2) (Fin m → ZMod 2) = m
        rw [Module.finrank_pi, Fintype.card_fin]
  calc
    Module.finrank (ZMod 2) (Pt m ⧸ F.direction) =
        (Module.finrank (ZMod 2) (Pt m ⧸ F.direction) + k) - k :=
      (Nat.add_sub_cancel _ _).symm
    _ = m - k := congrArg (fun n : ℕ => n - k) hsum

/-- One factor per quotient coordinate; an empty quotient basis gives the constant one. -/
noncomputable def indicatorPolynomial {m : ℕ} (F : AffineSubspace (ZMod 2) (Pt m))
    (p : Pt m) : MvPolynomial (Fin m) (ZMod 2) :=
  ∏ i : Fin (Module.finrank (ZMod 2) (Pt m ⧸ F.direction)),
    (MvPolynomial.C 1 + formPolynomial (quotientForm F.direction i) p)

theorem indicatorPolynomial_degree_le {m : ℕ}
    (F : AffineSubspace (ZMod 2) (Pt m)) (p : Pt m) :
    (indicatorPolynomial F p).totalDegree ≤
      Module.finrank (ZMod 2) (Pt m ⧸ F.direction) := by
  classical
  calc
    (indicatorPolynomial F p).totalDegree ≤
        ∑ i : Fin (Module.finrank (ZMod 2) (Pt m ⧸ F.direction)),
          (MvPolynomial.C (1 : ZMod 2) + formPolynomial (quotientForm F.direction i) p :
            MvPolynomial (Fin m) (ZMod 2)).totalDegree := by
      simpa only [indicatorPolynomial] using
        (MvPolynomial.totalDegree_finsetProd
          (Finset.univ : Finset (Fin (Module.finrank (ZMod 2) (Pt m ⧸ F.direction))))
          (fun i => (MvPolynomial.C (1 : ZMod 2) +
            formPolynomial (quotientForm F.direction i) p : MvPolynomial (Fin m) (ZMod 2))))
    _ ≤ ∑ _i : Fin (Module.finrank (ZMod 2) (Pt m ⧸ F.direction)), (1 : ℕ) := by
      apply Finset.sum_le_sum
      intro i _hi
      exact (MvPolynomial.totalDegree_add _ _).trans
        (max_le
          (by simpa only [MvPolynomial.totalDegree_C] using Nat.zero_le 1)
          (formPolynomial_degree_le (quotientForm F.direction i) p))
    _ = Module.finrank (ZMod 2) (Pt m ⧸ F.direction) := by simp

theorem binary_one_add_of_ne_zero (z : ZMod 2) (hz : z ≠ 0) : 1 + z = 0 := by
  revert z
  decide

/-- The same frozen indicator function, not merely a codeword of the same weight. -/
theorem evalFun_indicatorPolynomial {m : ℕ}
    (F : AffineSubspace (ZMod 2) (Pt m)) (p : Pt m) (hp : p ∈ F) :
    evalFun (indicatorPolynomial F p) = ind (F : Set (Pt m)) := by
  classical
  funext x
  have heval : evalFun (indicatorPolynomial F p) x =
      ∏ i : Fin (Module.finrank (ZMod 2) (Pt m ⧸ F.direction)),
        (1 + quotientForm F.direction i (x - p)) := by
    simp only [evalFun, indicatorPolynomial, MvPolynomial.eval_prod,
      MvPolynomial.eval_add, MvPolynomial.eval_C, eval_formPolynomial]
  rw [heval]
  by_cases hx : x ∈ F
  · rw [show ind (F : Set (Pt m)) x = 1 by simp [ind, hx]]
    have hzero := (flat_equations_iff F p hp x).mpr hx
    apply Finset.prod_eq_one
    intro i _hi
    rw [hzero i, add_zero]
  · rw [show ind (F : Set (Pt m)) x = 0 by simp [ind, hx]]
    have hnall : ¬ ∀ i, quotientForm F.direction i (x - p) = 0 :=
      fun h => hx ((flat_equations_iff F p hp x).mp h)
    obtain ⟨i, hi⟩ := not_forall.mp hnall
    apply Finset.prod_eq_zero (i := i)
    · exact Finset.mem_univ i
    · exact binary_one_add_of_ne_zero _ hi

/-- Both exact clauses of the frozen statement, for all m and k without extra hypotheses. -/
theorem check_FlatBasics : BackfillPaper6.V3.FlatBasics := by
  intro m k F hF
  obtain ⟨p, hp⟩ := hF.1
  constructor
  · exact flat_ncard F p hp k hF.2
  · refine ⟨indicatorPolynomial F p, ?_, (evalFun_indicatorPolynomial F p hp).symm⟩
    rw [← quotient_dimension F k hF.2]
    exact indicatorPolynomial_degree_le F p

end Paper6FlatBasics

#print axioms Paper6FlatBasics.directionEquiv
#print axioms Paper6FlatBasics.flat_ncard
#print axioms Paper6FlatBasics.linear_form_expansion
#print axioms Paper6FlatBasics.formPolynomial
#print axioms Paper6FlatBasics.formPolynomial_degree_le
#print axioms Paper6FlatBasics.eval_formPolynomial
#print axioms Paper6FlatBasics.quotientForm
#print axioms Paper6FlatBasics.quotient_forms_zero_iff
#print axioms Paper6FlatBasics.sub_mem_direction_iff
#print axioms Paper6FlatBasics.flat_equations_iff
#print axioms Paper6FlatBasics.quotient_dimension
#print axioms Paper6FlatBasics.indicatorPolynomial
#print axioms Paper6FlatBasics.indicatorPolynomial_degree_le
#print axioms Paper6FlatBasics.binary_one_add_of_ne_zero
#print axioms Paper6FlatBasics.evalFun_indicatorPolynomial
#print axioms Paper6FlatBasics.check_FlatBasics
