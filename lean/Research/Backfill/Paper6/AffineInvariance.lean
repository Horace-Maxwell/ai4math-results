import Research.Backfill.Paper6.ChallengeV3

/-!
# Affine invariance of Reed–Muller membership, weight, and flats

Complete source candidate for the exact frozen V3.AffineInvariance conjunction.
This source has not been compiled or independently reviewed.

Each affine coordinate is represented by a constant plus a linear polynomial.
Substitution does not increase total degree: expand over the original support,
bound each substituted monomial, and then bound the finite sum. This argument
allows constants, cancellation, zero dimensions, and arbitrary affine translation.
-/

set_option autoImplicit false

namespace Paper6AffineInvariance

open Finset
open BackfillPaper6.V3

/-- The standard coordinate expansion, valid also in the zero-dimensional space. -/
theorem point_basis_expansion {m : ℕ} (x : Pt m) :
    (∑ j : Fin m, x j • (Pi.single j 1 : Pt m)) = x := by
  classical
  calc
    (∑ j : Fin m, x j • (Pi.single j 1 : Pt m)) =
        ∑ j : Fin m, (Pi.single j (x j) : Pt m) := by
      apply Finset.sum_congr rfl
      intro j _hj
      simpa only [smul_eq_mul, mul_one] using
        (Pi.single_smul' j (x j) (1 : ZMod 2)).symm
    _ = x := Finset.univ_sum_single x

theorem linear_coordinate_formula {m : ℕ} (φ : Pt m ≃ᵃ[ZMod 2] Pt m)
    (x : Pt m) (i : Fin m) :
    φ.linear x i = ∑ j : Fin m, φ.linear (Pi.single j 1) i * x j := by
  classical
  calc
    φ.linear x i = φ.linear (∑ j : Fin m, x j • (Pi.single j 1 : Pt m)) i := by
      rw [point_basis_expansion x]
    _ = ∑ j : Fin m, x j * φ.linear (Pi.single j 1) i := by
      simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    _ = ∑ j : Fin m, φ.linear (Pi.single j 1) i * x j := by
      apply Finset.sum_congr rfl
      intro j _hj
      exact mul_comm _ _

/-- The translation term φ(0) is retained explicitly. -/
theorem affine_coordinate_formula {m : ℕ} (φ : Pt m ≃ᵃ[ZMod 2] Pt m)
    (x : Pt m) (i : Fin m) :
    φ x i = φ 0 i + ∑ j : Fin m, φ.linear (Pi.single j 1) i * x j := by
  calc
    φ x i = φ.linear x i + φ 0 i := by
      simpa only [vadd_eq_add, add_zero, Pi.add_apply] using
        congrFun (φ.map_vadd (0 : Pt m) x) i
    _ = φ 0 i + ∑ j : Fin m, φ.linear (Pi.single j 1) i * x j := by
      rw [linear_coordinate_formula]
      exact add_comm _ _

/-- An actual polynomial of degree at most one for one affine coordinate. -/
noncomputable def coordinatePolynomial {m : ℕ} (φ : Pt m ≃ᵃ[ZMod 2] Pt m)
    (i : Fin m) : MvPolynomial (Fin m) (ZMod 2) :=
  MvPolynomial.C (φ 0 i) +
    ∑ j : Fin m, MvPolynomial.C (φ.linear (Pi.single j 1) i) * MvPolynomial.X j

theorem coordinatePolynomial_degree_le {m : ℕ} (φ : Pt m ≃ᵃ[ZMod 2] Pt m)
    (i : Fin m) : (coordinatePolynomial φ i).totalDegree ≤ 1 := by
  unfold coordinatePolynomial
  apply (MvPolynomial.totalDegree_add _ _).trans
  apply max_le
  · simpa only [MvPolynomial.totalDegree_C] using Nat.zero_le 1
  · apply MvPolynomial.totalDegree_finsetSum_le
    intro j _hj
    simpa only [MvPolynomial.totalDegree_C, MvPolynomial.totalDegree_X, zero_add] using
      (MvPolynomial.totalDegree_mul
        (MvPolynomial.C (φ.linear (Pi.single j 1) i) : MvPolynomial (Fin m) (ZMod 2))
        (MvPolynomial.X j))

theorem eval_coordinatePolynomial {m : ℕ} (φ : Pt m ≃ᵃ[ZMod 2] Pt m)
    (i : Fin m) (x : Pt m) : MvPolynomial.eval x (coordinatePolynomial φ i) = φ x i := by
  simp only [coordinatePolynomial, MvPolynomial.eval_add, MvPolynomial.eval_sum,
    MvPolynomial.eval_mul, MvPolynomial.eval_C, MvPolynomial.eval_X]
  exact (affine_coordinate_formula φ x i).symm

/-- Substituting affine polynomials in a monomial does not increase its exponent sum. -/
theorem substituted_monomial_degree_le {m : ℕ}
    (g : Fin m → MvPolynomial (Fin m) (ZMod 2))
    (hg : ∀ i, (g i).totalDegree ≤ 1) (d : Fin m →₀ ℕ) (a : ZMod 2) :
    (MvPolynomial.eval₂ MvPolynomial.C g (MvPolynomial.monomial d a)).totalDegree ≤
      d.sum (fun _ n => n) := by
  classical
  rw [MvPolynomial.eval₂_monomial]
  change (MvPolynomial.C a * ∏ j ∈ d.support, g j ^ d j).totalDegree ≤
    ∑ j ∈ d.support, d j
  calc
    (MvPolynomial.C a * ∏ j ∈ d.support, g j ^ d j).totalDegree ≤
        (MvPolynomial.C a : MvPolynomial (Fin m) (ZMod 2)).totalDegree +
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

/-- Expanding over the original support handles cancellation without additional assumptions. -/
theorem substitution_degree_le {m : ℕ}
    (g : Fin m → MvPolynomial (Fin m) (ZMod 2))
    (hg : ∀ i, (g i).totalDegree ≤ 1) (p : MvPolynomial (Fin m) (ZMod 2)) :
    (MvPolynomial.eval₂ MvPolynomial.C g p).totalDegree ≤ p.totalDegree := by
  classical
  have hexpand := congrArg
    (fun q : MvPolynomial (Fin m) (ZMod 2) => MvPolynomial.eval₂ MvPolynomial.C g q)
    (MvPolynomial.as_sum p)
  rw [MvPolynomial.eval₂_sum] at hexpand
  rw [hexpand]
  apply MvPolynomial.totalDegree_finsetSum_le
  intro d hd
  exact (substituted_monomial_degree_le g hg d (p.coeff d)).trans
    (MvPolynomial.le_totalDegree hd)

/-- The actual polynomial used to represent affine precomposition. -/
noncomputable def affineSubstitution {m : ℕ} (φ : Pt m ≃ᵃ[ZMod 2] Pt m)
    (p : MvPolynomial (Fin m) (ZMod 2)) : MvPolynomial (Fin m) (ZMod 2) :=
  MvPolynomial.eval₂ MvPolynomial.C (coordinatePolynomial φ) p

theorem affineSubstitution_degree_le {m : ℕ} (φ : Pt m ≃ᵃ[ZMod 2] Pt m)
    (p : MvPolynomial (Fin m) (ZMod 2)) :
    (affineSubstitution φ p).totalDegree ≤ p.totalDegree :=
  substitution_degree_le (coordinatePolynomial φ) (coordinatePolynomial_degree_le φ) p

theorem evalFun_affineSubstitution {m : ℕ} (φ : Pt m ≃ᵃ[ZMod 2] Pt m)
    (p : MvPolynomial (Fin m) (ZMod 2)) :
    evalFun (affineSubstitution φ p) = fun x => evalFun p (φ x) := by
  funext x
  have hcoordinates : (MvPolynomial.eval x ∘ coordinatePolynomial φ) = φ x := by
    funext i
    exact eval_coordinatePolynomial φ i x
  change MvPolynomial.eval x (MvPolynomial.eval₂ MvPolynomial.C (coordinatePolynomial φ) p) =
    MvPolynomial.eval (φ x) p
  rw [← MvPolynomial.eval_assoc, hcoordinates]

theorem rm_precomposition {r m : ℕ} (φ : Pt m ≃ᵃ[ZMod 2] Pt m)
    (f : BFun m) (hf : f ∈ RM r m) : (fun x => f (φ x)) ∈ RM r m := by
  rcases hf with ⟨p, hp, rfl⟩
  exact ⟨affineSubstitution φ p, (affineSubstitution_degree_le φ p).trans hp,
    (evalFun_affineSubstitution φ p).symm⟩

/-- Affine bijectivity reindexes exactly the nonzero positions. -/
theorem weight_precomposition {m : ℕ} (φ : Pt m ≃ᵃ[ZMod 2] Pt m) (f : BFun m) :
    hammingNorm (fun x => f (φ x)) = hammingNorm f := by
  classical
  unfold hammingNorm
  apply Finset.card_equiv φ.toEquiv
  intro x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, AffineEquiv.coe_toEquiv]

/-- Both nonemptiness and the exact direction dimension survive the affine image. -/
theorem flat_map {m : ℕ} (φ : Pt m ≃ᵃ[ZMod 2] Pt m)
    (F : AffineSubspace (ZMod 2) (Pt m)) (k : ℕ) (hF : IsFlat F k) :
    IsFlat (F.map φ.toAffineMap) k := by
  rcases hF with ⟨hne, hdim⟩
  constructor
  · obtain ⟨x, hx⟩ := hne
    exact ⟨φ x, AffineSubspace.mem_map.mpr ⟨x, hx, rfl⟩⟩
  · rw [AffineSubspace.map_direction]
    exact (φ.linear.finrank_map_eq F.direction).trans hdim

/-- All three clauses of the unchanged frozen statement. -/
theorem check_AffineInvariance : BackfillPaper6.V3.AffineInvariance := by
  intro r m φ f
  exact ⟨rm_precomposition φ f, weight_precomposition φ f, flat_map φ⟩

end Paper6AffineInvariance

#print axioms Paper6AffineInvariance.point_basis_expansion
#print axioms Paper6AffineInvariance.linear_coordinate_formula
#print axioms Paper6AffineInvariance.affine_coordinate_formula
#print axioms Paper6AffineInvariance.coordinatePolynomial
#print axioms Paper6AffineInvariance.coordinatePolynomial_degree_le
#print axioms Paper6AffineInvariance.eval_coordinatePolynomial
#print axioms Paper6AffineInvariance.substituted_monomial_degree_le
#print axioms Paper6AffineInvariance.substitution_degree_le
#print axioms Paper6AffineInvariance.affineSubstitution
#print axioms Paper6AffineInvariance.affineSubstitution_degree_le
#print axioms Paper6AffineInvariance.evalFun_affineSubstitution
#print axioms Paper6AffineInvariance.rm_precomposition
#print axioms Paper6AffineInvariance.weight_precomposition
#print axioms Paper6AffineInvariance.flat_map
#print axioms Paper6AffineInvariance.check_AffineInvariance
