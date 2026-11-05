import Mathlib

/-! Exact single-vertex cofactor recurrence. The complementary matrix is
inverted only in this generic algebraic lemma; the graph application proves
its required nonvanishing from the monic characteristic polynomial. -/
set_option autoImplicit false
noncomputable section
namespace Paper7UnicyclicSchwenk
open scoped BigOperators

/-- A one-point border with zero top-left entry. No inverse of the full matrix
is required, and the complementary type may be empty. -/
theorem det_singleton_border {R I J : Type*} [CommRing R]
    [Fintype I] [DecidableEq I] [Unique I] [Fintype J] [DecidableEq J]
    (D : Matrix J J R) [Invertible D] (v : J) (c : J → R) :
    (Matrix.fromBlocks (0 : Matrix I I R)
      (Matrix.of fun (_ : I) (j : J) => (Pi.single v (1 : R) : J → R) j)
      (Matrix.of fun (i : J) (_ : I) => c i) D).det =
      -∑ j, D.adjugate v j * c j := by
  let : Invertible D.det := Matrix.detInvertibleOfInvertible D
  have hentry (i j : J) : D.det * (⅟D) i j = D.adjugate i j := by
    rw [Matrix.invOf_eq]
    change D.det * (⅟D.det * D.adjugate i j) = D.adjugate i j
    rw [← mul_assoc, mul_invOf_self, one_mul]
  have hrow (j : J) :
      ((Matrix.of fun (_ : I) k => (Pi.single v (1 : R) : J → R) k) * ⅟D) default j = (⅟D) v j := by
    simp [Matrix.mul_apply, Pi.single_apply]
  rw [Matrix.det_fromBlocks₂₂, Matrix.det_unique (n := I)]
  change D.det * (0 - ∑ j : J,
    ((Matrix.of fun (_ : I) k => (Pi.single v (1 : R) : J → R) k) * ⅟D) default j * c j) = _
  simp_rw [hrow]
  rw [zero_sub, mul_neg, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rw [← mul_assoc, hentry]
#print axioms Paper7UnicyclicSchwenk.det_singleton_border

/-- Cofactor recurrence after separating one actual index. -/
theorem adjugate_puncture_recurrence {R V : Type*} [CommRing R]
    [Fintype V] [DecidableEq V] (M : Matrix V V R) (u : V)
    (v : {x : V // x ≠ u})
    (hdet : IsUnit (M.submatrix
      (fun x : {x : V // x ≠ u} => x.val) (fun x : {x : V // x ≠ u} => x.val)).det) :
    M.adjugate v.val u = -∑ z : {x : V // x ≠ u},
      (M.submatrix (fun x : {x : V // x ≠ u} => x.val)
        (fun x : {x : V // x ≠ u} => x.val)).adjugate v z * M z.val u := by
  classical
  let : Fintype {x : V // x = u} := Subtype.fintype (fun x => x = u)
  let D := M.submatrix (fun x : {x : V // x ≠ u} => x.val)
    (fun x : {x : V // x ≠ u} => x.val)
  let T := M.updateRow u (Pi.single v.val 1)
  let : Unique {x : V // x = u} :=
    { default := ⟨u, rfl⟩
      uniq := fun x => Subtype.ext x.property }
  let : Invertible D := Matrix.invertibleOfIsUnitDet D hdet
  have h00 : T.toBlock (fun x => x = u) (fun x => x = u) = 0 := by
    apply Matrix.ext
    intro i j
    simp [Matrix.toBlock_apply, T, i.property, j.property, Ne.symm v.property]
  have h01 : T.toBlock (fun x => x = u) (fun x => x ≠ u) =
      (Matrix.of fun (_ : {x : V // x = u}) (j : {x : V // x ≠ u}) =>
        (Pi.single v (1 : R) : {x : V // x ≠ u} → R) j) := by
    apply Matrix.ext
    intro i j
    by_cases hj : j = v
    · subst j
      simp [Matrix.toBlock_apply, T, i.property]
    · have hjv : j.val ≠ v.val := fun h => hj (Subtype.ext h)
      simp [Matrix.toBlock_apply, T, i.property, hj, hjv]
  have h10 : T.toBlock (fun x => x ≠ u) (fun x => x = u) =
      (Matrix.of fun (i : {x : V // x ≠ u}) (_ : {x : V // x = u}) => M i.val u) := by
    apply Matrix.ext
    intro i j
    simp [Matrix.toBlock_apply, T, i.property, j.property]
  have h11 : T.toBlock (fun x => x ≠ u) (fun x => x ≠ u) = D := by
    apply Matrix.ext
    intro i j
    simp [Matrix.toBlock_apply, Matrix.submatrix_apply, T, D, i.property]
  rw [Matrix.adjugate_apply]
  change T.det = _
  rw [Matrix.det_toBlock T (fun x => x = u), h00, h01, h10, h11]
  exact det_singleton_border D v (fun z => M z.val u)
#print axioms Paper7UnicyclicSchwenk.adjugate_puncture_recurrence

/-- Passing to the polynomial fraction field removes the unit condition,
provided the complementary determinant is genuinely nonzero. -/
theorem polynomial_adjugate_puncture {V : Type} [Fintype V] [DecidableEq V]
    (M : Matrix V V (Polynomial ℤ)) (u : V) (v : {x : V // x ≠ u})
    (hdet : (M.submatrix (fun x : {x : V // x ≠ u} => x.val)
      (fun x : {x : V // x ≠ u} => x.val)).det ≠ 0) :
    M.adjugate v.val u = -∑ z : {x : V // x ≠ u},
      (M.submatrix (fun x : {x : V // x ≠ u} => x.val)
        (fun x : {x : V // x ≠ u} => x.val)).adjugate v z * M z.val u := by
  classical
  let K : Type := FractionRing (Polynomial ℤ)
  let f : Polynomial ℤ →+* K := algebraMap (Polynomial ℤ) K
  have hf : Function.Injective f := IsFractionRing.injective (Polynomial ℤ) K
  let D := M.submatrix (fun x : {x : V // x ≠ u} => x.val)
    (fun x : {x : V // x ≠ u} => x.val)
  have hmapD : (M.map f).submatrix
      (fun x : {x : V // x ≠ u} => x.val) (fun x : {x : V // x ≠ u} => x.val) =
      D.map f := rfl
  have hunit : IsUnit ((M.map f).submatrix
      (fun x : {x : V // x ≠ u} => x.val) (fun x : {x : V // x ≠ u} => x.val)).det := by
    apply isUnit_iff_ne_zero.mpr
    intro hz
    apply hdet
    apply hf
    calc
      f D.det = (D.map f).det := f.map_det D
      _ = 0 := by simpa only [hmapD] using hz
      _ = f 0 := (map_zero f).symm
  have hadj {W : Type} [Fintype W] [DecidableEq W]
      (A : Matrix W W (Polynomial ℤ)) (i j : W) :
      f (A.adjugate i j) = (A.map f).adjugate i j :=
    congrFun (congrFun (f.map_adjugate A) i) j
  have h := adjugate_puncture_recurrence (M.map f) u v hunit
  apply hf
  simpa only [map_neg, map_sum, map_mul, hadj, Matrix.map_apply, hmapD] using h
#print axioms Paper7UnicyclicSchwenk.polynomial_adjugate_puncture

/-- A cofactor vanishes across a one-sided closed block. This is proved by a
zero row of the diagonal block of the actual forced-row determinant. -/
theorem adjugate_zero_of_closed_block {R V : Type*} [CommRing R]
    [Fintype V] [DecidableEq V] (M : Matrix V V R) (S : Set V)
    (u v : V) (hu : u ∈ S) (hv : v ∉ S)
    (hcross : ∀ i, i ∉ S → ∀ j, j ∈ S → M i j = 0) :
    M.adjugate v u = 0 := by
  classical
  let T := M.updateRow u (Pi.single v 1)
  have htri : ∀ i, i ∉ S → ∀ j, j ∈ S → T i j = 0 := by
    intro i hi j hj
    have hiu : i ≠ u := fun h => hi (h.symm ▸ hu)
    simpa only [T, Matrix.updateRow_ne hiu] using hcross i hi j hj
  have hzero : (T.toSquareBlockProp (fun x => x ∈ S)).det = 0 := by
    apply Matrix.det_eq_zero_of_row_eq_zero ⟨u, hu⟩
    intro j
    have hjv : j.val ≠ v := fun h => hv (h ▸ j.property)
    simp [Matrix.toSquareBlockProp_def, T, hjv]
  rw [Matrix.adjugate_apply]
  change T.det = 0
  rw [Matrix.twoBlockTriangular_det T (fun x => x ∈ S) htri, hzero, zero_mul]
#print axioms Paper7UnicyclicSchwenk.adjugate_zero_of_closed_block

end Paper7UnicyclicSchwenk
