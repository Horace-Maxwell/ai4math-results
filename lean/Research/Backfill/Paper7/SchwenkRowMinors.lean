import Mathlib

/-! Algebraic minors for Schwenk's edge identity, over an arbitrary commutative
ring and arbitrary finite indices. No graph or cofactor formula is assumed. -/
set_option autoImplicit false
noncomputable section
namespace Paper7UnicyclicSchwenk

/-- The ordered two-point subtype, with no cardinality or nonempty-complement
assumption on the ambient type. -/
def pairIndexEquiv {V : Type*} [DecidableEq V] (u v : V) (huv : u ≠ v) :
    Fin 2 ≃ {x : V // x ∈ ({u, v} : Set V)} where
  toFun i := if i = 0 then ⟨u, by simp⟩ else ⟨v, by simp⟩
  invFun x := if x.val = u then 0 else 1
  left_inv := by
    intro i
    fin_cases i <;> simp [Ne.symm huv]
  right_inv := by
    rintro ⟨x, hx⟩
    rcases Set.mem_insert_iff.mp hx with rfl | hx
    · apply Subtype.ext
      simp
    · have h : x = v := Set.mem_singleton_iff.mp hx
      subst x
      apply Subtype.ext
      simp [Ne.symm huv]
#print axioms Paper7UnicyclicSchwenk.pairIndexEquiv

theorem det_two_row_add {R V : Type*} [CommRing R] [Fintype V] [DecidableEq V]
    (M : Matrix V V R) (u v : V) (huv : u ≠ v) (r s : V → R) :
    ((M.updateRow u (M u + r)).updateRow v (M v + s)).det =
      M.det + (M.updateRow u r).det + (M.updateRow v s).det +
        ((M.updateRow u r).updateRow v s).det := by
  rw [Matrix.det_updateRow_add]
  rw [Matrix.updateRow_comm M huv (M u + r) (M v), Matrix.updateRow_eq_self]
  rw [Matrix.det_updateRow_add, Matrix.updateRow_eq_self]
  rw [Matrix.updateRow_comm M huv (M u + r) s, Matrix.det_updateRow_add]
  have hrow : (M.updateRow v s).updateRow u (M u) = M.updateRow v s := by
    rw [Matrix.updateRow_comm M huv.symm s (M u), Matrix.updateRow_eq_self]
  rw [hrow, Matrix.updateRow_comm M huv.symm s r]
  ring
#print axioms Paper7UnicyclicSchwenk.det_two_row_add

theorem det_single_negative_row {R V : Type*} [CommRing R] [Fintype V]
    [DecidableEq V] (M : Matrix V V R) (u v : V) :
    (M.updateRow u (Pi.single v (-1))).det = -M.adjugate v u := by
  have hrow : (Pi.single v (-1) : V → R) = (-1 : R) • Pi.single v 1 := by
    simpa only [smul_eq_mul, mul_one] using (Pi.single_smul' v (-1 : R) (1 : R))
  rw [hrow, Matrix.det_updateRow_smul, ← Matrix.adjugate_apply]
  simp only [neg_one_mul]
#print axioms Paper7UnicyclicSchwenk.det_single_negative_row

/-- Both forced rows form the block [[0,-1],[-1,0]], whose determinant is -1.
The complementary block is retained even when its index type is empty. -/
theorem det_two_forced_rows {R V : Type*} [CommRing R] [Fintype V]
    [DecidableEq V] (M : Matrix V V R) (u v : V) (huv : u ≠ v) :
    ((M.updateRow u (Pi.single v (-1))).updateRow v (Pi.single u (-1))).det =
      -(M.submatrix (fun x : {x : V // x ∉ ({u, v} : Set V)} => x.val)
        (fun x : {x : V // x ∉ ({u, v} : Set V)} => x.val)).det := by
  classical
  let : Fintype {i : V // i ∈ ({u, v} : Set V)} :=
    Subtype.fintype (fun i => i ∈ ({u, v} : Set V))
  let T := (M.updateRow u (Pi.single v (-1))).updateRow v (Pi.single u (-1))
  have hcross : ∀ i, i ∈ ({u, v} : Set V) →
      ∀ j, j ∉ ({u, v} : Set V) → T i j = 0 := by
    intro i hi j hj
    have hju : j ≠ u := fun h => hj (by simp [h])
    have hjv : j ≠ v := fun h => hj (by simp [h])
    rcases Set.mem_insert_iff.mp hi with rfl | hi
    · simp [T, huv, hjv]
    · have hi' : i = v := Set.mem_singleton_iff.mp hi
      subst i
      simp [T, hju]
  have hpair : (T.toSquareBlockProp (fun i => i ∈ ({u, v} : Set V))).det = -1 := by
    let e := pairIndexEquiv u v huv
    rw [← Matrix.det_submatrix_equiv_self e, Matrix.det_fin_two]
    simp [Matrix.submatrix_apply, Matrix.toSquareBlockProp_def,
      e, pairIndexEquiv, T, huv, Ne.symm huv]
  have hrest : T.toSquareBlockProp (fun i => i ∉ ({u, v} : Set V)) =
      M.submatrix (fun x : {x : V // x ∉ ({u, v} : Set V)} => x.val)
        (fun x : {x : V // x ∉ ({u, v} : Set V)} => x.val) := by
    apply Matrix.ext
    intro i j
    have hiu : i.val ≠ u := fun h => i.property (by simp [h])
    have hiv : i.val ≠ v := fun h => i.property (by simp [h])
    change T i.val j.val = M i.val j.val
    simp only [T, Matrix.updateRow_ne hiv, Matrix.updateRow_ne hiu]
  change T.det = _
  have hdet := Matrix.twoBlockTriangular_det' T (fun i => i ∈ ({u, v} : Set V)) hcross
  have hp := congrArg₂ (fun a b : R => a * b) hpair (congrArg Matrix.det hrest)
  exact hdet.trans (hp.trans (neg_one_mul _))
#print axioms Paper7UnicyclicSchwenk.det_two_forced_rows

/-- The diagonal cofactor is the principal minor. This is the zero-length
path base case and includes a one-vertex ambient matrix. -/
theorem adjugate_diagonal_eq_complement {R V : Type*} [CommRing R] [Fintype V]
    [DecidableEq V] (M : Matrix V V R) (u : V) :
    M.adjugate u u = (M.submatrix
      (fun x : {x : V // x ∉ ({u} : Set V)} => x.val)
      (fun x : {x : V // x ∉ ({u} : Set V)} => x.val)).det := by
  classical
  let : Fintype {i : V // i ∈ ({u} : Set V)} :=
    Subtype.fintype (fun i => i ∈ ({u} : Set V))
  let T := M.updateRow u (Pi.single u 1)
  have hcross : ∀ i, i ∈ ({u} : Set V) →
      ∀ j, j ∉ ({u} : Set V) → T i j = 0 := by
    intro i hi j hj
    have hi' : i = u := Set.mem_singleton_iff.mp hi
    have hj' : j ≠ u := fun h => hj (Set.mem_singleton_iff.mpr h)
    subst i
    simp [T, hj']
  have hsingle : (T.toSquareBlockProp (fun i => i ∈ ({u} : Set V))).det = 1 := by
    let : Unique {i : V // i ∈ ({u} : Set V)} :=
      { default := ⟨u, by simp⟩
        uniq := fun i => Subtype.ext (Set.mem_singleton_iff.mp i.property) }
    rw [Matrix.det_unique]
    simp [Matrix.toSquareBlockProp_def, T]
  have hrest : T.toSquareBlockProp (fun i => i ∉ ({u} : Set V)) =
      M.submatrix (fun x : {x : V // x ∉ ({u} : Set V)} => x.val)
        (fun x : {x : V // x ∉ ({u} : Set V)} => x.val) := by
    apply Matrix.ext
    intro i j
    have hi : i.val ≠ u := fun h => i.property (Set.mem_singleton_iff.mpr h)
    change T i.val j.val = M i.val j.val
    exact congrFun (Matrix.updateRow_ne hi) j.val
  rw [Matrix.adjugate_apply]
  change T.det = _
  have hdet := Matrix.twoBlockTriangular_det' T (fun i => i ∈ ({u} : Set V)) hcross
  have hp := congrArg₂ (fun a b : R => a * b) hsingle (congrArg Matrix.det hrest)
  exact hdet.trans (hp.trans (one_mul _))
#print axioms Paper7UnicyclicSchwenk.adjugate_diagonal_eq_complement

/-- A symmetric matrix needs only one adjugate entry in the two-row expansion. -/
theorem symmetric_edge_row_expansion {R V : Type*} [CommRing R] [Fintype V]
    [DecidableEq V] (M : Matrix V V R) (hM : M.IsSymm)
    (u v : V) (huv : u ≠ v) :
    ((M.updateRow u (M u + Pi.single v (-1))).updateRow v
      (M v + Pi.single u (-1))).det =
      M.det - (M.submatrix
        (fun x : {x : V // x ∉ ({u, v} : Set V)} => x.val)
        (fun x : {x : V // x ∉ ({u, v} : Set V)} => x.val)).det -
      2 * M.adjugate v u := by
  rw [det_two_row_add M u v huv, det_single_negative_row,
    det_single_negative_row, det_two_forced_rows M u v huv]
  rw [hM.adjugate.apply v u]
  ring
#print axioms Paper7UnicyclicSchwenk.symmetric_edge_row_expansion

end Paper7UnicyclicSchwenk
