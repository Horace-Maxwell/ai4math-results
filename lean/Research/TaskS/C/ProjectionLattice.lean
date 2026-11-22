import Research.TaskS.C.Challenge

namespace TaskS.C.ProjectionLattice
open Challenge
open scoped BigOperators Matrix
open Module

private noncomputable def split {n : ℕ} (u : Challenge.Lattice (n+1))
    (f : Challenge.Lattice (n+1) →ₗ[ℤ] ℤ) (hf : f u = 1) :
    Challenge.Lattice (n+1) ≃ₗ[ℤ] (ℤ × LinearMap.ker f) where
  toFun x := (f x, ⟨x - f x • u, by rw [LinearMap.mem_ker,map_sub,map_smul,hf,smul_eq_mul,mul_one,sub_self]⟩)
  invFun p := p.1 • u + p.2.val
  left_inv x := by simp
  right_inv := by
    rintro ⟨a,y⟩
    have hy := LinearMap.mem_ker.mp y.property
    have hz : f (a • u + y.val) = a := by rw [map_add,map_smul,hf,hy,add_zero,smul_eq_mul,mul_one]
    ext1
    · exact hz
    · apply Subtype.ext
      change a • u + y.val - f (a • u + y.val) • u = y.val
      rw [hz]
      abel
  map_add' x y := by
    ext1
    · simp
    · apply Subtype.ext
      simp [add_smul,sub_add_sub_comm]
  map_smul' k x := by
    ext1
    · exact f.map_smul k x
    · apply Subtype.ext
      change k • x - f (k • x) • u = k • (x - f x • u)
      rw [map_smul,smul_sub,smul_smul]
      rfl

private def join (n : ℕ) : (ℤ × Challenge.Lattice n) ≃ₗ[ℤ] Challenge.Lattice (n+1) where
  toFun p := Fin.cons p.1 p.2
  invFun x := (x 0, Fin.tail x)
  left_inv p := by simp
  right_inv x := by simp
  map_add' x y := by ext k; refine Fin.cases ?_ (fun j => ?_) k <;> rfl
  map_smul' k x := by ext j; refine Fin.cases ?_ (fun j => ?_) j <;> rfl

/-- A primitive direction admits an integral change of coordinates carrying it to the first
standard vector, with determinant of absolute value one. -/
theorem exists_adapted {n : ℕ} (u : Challenge.Lattice (n+1)) (hu : Primitive u) :
    ∃ A : Matrix (Fin (n+1)) (Fin (n+1)) ℤ,
      |A.det| = 1 ∧ A.mulVec u = Pi.single 0 1 := by
  classical
  obtain ⟨a, ha⟩ := hu
  let f : Challenge.Lattice (n+1) →ₗ[ℤ] ℤ := ∑ k, a k • LinearMap.proj k
  have hf : f u = 1 := by simpa [f,LinearMap.sum_apply] using ha
  let e := split u f hf
  have hr := e.finrank_eq
  simp only [Module.finrank_prod, Module.finrank_self, finrank_fintype_fun_eq_card,
    Fintype.card_fin] at hr
  have hn : finrank ℤ (LinearMap.ker f) = n := by omega
  let b := Module.finBasisOfFinrankEq ℤ (LinearMap.ker f) hn
  let E := e.trans (((LinearEquiv.refl ℤ ℤ).prodCongr b.equivFun).trans (join n))
  have hEu : E u = Pi.single 0 1 := by
    have he : e u = (1,0) := by ext1 <;> simp [e,split,hf]
    change join n ((LinearEquiv.refl ℤ ℤ).prodCongr b.equivFun (e u)) = _
    rw [he]
    ext j
    refine Fin.cases ?_ (fun j => ?_) j <;> simp [join]
  refine ⟨LinearMap.toMatrix' E.toLinearMap, ?_, ?_⟩
  · rw [LinearMap.det_toMatrix', ← Int.isUnit_iff_abs_eq]
    exact E.isUnit_det'
  · rwa [LinearMap.toMatrix'_mulVec]

/-- Laplace expansion in any adapted unimodular coordinates identifies the ambient
determinant with the normalized edge determinant in the quotient lattice. -/
theorem edge_determinant {n : ℕ} (u : Challenge.Lattice (n+1)) (edges : Fin n → Space (n+1))
    (A : Matrix (Fin (n+1)) (Fin (n+1)) ℤ) (hdet : |A.det| = 1)
    (hu : A.mulVec u = Pi.single 0 1) :
    |(Matrix.of (Fin.cons (embed u) edges)).det| =
    |(Matrix.of fun k j : Fin n => ((A.map fun z => (z : ℝ)).mulVec (edges k)) j.succ).det| := by
  classical
  let B := A.map fun z => (z : ℝ)
  let M := Matrix.of (Fin.cons (embed u) edges)
  let D := M * B.transpose
  have hB : |B.det| = 1 := by
    change |(A.map fun z => (z : ℝ)).det| = 1
    rw [← Int.cast_det]
    exact_mod_cast hdet
  have hd : |D.det| = |M.det| := by
    simp only [D, Matrix.det_mul, Matrix.det_transpose, abs_mul, hB, mul_one]
  have row0 (j : Fin (n+1)) : D 0 j = (Pi.single 0 1 : Space (n+1)) j := by
    have h := congrFun hu j
    simp only [Matrix.mulVec, dotProduct, Pi.single_apply] at h
    change (∑ k, (u k : ℝ) * (A j k : ℝ)) = _
    simp only [Pi.single_apply]
    simp_rw [mul_comm (u _ : ℝ)]
    exact_mod_cast h
  have rows (k j : Fin n) : D k.succ j.succ = B.mulVec (edges k) j.succ := by
    change (∑ l, edges k l * (A j.succ l : ℝ)) = ∑ l, (A j.succ l : ℝ) * edges k l
    simp_rw [mul_comm (edges k _)]
  have hsub : D.submatrix Fin.succ Fin.succ = Matrix.of
      (fun k j : Fin n => B.mulVec (edges k) j.succ) := Matrix.ext rows
  change |M.det| = _
  rw [← hd, Matrix.det_succ_row_zero]
  simp [row0, Pi.single_apply, hsub, B]

/-- In adapted lattice coordinates the frozen projected volume is the determinant of the
projected simplex's opposite-facet edges after dropping coordinate zero. -/
theorem projected_volume {n : ℕ} (v : Fin (n+2) → Space (n+1))
    (u : Fin (n+2) → Challenge.Lattice (n+1)) (i : Fin (n+2)) (hu : Primitive (u i)) :
    ∃ A : Matrix (Fin (n+1)) (Fin (n+1)) ℤ, |A.det| = 1 ∧
      A.mulVec (u i) = Pi.single 0 1 ∧ projectedVolume v u i =
        |(Matrix.of fun k j : Fin n => ((A.map fun z => (z : ℝ)).mulVec
          (v (i.succAbove k.succ) - v (i.succAbove 0))) j.succ).det| := by
  obtain ⟨A,hA,he⟩ := exists_adapted (u i) hu
  exact ⟨A,hA,he,edge_determinant _ _ A hA he⟩

#print axioms exists_adapted
#print axioms edge_determinant
#print axioms projected_volume

end TaskS.C.ProjectionLattice
