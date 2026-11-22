import Research.TaskS.C.Challenge

namespace TaskS.C
open Challenge
open scoped BigOperators

private theorem facet_det {n : ℕ} (z b : Space (n+1)) (w : Fin n → Space (n+1)) :
    |(Matrix.of (Fin.cons (Fin.cons (0 : ℝ) z) (Fin.cons (Fin.cons 1 b)
      (fun j => Fin.cons 1 (w j))))).det| =
    |(Matrix.of (Fin.cons z (fun j => w j - b))).det| := by
  let A : Matrix (Fin (n+2)) (Fin (n+2)) ℝ := Matrix.of
    (Fin.cons (Fin.cons 0 z) (Fin.cons (Fin.cons 1 b) (fun j => Fin.cons 1 (w j))))
  let T : Matrix (Fin (n+2)) (Fin (n+2)) ℝ := Matrix.of
    (Fin.cons (Fin.cons 0 z) (Fin.cons (Fin.cons 1 b) (fun j => Fin.cons 0 (w j - b))))
  let k := (0 : Fin (n+1)).succ
  let c : Fin (n+2) → ℝ := Fin.cons 0 (Fin.cons 0 (fun _ => -1))
  have ht : T.det = A.det := by
    apply Matrix.det_eq_of_forall_row_eq_smul_add_const c k (by simp [c,k])
    intro i j
    refine Fin.cases ?_ (fun i => Fin.cases ?_ (fun l => ?_) i) i
    · simp [T,A,c,k]
    · simp [T,A,c,k]
    · refine Fin.cases ?_ (fun l' => ?_) j <;> simp [T,A,c,k,sub_eq_add_neg]
  have hm : T.submatrix k.succAbove Fin.succ = Matrix.of (Fin.cons z (fun j => w j - b)) := by
    ext i j
    refine Fin.cases ?_ (fun l => ?_) i <;> simp [Matrix.submatrix_apply,T,k]
  have hd : T.det = -(T.submatrix k.succAbove Fin.succ).det := by
    rw [Matrix.det_succ_column_zero]
    simp [Fin.sum_univ_succ,T,k]
  change |A.det| = _
  rw [← ht, hd, abs_neg, hm]

private theorem updated_facet {n : ℕ} (v : Fin (n+2) → Space (n+1)) (i : Fin (n+2))
    (z : Space (n+1)) :
    |((Matrix.of fun j => Fin.cons (1 : ℝ) (v j)).updateRow i (Fin.cons 0 z)).det| =
    |(Matrix.of (Fin.cons z (fun k : Fin n => v (i.succAbove k.succ) - v (i.succAbove 0)))).det| := by
  let A := (Matrix.of fun j => Fin.cons (1 : ℝ) (v j)).updateRow i (Fin.cons 0 z)
  let e := (finSuccEquiv (n+1)).trans (finSuccEquiv' i).symm
  have hone : finSuccEquiv (n+1) (1 : Fin (n+2)) = some 0 := finSuccEquiv_succ 0
  have h : A.submatrix e (Equiv.refl _) = Matrix.of (Fin.cons (Fin.cons 0 z)
        (Fin.cons (Fin.cons 1 (v (i.succAbove 0)))
        (fun k => Fin.cons 1 (v (i.succAbove k.succ))))) := by
    ext j l
    refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun k => ?_) j) j <;>
      simp [A,e,Matrix.submatrix_apply,Matrix.updateRow_apply,Fin.succAbove_ne,hone]
  change |A.det| = _
  rw [← Matrix.abs_det_submatrix_equiv_equiv e (Equiv.refl _) A, h]
  exact facet_det z _ _

/-- Determinantal base-times-height identity for a simplex whose origin has barycentric
coordinates β. The primitive ray gives the quotient-lattice volume normalization. -/
theorem projected_eq {n : ℕ} (u : Fin (n+2) → Challenge.Lattice (n+1)) (ω β : Fin (n+2) → ℝ)
    (hω : ∀ i, 0 < ω i) (hβ : ∀ i, 0 < β i) (hs : ∑ i, β i = 1)
    (hz : ∑ i, β i • vertices u ω i = 0) (i : Fin (n+2)) :
    projectedVolume (vertices u ω) u i = volume (vertices u ω) * ((1 - β i) / ω i) := by
  let v := vertices u ω
  let A : Matrix (Fin (n+2)) (Fin (n+2)) ℝ := Matrix.of fun j => Fin.cons 1 (v j)
  have hrow : (∑ j, β j • A j) = Fin.cons (1 : ℝ) (0 : Space (n+1)) := by
    funext k
    refine Fin.cases ?_ (fun l => ?_) k
    · simpa [A, Finset.sum_apply] using hs
    · simpa [A, Finset.sum_apply,v] using congrFun hz l
  let z : Space (n+2) := Fin.cons (0 : ℝ) (embed (u i))
  have he : A i = ω i • z + ∑ j, β j • A j := by
    rw [hrow]; funext k
    refine Fin.cases ?_ (fun l => ?_) k <;> simp [A,v,z,vertices]
  have hd : A.det = ω i * (A.updateRow i z).det + β i * A.det := by
    calc
      A.det = (A.updateRow i (ω i • z + ∑ j, β j • A j)).det := by rw [← he, Matrix.updateRow_eq_self]
      _ = _ := by rw [Matrix.det_updateRow_add, Matrix.det_updateRow_smul, Matrix.det_updateRow_sum]; rfl
  have hi : β i ≤ 1 := hs ▸ Finset.single_le_sum (fun j _ => (hβ j).le) (Finset.mem_univ i)
  have hu : (A.updateRow i z).det = A.det * ((1 - β i) / ω i) := by
    field_simp [ne_of_gt (hω i)]; nlinarith
  change _ = |A.det| * _
  rw [← abs_of_nonneg (div_nonneg (sub_nonneg.mpr hi) (hω i).le), ← abs_mul, ← hu]
  exact (updated_facet v i (embed (u i))).symm

end TaskS.C
