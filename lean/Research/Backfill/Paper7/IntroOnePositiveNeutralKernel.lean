import Research.Backfill.Paper7.BorderedPivotInertia
import Research.Backfill.Paper7.MatrixInertiaEmbeddings

/-! A neutral vector orthogonal for a symmetric form to a positive vector
lies in the kernel whenever the form has at most one positive direction. -/
set_option autoImplicit false
noncomputable section
open scoped Classical Matrix BigOperators

namespace Paper7IntroStrictCut
open Matrix BackfillPaper7.Challenge Paper7Inertia Paper7Comparison

theorem real_hermitian_bilinear_comm
    {V : Type} [Fintype V] [DecidableEq V]
    (M : Matrix V V ℝ) (hM : M.IsHermitian) (x y : V → ℝ) :
    x ⬝ᵥ M *ᵥ y = y ⬝ᵥ M *ᵥ x := by
  simpa only [star_trivial] using hM.star_dotProduct_mulVec_comm x y
#print axioms Paper7IntroStrictCut.real_hermitian_bilinear_comm

theorem rectangular_congruence_entry
    {V W : Type} [Fintype V] [Fintype W]
    (M : Matrix V V ℝ) (P : Matrix V W ℝ) (i j : W) :
    (Pᵀ * M * P) i j = P.col i ⬝ᵥ M *ᵥ P.col j := by
  rw [Matrix.mul_assoc, Matrix.mul_apply]
  rfl
#print axioms Paper7IntroStrictCut.rectangular_congruence_entry

theorem one_positive_neutral_orthogonal_kernel
    {V : Type} [Fintype V] [DecidableEq V]
    (M : Matrix V V ℝ) (hM : M.IsHermitian) (hpos : nPos M ≤ 1)
    (x y : V → ℝ) (hx : 0 < x ⬝ᵥ M *ᵥ x)
    (hy : y ⬝ᵥ M *ᵥ y = 0) (hxy : x ⬝ᵥ M *ᵥ y = 0) : M *ᵥ y = 0 := by
  by_contra hMy
  let z : V → ℝ := M *ᵥ y
  let a : ℝ := z ⬝ᵥ M *ᵥ x
  let b : ℝ := y ⬝ᵥ M *ᵥ z
  let c : ℝ := z ⬝ᵥ M *ᵥ z
  let d : ℝ := x ⬝ᵥ M *ᵥ x
  have hd : 0 < d := hx
  have hb : b ≠ 0 := by
    change y ⬝ᵥ M *ᵥ (M *ᵥ y) ≠ 0
    rw [real_hermitian_bilinear_comm M hM]
    exact fun h => hMy (dotProduct_self_eq_zero.mp h)
  have hyx : y ⬝ᵥ M *ᵥ x = 0 :=
    (real_hermitian_bilinear_comm M hM y x).trans hxy
  have hzy : z ⬝ᵥ M *ᵥ y = b :=
    real_hermitian_bilinear_comm M hM z y
  have hxz : x ⬝ᵥ M *ᵥ z = a :=
    real_hermitian_bilinear_comm M hM x z
  have hyne : y ≠ 0 := by
    intro h
    apply hMy
    rw [h, Matrix.mulVec_zero]
  let P : Matrix V (Fin 2 ⊕ Fin 1) ℝ := Matrix.of fun i j =>
    Sum.elim (fun k : Fin 2 => if k = 0 then y i else z i) (fun _ => x i) j
  have hPv (w : (Fin 2 ⊕ Fin 1) → ℝ) : P *ᵥ w =
      w (Sum.inl 0) • y + w (Sum.inl 1) • z + w (Sum.inr 0) • x := by
    funext i
    simp [P, Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Fin.sum_univ_succ,
      mul_comm]
  have hker (w : (Fin 2 ⊕ Fin 1) → ℝ) (hw : P *ᵥ w = 0) : w = 0 := by
    have he : w (Sum.inl 0) • y + w (Sum.inl 1) • z + w (Sum.inr 0) • x = 0 :=
      (hPv w).symm.trans hw
    have heY := congrArg (fun q : V → ℝ => y ⬝ᵥ M *ᵥ q) he
    simp only [Matrix.mulVec_add, Matrix.mulVec_smul, dotProduct_add, dotProduct_smul,
      smul_eq_mul, hy, hyx, Matrix.mulVec_zero, dotProduct_zero,
      mul_zero, zero_add, add_zero] at heY
    have hw1 : w (Sum.inl 1) = 0 := (mul_eq_zero.mp heY).resolve_right hb
    rw [hw1, zero_smul, add_zero] at he
    have heX := congrArg (fun q : V → ℝ => x ⬝ᵥ M *ᵥ q) he
    simp only [Matrix.mulVec_add, Matrix.mulVec_smul, dotProduct_add, dotProduct_smul,
      smul_eq_mul, hxy, Matrix.mulVec_zero, dotProduct_zero, mul_zero, zero_add] at heX
    have hw2 : w (Sum.inr 0) = 0 := (mul_eq_zero.mp heX).resolve_right (ne_of_gt hd)
    rw [hw2, zero_smul, add_zero] at he
    have hw0 : w (Sum.inl 0) = 0 := (smul_eq_zero.mp he).resolve_right hyne
    funext i
    rcases i with i | i
    · fin_cases i <;> assumption
    · fin_cases i
      exact hw2
  have hinj : Function.Injective P.mulVecLin := by
    intro w t h
    apply sub_eq_zero.mp
    apply hker
    change P *ᵥ (w - t) = 0
    rw [Matrix.mulVec_sub]
    change P *ᵥ w = P *ᵥ t at h
    rw [h, sub_self]
  have hblock : Pᵀ * M * P =
      Matrix.fromBlocks (zeroPivotBlock b c) (zeroPairCoupling (fun _ : Fin 1 => a))
        (zeroPairCoupling (fun _ : Fin 1 => a))ᵀ (singletonBlock d) := by
    ext i j
    rw [rectangular_congruence_entry]
    rcases i with i | i <;> rcases j with j | j
    · fin_cases i <;> fin_cases j
      · change y ⬝ᵥ M *ᵥ y = 0
        exact hy
      · change y ⬝ᵥ M *ᵥ z = b
        rfl
      · change z ⬝ᵥ M *ᵥ y = b
        exact hzy
      · change z ⬝ᵥ M *ᵥ z = c
        rfl
    · fin_cases i <;> fin_cases j
      · change y ⬝ᵥ M *ᵥ x = 0
        exact hyx
      · change z ⬝ᵥ M *ᵥ x = a
        rfl
    · fin_cases i; fin_cases j
      · change x ⬝ᵥ M *ᵥ y = 0
        exact hxy
      · change x ⬝ᵥ M *ᵥ z = a
        exact hxz
    · fin_cases i; fin_cases j
      change x ⬝ᵥ M *ᵥ x = d
      rfl
  have hD : (singletonBlock d).IsHermitian := by
    apply Matrix.IsHermitian.ext
    intro i j
    simp [singletonBlock]
  have htwo : nPos (Pᵀ * M * P) = 2 := by
    rw [hblock, (zeroPair_inertia b c (fun _ : Fin 1 => a) (singletonBlock d) hb hD).1,
      (singletonBlock_inertia d).1, ite_eq_left hd]
  have hPM : (Pᵀ * M * P).IsHermitian := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      Matrix.isHermitian_conjTranspose_mul_mul P hM
  have hmono := nPos_map_le (Pᵀ * M * P) M hPM hM P.mulVecLin hinj
    (fun w => (quadratic_rectangular_congruence M P w).le)
  rw [htwo] at hmono
  omega
#print axioms Paper7IntroStrictCut.one_positive_neutral_orthogonal_kernel

end Paper7IntroStrictCut
