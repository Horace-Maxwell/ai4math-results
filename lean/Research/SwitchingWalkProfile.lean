import Mathlib

/-!
# Switching conjecture for main eigenvalues: a closed-walk-profile criterion

Setting (arXiv:2609.27046, Conjecture 1.1; Akbari–França–Ghasemian–Javarsineh–de Lima 2021):
for a graph `G` with adjacency matrix `A` and a switching `s ∈ {±1}^n`, the signed graph
`G^s` has adjacency matrix `D_s A D_s`; an eigenvalue is *main* if some eigenvector is not
orthogonal to the all-ones vector.

We prove, for any real symmetric matrix `A` with constant row sums `k` (e.g. the adjacency
matrix of a `k`-regular graph) on an index type of size `≠ 2`:

if the closed-walk counts at a vertex `v` are a strictly positive combination of the
closed-walk counts at all vertices, simultaneously for every length `j`
(`(A^j) v v = ∑ u, w u * (A^j) u u` with all `w u > 0`), then switching at the single vertex
`v` (i.e. `s = 1 - 2 e_v`) makes every eigenvalue main.

Walk-regular graphs are the special case `w u = 1/n`.

Main results:
* `SwitchingWalkProfile.annihilator` : every real polynomial `f` with `f(A) s = 0` has `f(A) = 0`;
* `SwitchingWalkProfile.eigen_nonorth` : every eigenvalue `θ` of `A` has an eigenvector `y`
  with `s ⬝ y ≠ 0`;
* `SwitchingWalkProfile.main_after_switching` : for `B = D_s A D_s`, every eigenvalue `θ` of `B`
  has an eigenvector `z` with `1 ⬝ z ≠ 0` (all eigenvalues of the switched matrix are main).
-/

set_option autoImplicit false

open Matrix Polynomial

namespace SwitchingWalkProfile

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The switching vector `s_v = 1 - 2 e_v`. -/
def switchVec (v : ι) : ι → ℝ := fun i => if i = v then -1 else 1

/-- Polynomial evaluation along an eigenvector. -/
lemma aeval_mulVec_of_eigen (A : Matrix ι ι ℝ) (θ : ℝ) (x : ι → ℝ)
    (hx : A *ᵥ x = θ • x) (p : ℝ[X]) : (aeval A p) *ᵥ x = (p.eval θ) • x := by
  have hpow : ∀ j : ℕ, (A ^ j) *ᵥ x = (θ ^ j) • x := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      rw [pow_succ, ← mulVec_mulVec, hx, mulVec_smul, ih, smul_smul, pow_succ, mul_comm]
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add, add_mulVec, hp, hq, eval_add, add_smul]
  | monomial j c =>
    rw [aeval_monomial, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul, smul_mulVec,
      hpow, smul_smul, eval_monomial]

/-- A profile identity at `v` for all powers extends to all polynomials. -/
lemma diag_aeval_profile (A : Matrix ι ι ℝ) (v : ι) (w : ι → ℝ)
    (hprof : ∀ j : ℕ, (A ^ j) v v = ∑ u, w u * (A ^ j) u u) (p : ℝ[X]) :
    (aeval A p) v v = ∑ u, w u * (aeval A p) u u := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [map_add, Matrix.add_apply, hp, hq, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro u _
    rw [Matrix.add_apply, mul_add]
  | monomial j c =>
    simp only [aeval_monomial, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul,
      Matrix.smul_apply, smul_eq_mul, hprof j, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro u _
    ring

/-- `f(A)` is symmetric when `A` is. -/
lemma aeval_transpose_of_symm (A : Matrix ι ι ℝ) (hA : Aᵀ = A) (p : ℝ[X]) :
    (aeval A p)ᵀ = aeval A p := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add, Matrix.transpose_add, hp, hq]
  | monomial j c =>
    rw [aeval_monomial, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul,
      Matrix.transpose_smul, Matrix.transpose_pow, hA]

/-- **Annihilator form.** If `A` is real symmetric with constant row sums, the index set does
not have exactly two elements, and the closed-walk counts at `v` are a strictly positive
combination of those at all vertices (for every length), then every polynomial annihilating
`s_v = 1 - 2 e_v` annihilates `A`. -/
theorem annihilator (A : Matrix ι ι ℝ) (hA : Aᵀ = A) (k : ℝ)
    (hk : A *ᵥ (fun _ => (1 : ℝ)) = k • (fun _ => (1 : ℝ)))
    (hn : Fintype.card ι ≠ 2) (v : ι) (w : ι → ℝ) (hw : ∀ u, 0 < w u)
    (hprof : ∀ j : ℕ, (A ^ j) v v = ∑ u, w u * (A ^ j) u u)
    (f : ℝ[X]) (hf : (aeval A f) *ᵥ switchVec v = 0) : aeval A f = 0 := by
  set M := aeval A f with hM
  have hMT : Mᵀ = M := aeval_transpose_of_symm A hA f
  have hsym : ∀ i j, M i j = M j i := by
    intro i j
    have h := congrFun (congrFun hMT j) i
    rw [Matrix.transpose_apply] at h
    exact h
  have h1 : M *ᵥ (fun _ => (1 : ℝ)) = (f.eval k) • (fun _ => (1 : ℝ)) :=
    aeval_mulVec_of_eigen A k _ hk f
  have hs : switchVec v = (fun _ => (1 : ℝ)) - (2 : ℝ) • Pi.single v (1 : ℝ) := by
    funext i
    by_cases h : i = v
    · subst h; simp [switchVec]; norm_num
    · simp [switchVec, h]
  have key : (f.eval k) • (fun _ => (1 : ℝ)) = (2 : ℝ) • M.col v := by
    have h2 := hf
    rw [hs, mulVec_sub, mulVec_smul, h1, mulVec_single_one, sub_eq_zero] at h2
    exact h2
  have hsumcol : ∑ i, M i v = f.eval k := by
    have h3 : (M *ᵥ (fun _ => (1 : ℝ))) v = f.eval k := by
      rw [h1]; simp
    rw [← h3]
    simp only [mulVec, dotProduct, mul_one]
    exact Finset.sum_congr rfl (fun i _ => hsym i v)
  have hfk : f.eval k = 0 := by
    have h4 := congrArg (fun g : ι → ℝ => ∑ i, g i) key
    simp only [Pi.smul_apply, smul_eq_mul, mul_one, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, Matrix.col_apply] at h4
    rw [← Finset.mul_sum, hsumcol] at h4
    have hc : (Fintype.card ι : ℝ) ≠ 2 := by exact_mod_cast hn
    have h5 : ((Fintype.card ι : ℝ) - 2) * f.eval k = 0 := by linarith
    rcases mul_eq_zero.1 h5 with h | h
    · exact absurd (by linarith : (Fintype.card ι : ℝ) = 2) hc
    · exact h
  have hcolzero : ∀ i, M i v = 0 := by
    intro i
    have h6 := congrFun key i
    simp only [hfk, Pi.smul_apply, Matrix.col_apply, smul_eq_mul] at h6
    linarith
  have hsq : ∀ u, (M * M) u u = ∑ i, (M i u) ^ 2 := by
    intro u
    rw [Matrix.mul_apply]
    apply Finset.sum_congr rfl
    intro i _
    rw [sq, hsym u i]
  have hvv : (M * M) v v = 0 := by
    rw [hsq]; simp [hcolzero]
  have hprofM : (M * M) v v = ∑ u, w u * (M * M) u u := by
    have h7 := diag_aeval_profile A v w hprof (f * f)
    rw [map_mul] at h7
    exact h7
  have hnonneg : ∀ u, 0 ≤ (M * M) u u := by
    intro u; rw [hsq]; positivity
  have hall : ∀ u, (M * M) u u = 0 := by
    have hsum0 : ∑ u, w u * (M * M) u u = 0 := by rw [← hprofM, hvv]
    have h8 := (Finset.sum_eq_zero_iff_of_nonneg
      (fun u _ => mul_nonneg (hw u).le (hnonneg u))).1 hsum0
    intro u
    rcases mul_eq_zero.1 (h8 u (Finset.mem_univ u)) with h' | h'
    · exact absurd h' (hw u).ne'
    · exact h'
  funext i u
  have h9 := hall u
  rw [hsq] at h9
  have h10 := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg (M i u))).1 h9 i
    (Finset.mem_univ i)
  simpa using h10

/-- **Eigenvector form.** Under the same hypotheses, every eigenvalue `θ` of `A` has an
eigenvector `y` with `s_v ⬝ y ≠ 0`, i.e. no eigenspace of `A` is orthogonal to `s_v`. -/
theorem eigen_nonorth (A : Matrix ι ι ℝ) (hA : Aᵀ = A) (k : ℝ)
    (hk : A *ᵥ (fun _ => (1 : ℝ)) = k • (fun _ => (1 : ℝ)))
    (hn : Fintype.card ι ≠ 2) (v : ι) (w : ι → ℝ) (hw : ∀ u, 0 < w u)
    (hprof : ∀ j : ℕ, (A ^ j) v v = ∑ u, w u * (A ^ j) u u)
    (θ : ℝ) (x : ι → ℝ) (hx0 : x ≠ 0) (hx : A *ᵥ x = θ • x) :
    ∃ y : ι → ℝ, A *ᵥ y = θ • y ∧ switchVec v ⬝ᵥ y ≠ 0 := by
  have hint : IsIntegral ℝ A := Matrix.isIntegral A
  have hμ : aeval A (minpoly ℝ A) = 0 := minpoly.aeval ℝ A
  have hroot : (minpoly ℝ A).IsRoot θ := by
    have h1 := aeval_mulVec_of_eigen A θ x hx (minpoly ℝ A)
    rw [hμ, zero_mulVec] at h1
    by_contra h
    apply hx0
    have h' : (minpoly ℝ A).eval θ ≠ 0 := h
    have h2 := congrArg (fun z => ((minpoly ℝ A).eval θ)⁻¹ • z) h1
    simp only [smul_zero, smul_smul, inv_mul_cancel₀ h', one_smul] at h2
    exact h2.symm
  set q := minpoly ℝ A /ₘ (X - C θ) with hqdef
  have hfac : (X - C θ) * q = minpoly ℝ A := mul_divByMonic_eq_iff_isRoot.2 hroot
  have hqmonic : q.Monic :=
    (monic_X_sub_C θ).of_mul_monic_left (by rw [hfac]; exact minpoly.monic hint)
  have hq : aeval A q ≠ 0 := by
    apply minpoly.aeval_ne_zero_of_dvdNotUnit_minpoly hint hqmonic
    exact ⟨hqmonic.ne_zero, X - C θ, not_isUnit_X_sub_C θ, by rw [mul_comm, hfac]⟩
  set Q := aeval A q with hQ
  set s := switchVec v with hsdef
  refine ⟨Q *ᵥ s, ?_, ?_⟩
  · -- `A Q = θ Q` because `(A - θ) Q = minpoly(A) = 0`
    have h3 : A * Q = θ • Q := by
      have h4 := congrArg (aeval A) hfac
      rw [hμ, map_mul, map_sub, aeval_X, aeval_C, sub_mul,
        Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul, sub_eq_zero] at h4
      exact h4
    rw [mulVec_mulVec, h3, smul_mulVec]
  · intro hdot
    have hy0 : Q *ᵥ s ≠ 0 := by
      intro h0
      exact hq (annihilator A hA k hk hn v w hw hprof q h0)
    apply hy0
    have hQT : Qᵀ = Q := aeval_transpose_of_symm A hA q
    have heig : A *ᵥ (Q *ᵥ s) = θ • (Q *ᵥ s) := by
      have h3 : A * Q = θ • Q := by
        have h4 := congrArg (aeval A) hfac
        rw [hμ, map_mul, map_sub, aeval_X, aeval_C, sub_mul,
          Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul, sub_eq_zero] at h4
        exact h4
      rw [mulVec_mulVec, h3, smul_mulVec]
    have hQy : Q *ᵥ (Q *ᵥ s) = (q.eval θ) • (Q *ᵥ s) :=
      aeval_mulVec_of_eigen A θ _ heig q
    have hself : (Q *ᵥ s) ⬝ᵥ (Q *ᵥ s) = 0 := by
      calc (Q *ᵥ s) ⬝ᵥ (Q *ᵥ s) = ((Q *ᵥ s) ᵥ* Q) ⬝ᵥ s := dotProduct_mulVec _ _ _
        _ = (Qᵀ *ᵥ (Q *ᵥ s)) ⬝ᵥ s := by rw [mulVec_transpose]
        _ = (Q *ᵥ (Q *ᵥ s)) ⬝ᵥ s := by rw [hQT]
        _ = (q.eval θ) * (s ⬝ᵥ (Q *ᵥ s)) := by
          rw [hQy, smul_dotProduct, smul_eq_mul, dotProduct_comm]
        _ = 0 := by rw [hdot, mul_zero]
    exact dotProduct_self_eq_zero.1 hself

/-- **Signed-graph form.** With `D = diag(s_v)` and `B = D A D` (the switched matrix), every
eigenvalue of `B` is main: it has an eigenvector not orthogonal to the all-ones vector. -/
theorem main_after_switching (A : Matrix ι ι ℝ) (hA : Aᵀ = A) (k : ℝ)
    (hk : A *ᵥ (fun _ => (1 : ℝ)) = k • (fun _ => (1 : ℝ)))
    (hn : Fintype.card ι ≠ 2) (v : ι) (w : ι → ℝ) (hw : ∀ u, 0 < w u)
    (hprof : ∀ j : ℕ, (A ^ j) v v = ∑ u, w u * (A ^ j) u u)
    (θ : ℝ) (x : ι → ℝ) (hx0 : x ≠ 0)
    (hx : (diagonal (switchVec v) * A * diagonal (switchVec v)) *ᵥ x = θ • x) :
    ∃ z : ι → ℝ, (diagonal (switchVec v) * A * diagonal (switchVec v)) *ᵥ z = θ • z ∧
      (fun _ => (1 : ℝ)) ⬝ᵥ z ≠ 0 := by
  set D := diagonal (switchVec v) with hD
  have hDD : D * D = 1 := by
    rw [hD, diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext i
    by_cases h : i = v <;> simp [switchVec, h]
  -- `D x` is a `θ`-eigenvector of `A`
  have hx' : A *ᵥ (D *ᵥ x) = θ • (D *ᵥ x) := by
    have h1 := congrArg (fun z => D *ᵥ z) hx
    simp only [mulVec_mulVec, mulVec_smul] at h1
    rw [← mul_assoc, ← mul_assoc, hDD, one_mul] at h1
    rw [mulVec_mulVec]
    exact h1
  have hDx0 : D *ᵥ x ≠ 0 := by
    intro h0
    apply hx0
    have h1 := congrArg (fun z => D *ᵥ z) h0
    simp only [mulVec_mulVec, hDD, one_mulVec, mulVec_zero] at h1
    exact h1
  obtain ⟨y, hyA, hys⟩ := eigen_nonorth A hA k hk hn v w hw hprof θ (D *ᵥ x) hDx0 hx'
  refine ⟨D *ᵥ y, ?_, ?_⟩
  · rw [mulVec_mulVec, mul_assoc, mul_assoc, hDD, mul_one, ← mulVec_mulVec, hyA, mulVec_smul]
  · have h2 : (fun _ => (1 : ℝ)) ⬝ᵥ (D *ᵥ y) = switchVec v ⬝ᵥ y := by
      simp only [hD, dotProduct, mulVec_diagonal, one_mul]
    rw [h2]
    exact hys

/-- Walk-regular special case: if all powers of `A` have constant diagonal, every vertex works. -/
theorem walkRegular_main_after_switching (A : Matrix ι ι ℝ) (hA : Aᵀ = A) (k : ℝ)
    (hk : A *ᵥ (fun _ => (1 : ℝ)) = k • (fun _ => (1 : ℝ)))
    (hn : Fintype.card ι ≠ 2) (hwr : ∀ (j : ℕ) (u u' : ι), (A ^ j) u u = (A ^ j) u' u')
    (v : ι) (θ : ℝ) (x : ι → ℝ) (hx0 : x ≠ 0)
    (hx : (diagonal (switchVec v) * A * diagonal (switchVec v)) *ᵥ x = θ • x) :
    ∃ z : ι → ℝ, (diagonal (switchVec v) * A * diagonal (switchVec v)) *ᵥ z = θ • z ∧
      (fun _ => (1 : ℝ)) ⬝ᵥ z ≠ 0 := by
  have hcard : (0 : ℝ) < Fintype.card ι := by
    have : Nonempty ι := ⟨v⟩
    exact_mod_cast Fintype.card_pos
  refine main_after_switching A hA k hk hn v (fun _ => 1 / (Fintype.card ι : ℝ))
    (fun _ => by positivity) ?_ θ x hx0 hx
  intro j
  simp only [hwr j _ v, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  field_simp

end SwitchingWalkProfile

#print axioms SwitchingWalkProfile.annihilator
#print axioms SwitchingWalkProfile.eigen_nonorth
#print axioms SwitchingWalkProfile.main_after_switching
#print axioms SwitchingWalkProfile.walkRegular_main_after_switching
