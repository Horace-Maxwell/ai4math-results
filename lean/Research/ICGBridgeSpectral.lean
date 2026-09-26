import Mathlib

/-!
# Spectral bridge, part 1: spectrum of circulant matrices over `ZMod N`

For `f : ZMod N → ℂ` the circulant matrix `Matrix.circulant f` (entries `f (i - j)`) satisfies
`circulant f * W = W * diagonal (𝓕 f)` where `W i k = stdAddChar (i * k)` is the (unnormalised)
DFT matrix and `𝓕 = ZMod.dft`.  Since `W` is invertible, the characteristic polynomial of
`circulant f` is `∏ k, (X - C (𝓕 f k))`.

Consequently, for any real symmetric matrix `A` indexed by a type `ι ≃ ZMod N` whose entries are
`A i j = f (e i - e j)` with `f : ZMod N → ℝ`, the multiset of (Hermitian) eigenvalues of `A`
coincides (after coercion to `ℂ`) with the multiset `{𝓕 f k | k : ZMod N}`; in particular
`∑ i, |eigenvalue i| = ∑ k, ‖𝓕 f k‖`  (`sum_abs_eigenvalues_eq_sum_norm_dft`).

Everything here is for general `N`; no arithmetic of `N` is used.
-/

namespace ICGBridge

open Matrix Polynomial ZMod Finset

variable {N : ℕ} [NeZero N]

/-- Unnormalised DFT matrix `W i k = ψ(i k)`, `ψ = ZMod.stdAddChar`. -/
noncomputable def dftMat (N : ℕ) [NeZero N] : Matrix (ZMod N) (ZMod N) ℂ :=
  Matrix.of fun i k => stdAddChar (i * k)

/-- Its inverse `N⁻¹ ψ(-k j)`. -/
noncomputable def idftMat (N : ℕ) [NeZero N] : Matrix (ZMod N) (ZMod N) ℂ :=
  Matrix.of fun k j => (N : ℂ)⁻¹ * stdAddChar (-(k * j))

lemma sum_stdAddChar_mul (t : ZMod N) :
    ∑ i : ZMod N, stdAddChar (t * i) = if t = 0 then (N : ℂ) else 0 := by
  split_ifs with h
  · simp [h]
  · exact AddChar.sum_eq_zero_of_ne_one (isPrimitive_stdAddChar N h)

lemma dftMat_mul_idftMat : dftMat N * idftMat N = 1 := by
  ext i j
  simp only [dftMat, idftMat, Matrix.mul_apply, Matrix.of_apply, Matrix.one_apply]
  have h : ∀ k : ZMod N, stdAddChar (i * k) * ((N : ℂ)⁻¹ * stdAddChar (-(k * j))) =
      (N : ℂ)⁻¹ * stdAddChar ((i - j) * k) := by
    intro k
    rw [mul_left_comm, ← AddChar.map_add_eq_mul]
    congr 2
    ring
  simp_rw [h, ← Finset.mul_sum, sum_stdAddChar_mul, sub_eq_zero]
  split_ifs
  · exact inv_mul_cancel₀ (by exact_mod_cast NeZero.ne N)
  · simp

lemma idftMat_mul_dftMat : idftMat N * dftMat N = 1 :=
  mul_eq_one_comm.mp dftMat_mul_idftMat

/-- Circulant matrices are diagonalised by the DFT matrix. -/
lemma circulant_mul_dftMat (f : ZMod N → ℂ) :
    circulant f * dftMat N = dftMat N * diagonal (𝓕 f) := by
  ext i k
  rw [Matrix.mul_diagonal]
  simp only [Matrix.mul_apply, circulant_apply, dftMat, Matrix.of_apply, dft_apply, smul_eq_mul,
    Finset.mul_sum]
  refine Fintype.sum_equiv (Equiv.subLeft i) _ _ ?_
  intro j
  simp only [Equiv.subLeft_apply]
  rw [← mul_assoc, ← AddChar.map_add_eq_mul, mul_comm (f (i - j))]
  congr 2
  ring

/-- Characteristic polynomial of a circulant matrix over `ZMod N`. -/
theorem charpoly_circulant (f : ZMod N → ℂ) :
    (circulant f).charpoly = ∏ k, (X - C (𝓕 f k)) := by
  have h1 : circulant f = dftMat N * (diagonal (𝓕 f) * idftMat N) := by
    calc circulant f = circulant f * (dftMat N * idftMat N) := by
          rw [dftMat_mul_idftMat, Matrix.mul_one]
      _ = (circulant f * dftMat N) * idftMat N := by rw [Matrix.mul_assoc]
      _ = _ := by rw [circulant_mul_dftMat, Matrix.mul_assoc]
  rw [h1, charpoly_mul_comm, Matrix.mul_assoc, idftMat_mul_dftMat, Matrix.mul_one,
    charpoly_diagonal]

lemma roots_prod_X_sub_C_univ {ι : Type*} [Fintype ι] (g : ι → ℂ) :
    (∏ i, (X - C (g i))).roots = Finset.univ.val.map g := by
  rw [Finset.prod_eq_multiset_prod]
  have : (fun i => X - C (g i)) = (fun a => X - C a) ∘ g := rfl
  rw [this, ← Multiset.map_map, Polynomial.roots_multiset_prod_X_sub_C]

/-- **Spectral bridge.** For a real symmetric (Hermitian) matrix whose entries are given by a
function of the difference of the indices in `ZMod N`, the eigenvalue multiset (coerced to `ℂ`)
is the multiset of DFT values. -/
theorem eigenvalues_multiset_eq_dft {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (hA : A.IsHermitian) (e : ι ≃ ZMod N) (f : ZMod N → ℝ)
    (hAf : ∀ i j, A i j = f (e i - e j)) :
    Finset.univ.val.map (fun i => (hA.eigenvalues i : ℂ)) =
      Finset.univ.val.map (𝓕 (fun s => (f s : ℂ))) := by
  set F : ZMod N → ℂ := fun s => (f s : ℂ) with hF
  have hcp : (A.map (algebraMap ℝ ℂ)).charpoly = ∏ i, (X - C ((hA.eigenvalues i : ℂ))) := by
    have := charpoly_map A (algebraMap ℝ ℂ)
    rw [this, hA.charpoly_eq, Polynomial.map_prod]
    simp
  have hre : A.map (algebraMap ℝ ℂ) = reindex e.symm e.symm (circulant F) := by
    ext i j
    simp [hAf, hF, circulant_apply]
  have hcp2 : (A.map (algebraMap ℝ ℂ)).charpoly = ∏ k, (X - C (𝓕 F k)) := by
    rw [hre, charpoly_reindex, charpoly_circulant]
  have h := congrArg Polynomial.roots (hcp.symm.trans hcp2)
  rwa [roots_prod_X_sub_C_univ, roots_prod_X_sub_C_univ] at h

/-- **Energy form of the spectral bridge.** -/
theorem sum_abs_eigenvalues_eq_sum_norm_dft {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (hA : A.IsHermitian) (e : ι ≃ ZMod N) (f : ZMod N → ℝ)
    (hAf : ∀ i j, A i j = f (e i - e j)) :
    ∑ i, |hA.eigenvalues i| = ∑ k, ‖𝓕 (fun s => (f s : ℂ)) k‖ := by
  have h := congrArg (fun m : Multiset ℂ => (m.map (fun z => ‖z‖)).sum)
    (eigenvalues_multiset_eq_dft A hA e f hAf)
  simp only [Multiset.map_map, Function.comp_def] at h
  have h1 : ∑ i, |hA.eigenvalues i| = ∑ i, ‖(hA.eigenvalues i : ℂ)‖ := by
    simp [Complex.norm_real]
  rw [h1, Finset.sum_eq_multiset_sum, Finset.sum_eq_multiset_sum]
  exact h

end ICGBridge

#print axioms ICGBridge.sum_abs_eigenvalues_eq_sum_norm_dft
