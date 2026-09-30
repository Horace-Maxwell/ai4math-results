import Mathlib

/-!
# Paper 8 back-fill (agent `lin`): linear algebra under a change of field

Three facts used for Lemma 2.2 and Remark 8.2:
* the rank of a matrix does not change under a ring hom of fields `f : K →+* L` (square case from
  the transvection normal form `M = P · diagonal D · Q`, the general case for ordered fields from
  `rank (Mᵀ M) = rank M`);
* if a vector `α` over `K` is orthogonal to `ker_K N`, then `f α` is orthogonal to `ker_L (f N)`
  (`α = y ᵥ* N` by `LinearMap.range_dualMap_eq_dualAnnihilator_ker`);
* integer vectors whose reductions mod a prime `p` are linearly independent are linearly
  independent over `ℤ` (descent on `∑ |g_i|`), hence full column rank mod `p` gives full column
  rank over `ℚ`.
-/

set_option autoImplicit false

open Matrix

namespace P8Lin

section RankMap

variable {K L : Type*} [Field K] [Field L]

/-- The rank of a square matrix is unchanged under a ring hom of fields. -/
theorem rank_map_square {m : Type*} [Fintype m] [DecidableEq m] (f : K →+* L)
    (M : Matrix m m K) : (M.map f).rank = M.rank := by
  classical
  obtain ⟨L1, L2, D, hM⟩ := Matrix.Pivot.exists_list_transvec_mul_diagonal_mul_list_transvec M
  have hP : (L1.map TransvectionStruct.toMatrix).prod.det = 1 :=
    TransvectionStruct.det_toMatrix_prod L1
  have hQ : (L2.map TransvectionStruct.toMatrix).prod.det = 1 :=
    TransvectionStruct.det_toMatrix_prod L2
  have hPf : IsUnit ((L1.map TransvectionStruct.toMatrix).prod.map f).det := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, hP, map_one]
    exact isUnit_one
  have hQf : IsUnit ((L2.map TransvectionStruct.toMatrix).prod.map f).det := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, hQ, map_one]
    exact isUnit_one
  have hMf : M.map f = (L1.map TransvectionStruct.toMatrix).prod.map f *
      diagonal (fun i => f (D i)) * (L2.map TransvectionStruct.toMatrix).prod.map f := by
    rw [hM, Matrix.map_mul, Matrix.map_mul, diagonal_map (map_zero f)]
  rw [hMf, rank_mul_eq_left_of_isUnit_det _ _ hQf, rank_mul_eq_right_of_isUnit_det _ _ hPf, hM,
    rank_mul_eq_left_of_isUnit_det _ _ (by rw [hQ]; exact isUnit_one),
    rank_mul_eq_right_of_isUnit_det _ _ (by rw [hP]; exact isUnit_one), rank_diagonal,
    rank_diagonal]
  exact Fintype.card_congr (Equiv.subtypeEquivRight fun i => map_ne_zero f)

/-- The rank of a matrix over an ordered field is unchanged under a ring hom into another ordered
field (for instance `ℚ → ℝ`). -/
theorem rank_map_of_linearOrder [LinearOrder K] [IsStrictOrderedRing K] [LinearOrder L]
    [IsStrictOrderedRing L] {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (f : K →+* L) (M : Matrix m n K) : (M.map f).rank = M.rank := by
  rw [← rank_transpose_mul_self M, ← rank_transpose_mul_self (M.map f), ← transpose_map,
    ← Matrix.map_mul, rank_map_square]

end RankMap

section Duality

variable {K L : Type*} [Field K] [Field L]

/-- Over a field, a vector orthogonal to `ker N` is a combination of the rows of `N`. -/
theorem exists_vecMul_eq_of_ker {m m' : Type*} [Fintype m] [Fintype m'] [DecidableEq m]
    [DecidableEq m'] (N : Matrix m m' K) (α : m' → K)
    (h : ∀ u : m' → K, N *ᵥ u = 0 → α ⬝ᵥ u = 0) : ∃ y : m → K, y ᵥ* N = α := by
  let φ : Module.Dual K (m' → K) :=
    { toFun := fun u => α ⬝ᵥ u
      map_add' := fun u v => dotProduct_add α u v
      map_smul' := fun c u => by simp [dotProduct_smul] }
  have hφ : φ ∈ (LinearMap.ker N.mulVecLin).dualAnnihilator := by
    rw [Submodule.mem_dualAnnihilator]
    intro u hu
    exact h u (by simpa using hu)
  rw [← LinearMap.range_dualMap_eq_dualAnnihilator_ker] at hφ
  obtain ⟨ψ, hψ⟩ := hφ
  refine ⟨fun i => ψ (fun j => if i = j then 1 else 0), ?_⟩
  funext j
  have h1 : ψ (N *ᵥ Pi.single j 1) = α j := by
    have := LinearMap.congr_fun hψ (Pi.single j 1)
    rw [LinearMap.dualMap_apply] at this
    simpa [φ] using this
  rw [LinearMap.pi_apply_eq_sum_univ ψ] at h1
  rw [← h1, vecMul, dotProduct]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  simp [mulVec_single, mul_comm]

/-- If `α` (over `K`) is orthogonal to `ker_K N`, then `f ∘ α` is orthogonal to `ker_L (N.map f)`
(the kernel over `L` is spanned by vectors over `K`). -/
theorem dotProduct_map_eq_zero_of_ker {m m' : Type*} [Fintype m] [Fintype m'] [DecidableEq m]
    [DecidableEq m'] (f : K →+* L) (N : Matrix m m' K) (α : m' → K)
    (h : ∀ u : m' → K, N *ᵥ u = 0 → α ⬝ᵥ u = 0) (u : m' → L) (hu : N.map f *ᵥ u = 0) :
    (fun j => f (α j)) ⬝ᵥ u = 0 := by
  obtain ⟨y, rfl⟩ := exists_vecMul_eq_of_ker N α h
  have : (fun j => f ((y ᵥ* N) j)) = (fun i => f (y i)) ᵥ* N.map f := by
    funext j
    exact RingHom.map_vecMul f N y j
  rw [this, ← dotProduct_mulVec, hu, dotProduct_zero]

end Duality

section ModP

/-- Integer vectors whose reductions mod a prime `p` are linearly independent over `𝔽_p` are
linearly independent over `ℤ`. -/
theorem linearIndependent_int_of_zmod {ι n : Type*} [Fintype ι] (p : ℕ) [hp : Fact p.Prime]
    (v : ι → n → ℤ) (h : LinearIndependent (ZMod p) (fun i j => (v i j : ZMod p))) :
    LinearIndependent ℤ v := by
  rw [Fintype.linearIndependent_iff] at h ⊢
  suffices H : ∀ N : ℕ, ∀ g : ι → ℤ, ∑ i, (g i).natAbs ≤ N → ∑ i, g i • v i = 0 → g = 0 by
    intro g hg i
    exact congrFun (H _ g le_rfl hg) i
  intro N
  induction N with
  | zero =>
    intro g hN _
    funext i
    have h0 : (g i).natAbs ≤ ∑ j, (g j).natAbs :=
      Finset.single_le_sum (f := fun j => (g j).natAbs) (fun j _ => Nat.zero_le _)
        (Finset.mem_univ i)
    have : (g i).natAbs = 0 := by omega
    simpa using this
  | succ N ih =>
    intro g hN hg
    have hmod : ∑ i, (g i : ZMod p) • (fun j => (v i j : ZMod p)) = 0 := by
      funext j
      have := congrArg (Int.cast : ℤ → ZMod p) (congrFun hg j)
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, Int.cast_sum,
        Int.cast_mul, Int.cast_zero] at this
      simpa [Finset.sum_apply] using this
    have hdiv : ∀ i, (p : ℤ) ∣ g i := fun i =>
      (ZMod.intCast_zmod_eq_zero_iff_dvd (g i) p).1 (h _ hmod i)
    choose g' hg' using hdiv
    have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
    have hrel : ∑ i, g' i • v i = 0 := by
      funext j
      have hj := congrFun hg j
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hj ⊢
      have : (p : ℤ) * ∑ i, g' i * v i j = 0 := by
        rw [Finset.mul_sum, ← hj]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [hg' i, mul_assoc]
      exact (mul_eq_zero.1 this).resolve_left hp0
    by_cases hz : g' = 0
    · funext i
      rw [hg' i, hz]
      simp
    · exfalso
      apply hz
      apply ih g' _ hrel
      have hsum : ∑ i, (g i).natAbs = p * ∑ i, (g' i).natAbs := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [hg' i, Int.natAbs_mul]
        simp
      obtain ⟨i0, hi0⟩ : ∃ i, g' i ≠ 0 := by
        by_contra hcon
        push Not at hcon
        exact hz (funext hcon)
      have hpos : 1 ≤ ∑ i, (g' i).natAbs := by
        have : (g' i0).natAbs ≤ ∑ i, (g' i).natAbs :=
          Finset.single_le_sum (f := fun j => (g' j).natAbs) (fun j _ => Nat.zero_le _)
            (Finset.mem_univ i0)
        have : 0 < (g' i0).natAbs := Int.natAbs_pos.2 hi0
        omega
      have h2 : 2 * ∑ i, (g' i).natAbs ≤ p * ∑ i, (g' i).natAbs :=
        Nat.mul_le_mul_right _ hp.out.two_le
      omega

/-- Full column rank of an integer matrix mod a prime gives full column rank over `ℚ`. -/
theorem rank_rat_of_rank_zmod {m d : ℕ} (K : Matrix (Fin m) (Fin d) ℤ) (p : ℕ) (hp : p.Prime)
    (h : (K.map (Int.cast : ℤ → ZMod p)).rank = d) : (K.map (Int.cast : ℤ → ℚ)).rank = d := by
  have := Fact.mk hp
  have h1 : LinearIndependent (ZMod p) (K.map (Int.cast : ℤ → ZMod p)).col := by
    rw [linearIndependent_iff_card_eq_finrank_span, Fintype.card_fin, Set.finrank,
      ← rank_eq_finrank_span_cols, h]
  have h2 : LinearIndependent ℤ K.col := linearIndependent_int_of_zmod p K.col h1
  have h3 : LinearIndependent ℚ (K.map (Int.cast : ℤ → ℚ)).col := by
    rw [← linearIndependent_algebraMap_comp_iff (S := ℚ)] at h2
    convert h2 using 1
    funext i j
    simp [Matrix.col]
  rw [rank_eq_finrank_span_cols, finrank_span_eq_card h3, Fintype.card_fin]

end ModP

end P8Lin
