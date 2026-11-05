import Research.Backfill.Paper7.InertiaQuadraticBridge

set_option autoImplicit false

noncomputable section

namespace Paper7Comparison

open Matrix BackfillPaper7.Challenge Paper7Inertia
open scoped Matrix

theorem multiset_pos_zero_eq_nonneg (s : Multiset ℝ) :
    (s.filter (fun x => 0 < x)).card + s.count 0 =
      (s.filter (fun x => 0 ≤ x)).card := by
  have hu : s.filter (fun x => 0 < x ∨ 0 = x) = s.filter (fun x => 0 ≤ x) := by
    apply Multiset.filter_congr
    intro x hx
    exact le_iff_lt_or_eq.symm
  have hi : s.filter (fun x => 0 < x ∧ 0 = x) = 0 := by
    apply Multiset.filter_eq_nil.mpr
    intro x hx h
    rcases h with ⟨hp, hz⟩
    linarith
  have h : s.filter (fun x => 0 < x) + s.filter (fun x => 0 = x) =
      s.filter (fun x => 0 ≤ x) := by
    rw [Multiset.filter_add_filter, hu, hi, add_zero]
  simpa only [Multiset.card_add, Multiset.count_eq_card_filter_eq] using
    congrArg Multiset.card h
#print axioms Paper7Comparison.multiset_pos_zero_eq_nonneg

theorem multiset_neg_zero_eq_nonpos (s : Multiset ℝ) :
    (s.filter (fun x => x < 0)).card + s.count 0 =
      (s.filter (fun x => x ≤ 0)).card := by
  have hu : s.filter (fun x => x < 0 ∨ 0 = x) = s.filter (fun x => x ≤ 0) := by
    apply Multiset.filter_congr
    intro x hx
    constructor
    · rintro (h | h) <;> linarith
    · intro h
      rcases h.lt_or_eq with h | h
      · exact Or.inl h
      · exact Or.inr h.symm
  have hi : s.filter (fun x => x < 0 ∧ 0 = x) = 0 := by
    apply Multiset.filter_eq_nil.mpr
    intro x hx h
    rcases h with ⟨hn, hz⟩
    linarith
  have h : s.filter (fun x => x < 0) + s.filter (fun x => 0 = x) =
      s.filter (fun x => x ≤ 0) := by
    rw [Multiset.filter_add_filter, hu, hi, add_zero]
  simpa only [Multiset.card_add, Multiset.count_eq_card_filter_eq] using
    congrArg Multiset.card h
#print axioms Paper7Comparison.multiset_neg_zero_eq_nonpos

theorem multiset_inertia_total (s : Multiset ℝ) :
    (s.filter (fun x => 0 < x)).card + s.count 0 +
      (s.filter (fun x => x < 0)).card = s.card := by
  rw [multiset_pos_zero_eq_nonneg]
  have h := congrArg Multiset.card (Multiset.filter_add_not (fun x : ℝ => 0 ≤ x) s)
  simpa only [Multiset.card_add, not_le] using h
#print axioms Paper7Comparison.multiset_inertia_total

variable {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

theorem inertia_total (M : Matrix ι ι ℝ) (hM : M.IsHermitian) :
    nPos M + nZero M + nNeg M = Fintype.card ι := by
  have hc : (eigs M).card = Fintype.card ι := by
    simp [eigs, hM.roots_charpoly_eq_eigenvalues]
  exact (multiset_inertia_total (eigs M)).trans hc
#print axioms Paper7Comparison.inertia_total

omit [DecidableEq ι] in
theorem sigPos_mono (Q₁ Q₂ : QuadraticForm ℝ (ι → ℝ))
    (h : ∀ x, Q₁ x ≤ Q₂ x) : sigPos Q₁ ≤ sigPos Q₂ := by
  obtain ⟨V, hd, hV⟩ := exists_finrank_eq_sigPos_and_posDef Q₁
  rw [← hd]
  apply le_sigPos_of_posDef Q₂
  intro x hx
  exact (hV x hx).trans_le (h x)
#print axioms Paper7Comparison.sigPos_mono

omit [DecidableEq ι] in
theorem sigNeg_antitone (Q₁ Q₂ : QuadraticForm ℝ (ι → ℝ))
    (h : ∀ x, Q₁ x ≤ Q₂ x) : sigNeg Q₂ ≤ sigNeg Q₁ := by
  change sigPos (-Q₂) ≤ sigPos (-Q₁)
  apply sigPos_mono
  intro x
  exact neg_le_neg (h x)
#print axioms Paper7Comparison.sigNeg_antitone

theorem inertia_mono (A B : Matrix ι ι ℝ) (hA : A.IsHermitian) (hB : B.IsHermitian)
    (h : ∀ x, A.toQuadraticForm' x ≤ B.toQuadraticForm' x) :
    nPos A ≤ nPos B ∧ nNeg B ≤ nNeg A := by
  constructor
  · rw [nPos_eq_sigPos A hA, nPos_eq_sigPos B hB]
    exact sigPos_mono _ _ h
  · rw [nNeg_eq_sigNeg B hB, nNeg_eq_sigNeg A hA]
    exact sigNeg_antitone _ _ h
#print axioms Paper7Comparison.inertia_mono

/-- Non-strict counts are controlled separately, retaining every zero root. -/
theorem nonneg_inertia_mono (A B : Matrix ι ι ℝ)
    (hA : A.IsHermitian) (hB : B.IsHermitian)
    (h : ∀ x, A.toQuadraticForm' x ≤ B.toQuadraticForm' x) :
    nPos A + nZero A ≤ nPos B + nZero B := by
  have hn := (inertia_mono A B hA hB h).2
  have ha := inertia_total A hA
  have hb := inertia_total B hB
  omega
#print axioms Paper7Comparison.nonneg_inertia_mono

omit [DecidableEq ι] [DecidableEq κ] in
theorem sigPos_map_le (Q₁ : QuadraticForm ℝ (ι → ℝ)) (Q₂ : QuadraticForm ℝ (κ → ℝ))
    (f : (ι → ℝ) →ₗ[ℝ] (κ → ℝ)) (hf : Function.Injective f)
    (h : ∀ x, Q₁ x ≤ Q₂ (f x)) : sigPos Q₁ ≤ sigPos Q₂ := by
  obtain ⟨V, hd, hV⟩ := exists_finrank_eq_sigPos_and_posDef Q₁
  have hmap : (Q₂.restrict (V.map f)).PosDef := by
    intro y hy
    obtain ⟨x, hx, hxy⟩ := Submodule.mem_map.mp y.property
    have hx0 : (⟨x, hx⟩ : V) ≠ 0 := by
      intro hz
      have hzero : x = 0 := congrArg Subtype.val hz
      apply hy
      apply Subtype.ext
      simpa [hzero] using hxy.symm
    change 0 < Q₂ (y : κ → ℝ)
    rw [← hxy]
    exact (hV ⟨x, hx⟩ hx0).trans_le (h x)
  calc
    sigPos Q₁ = Module.finrank ℝ V := hd.symm
    _ = Module.finrank ℝ (V.map f) := (Submodule.equivMapOfInjective f hf V).finrank_eq
    _ ≤ sigPos Q₂ := le_sigPos_of_posDef Q₂ hmap
#print axioms Paper7Comparison.sigPos_map_le

/-- A genuine injective linear embedding and pointwise form comparison imply
the positive inertia bound; no assumed inertia inequality is hidden here. -/
theorem nPos_map_le (A : Matrix ι ι ℝ) (B : Matrix κ κ ℝ)
    (hA : A.IsHermitian) (hB : B.IsHermitian)
    (f : (ι → ℝ) →ₗ[ℝ] (κ → ℝ)) (hf : Function.Injective f)
    (h : ∀ x, A.toQuadraticForm' x ≤ B.toQuadraticForm' (f x)) : nPos A ≤ nPos B := by
  rw [nPos_eq_sigPos A hA, nPos_eq_sigPos B hB]
  exact sigPos_map_le _ _ f hf h
#print axioms Paper7Comparison.nPos_map_le

theorem nonneg_subspace_bound (M : Matrix ι ι ℝ) (hM : M.IsHermitian)
    (V : Submodule ℝ (ι → ℝ)) (hV : ∀ x ∈ V, 0 ≤ M.toQuadraticForm' x) :
    Module.finrank ℝ V ≤ nPos M + nZero M := by
  have hb := QuadraticForm.sigPos_add_finrank_le_of_nonpos
    (Q := -M.toQuadraticForm') (V := V) (fun x hx => by
      change -M.toQuadraticForm' x ≤ 0
      exact neg_nonpos.mpr (hV x hx))
  rw [sigPos_neg, ← nNeg_eq_sigNeg M hM, Module.finrank_fintype_fun_eq_card] at hb
  have ht := inertia_total M hM
  omega
#print axioms Paper7Comparison.nonneg_subspace_bound

theorem exists_nonneg_subspace (M : Matrix ι ι ℝ) (hM : M.IsHermitian) :
    ∃ V : Submodule ℝ (ι → ℝ), Module.finrank ℝ V = nPos M + nZero M ∧
      ∀ x ∈ V, 0 ≤ M.toQuadraticForm' x := by
  classical
  obtain ⟨e⟩ := quadratic_equivalent_eigenvalues M hM
  let S : Set ι := {i | 0 ≤ hM.eigenvalues i}
  let W : Submodule ℝ (ι → ℝ) := Pi.spanSubset ℝ S
  let V : Submodule ℝ (ι → ℝ) := W.map e.symm.toLinearMap
  have hWdim : Module.finrank ℝ W = S.ncard := Pi.dim_spanSubset
  have hVdim : Module.finrank ℝ V = Module.finrank ℝ W :=
    (Submodule.equivMapOfInjective e.symm.toLinearMap e.symm.toLinearEquiv.injective W).finrank_eq.symm
  have hcomp : Sᶜ = {i | hM.eigenvalues i < 0} := by
    ext i
    change ¬0 ≤ hM.eigenvalues i ↔ hM.eigenvalues i < 0
    exact not_le
  have hcard := Set.ncard_add_ncard_compl S
  rw [hcomp, ← nNeg_eq_eigenvalue_card M hM] at hcard
  simp only [Nat.card_eq_fintype_card] at hcard
  have htot := inertia_total M hM
  refine ⟨V, ?_, ?_⟩
  · omega
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.mp hx
    change 0 ≤ M.toQuadraticForm' (e.symm y)
    rw [e.symm.map_app, QuadraticMap.weightedSumSquares_apply]
    apply Finset.sum_nonneg
    intro i hi
    by_cases he : 0 ≤ hM.eigenvalues i
    · exact smul_nonneg he (mul_self_nonneg (y i))
    · have hz : y i = 0 := Pi.mem_spanSubset_iff.mp hy i he
      simp [hz]
#print axioms Paper7Comparison.exists_nonneg_subspace

/-- The embedding inequality for non-strict inertia, with zero eigenspaces retained. -/
theorem nonneg_map_le (A : Matrix ι ι ℝ) (B : Matrix κ κ ℝ)
    (hA : A.IsHermitian) (hB : B.IsHermitian)
    (f : (ι → ℝ) →ₗ[ℝ] (κ → ℝ)) (hf : Function.Injective f)
    (h : ∀ x, A.toQuadraticForm' x ≤ B.toQuadraticForm' (f x)) :
    nPos A + nZero A ≤ nPos B + nZero B := by
  obtain ⟨V, hd, hV⟩ := exists_nonneg_subspace A hA
  have hmap : ∀ y ∈ V.map f, 0 ≤ B.toQuadraticForm' y := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.mp hy
    exact (hV x hx).trans (h x)
  calc
    nPos A + nZero A = Module.finrank ℝ V := hd.symm
    _ = Module.finrank ℝ (V.map f) := (Submodule.equivMapOfInjective f hf V).finrank_eq
    _ ≤ nPos B + nZero B := nonneg_subspace_bound B hB (V.map f) hmap
#print axioms Paper7Comparison.nonneg_map_le

theorem quadratic_add_apply (A B : Matrix ι ι ℝ) (x : ι → ℝ) :
    (A+B).toQuadraticForm' x = A.toQuadraticForm' x + B.toQuadraticForm' x := by
  simp only [quadratic_apply, Matrix.add_mulVec, dotProduct_add]
#print axioms Paper7Comparison.quadratic_add_apply

end Paper7Comparison
