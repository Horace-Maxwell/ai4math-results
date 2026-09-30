import Research.Backfill.Paper8.Proof.Spec.Secular
import Research.Backfill.Paper8.Proof.Basic

/-!
# Paper 8, Lemma 3.1(i),(ii): eigenvectors of `A(T(a))`

Solving `A x = θ x` (equation (3.1), `P8Basic.mulVec_eq_smul_iff`): if `θ ≠ 0` and `θ² ≠ a_i` for
all `i`, then `x = x_c · x^θ` (`eq_smul_secVec`), and `x^θ` is an eigenvector iff
`∑_i 1/(θ² - a_i) = 1`, i.e. `R(θ²) = 0` (`secVec_eigen`, `aeval_secular_eq_zero_iff`). If
`θ² = b ∈ B`, `θ ≠ 0`, the eigenspace is described coordinatewise (`mulVec_eq_smul_sqrt_iff`) and
is isomorphic to `{α : I_b → ℝ | ∑ α = 0}`, of dimension `k_b - 1` (`finrank_eigenspace_sqrt`).
-/

set_option autoImplicit false

open BackfillPaper8.Challenge Polynomial Matrix

namespace P8Spec

section Branch

variable {k : ℕ} (a : Fin k → ℕ)

theorem mem_Bset_branchMS (b : ℕ) : b ∈ Bset (branchMS a) ↔ ∃ i, a i = b := by
  simp [Bset, branchMS]

theorem card_branchMS : Multiset.card (branchMS a) = k := by
  simp [branchMS]

theorem branchMS_ne_zero (hk : 0 < k) : branchMS a ≠ 0 := by
  intro h
  have := card_branchMS a
  rw [h, Multiset.card_zero] at this
  omega

theorem kb_branchMS (b : ℕ) : kb (branchMS a) b = (Ib a b).card := by
  rw [kb, branchMS, Multiset.count_map, Ib, Finset.card_def, Finset.filter_val]
  congr 1
  exact Multiset.filter_congr (fun x _ => eq_comm)

/-- `∑_i f(a_i) = ∑_{b ∈ B} k_b f(b)`. -/
theorem sum_branch (f : ℕ → ℝ) :
    ∑ i, f (a i) = ∑ b ∈ Bset (branchMS a), (kb (branchMS a) b : ℝ) * f b := by
  have h := Finset.sum_multiset_map_count (branchMS a) f
  simp only [nsmul_eq_mul] at h
  change _ = ∑ b ∈ (branchMS a).toFinset, ((branchMS a).count b : ℝ) * f b
  rw [← h, branchMS, Multiset.map_map, Finset.sum_map_val]
  rfl

/-- For `t ≠ a_i` (all `i`): `R(t) = 0 ↔ F(t) = ∑_i 1/(t - a_i) = 1`. -/
theorem aeval_secular_eq_zero_iff (t : ℝ) (ht : ∀ i, t ≠ (a i : ℝ)) :
    aeval t (secular (branchMS a)) = 0 ↔ ∑ i, 1 / (t - (a i : ℝ)) = 1 := by
  have htB : ∀ b ∈ Bset (branchMS a), t ≠ (b : ℝ) := by
    intro b hb
    obtain ⟨i, rfl⟩ := (mem_Bset_branchMS a b).1 hb
    exact ht i
  rw [aeval_secular_eq_mul _ t htB]
  have hP : ∏ b ∈ Bset (branchMS a), (t - (b : ℝ)) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 (fun b hb => sub_ne_zero.2 (htB b hb))
  have hF : ∑ i, 1 / (t - (a i : ℝ)) =
      ∑ b ∈ Bset (branchMS a), (kb (branchMS a) b : ℝ) / (t - (b : ℝ)) := by
    have h := sum_branch a (fun b : ℕ => 1 / (t - (b : ℝ)))
    simp only [mul_one_div] at h
    exact h
  rw [hF, mul_eq_zero, sub_eq_zero]
  constructor
  · rintro (h | h)
    · exact absurd h hP
    · exact h.symm
  · intro h
    exact Or.inr h.symm

end Branch

section Secular

variable {k : ℕ} (a : Fin k → ℕ)

/-- `x^θ` is an eigenvector when `θ² ∉ {a_i}` and `F(θ²) = 1`. -/
theorem secVec_eigen (θ : ℝ) (hne : ∀ i, θ ^ 2 ≠ (a i : ℝ))
    (hF : ∑ i, 1 / (θ ^ 2 - (a i : ℝ)) = 1) :
    adjT a *ᵥ secVec a θ = θ • secVec a θ := by
  rw [P8Basic.mulVec_eq_smul_iff]
  refine ⟨?_, fun i => ?_, fun i j => ?_⟩
  · simp only [secVec]
    calc θ * 1 = θ * ∑ i, 1 / (θ ^ 2 - (a i : ℝ)) := by rw [hF]
      _ = ∑ i, θ / (θ ^ 2 - (a i : ℝ)) := by
        rw [Finset.mul_sum]
        simp only [mul_one_div]
  · simp only [secVec, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hD : θ ^ 2 - (a i : ℝ) ≠ 0 := sub_ne_zero.2 (hne i)
    field_simp
    ring
  · simp only [secVec, mul_one_div]

/-- Leaf coordinates of an eigenvector for `θ ≠ 0`: `x_ℓ = x_{v_i}/θ`. -/
theorem leaf_eq_div (θ : ℝ) (hθ : θ ≠ 0) (x : TV a → ℝ) (hx : adjT a *ᵥ x = θ • x) (i : Fin k)
    (j : Fin (a i)) : x (some ⟨i, some j⟩) = x (some ⟨i, none⟩) / θ := by
  obtain ⟨_, _, h3⟩ := (P8Basic.mulVec_eq_smul_iff a x θ).1 hx
  rw [← h3 i j]
  field_simp

/-- For an eigenvector with `θ ≠ 0`: `(θ² - a_i) x_{v_i} = θ x_c`. -/
theorem mid_eq (θ : ℝ) (hθ : θ ≠ 0) (x : TV a → ℝ) (hx : adjT a *ᵥ x = θ • x) (i : Fin k) :
    (θ ^ 2 - (a i : ℝ)) * x (some ⟨i, none⟩) = θ * x none := by
  obtain ⟨_, h2, _⟩ := (P8Basic.mulVec_eq_smul_iff a x θ).1 hx
  have e := h2 i
  simp only [leaf_eq_div a θ hθ x hx i, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul] at e
  have hinv : θ⁻¹ * θ = 1 := inv_mul_cancel₀ hθ
  linear_combination θ * e + (a i : ℝ) * x (some ⟨i, none⟩) * hinv

/-- An eigenvector for `θ ≠ 0` with `θ² ∉ {a_i}` is `x_c · x^θ`. -/
theorem eq_smul_secVec (θ : ℝ) (hθ : θ ≠ 0) (hne : ∀ i, θ ^ 2 ≠ (a i : ℝ)) (x : TV a → ℝ)
    (hx : adjT a *ᵥ x = θ • x) : x = x none • secVec a θ := by
  have hv : ∀ i, x (some ⟨i, none⟩) = θ * x none / (θ ^ 2 - (a i : ℝ)) := by
    intro i
    rw [eq_div_iff (sub_ne_zero.2 (hne i)), mul_comm]
    exact mid_eq a θ hθ x hx i
  funext v
  rcases v with _ | ⟨i, _ | j⟩
  · simp [secVec]
  · simp only [Pi.smul_apply, smul_eq_mul, secVec]
    rw [hv i]
    ring
  · simp only [Pi.smul_apply, smul_eq_mul, secVec]
    rw [leaf_eq_div a θ hθ x hx i j, hv i]
    have hD : θ ^ 2 - (a i : ℝ) ≠ 0 := sub_ne_zero.2 (hne i)
    field_simp

/-- Lemma 3.1(i), eigenspaces: for `θ ≠ 0`, `θ² ∉ {a_i}`, `F(θ²) = 1`, `E_θ = span {x^θ}`. -/
theorem eigenspace_eq_span_secVec (θ : ℝ) (hθ : θ ≠ 0) (hne : ∀ i, θ ^ 2 ≠ (a i : ℝ))
    (hF : ∑ i, 1 / (θ ^ 2 - (a i : ℝ)) = 1) :
    Module.End.eigenspace (Matrix.toLin' (adjT a)) θ = Submodule.span ℝ {secVec a θ} := by
  ext x
  rw [P8Basic.mem_eigenspace_iff, Submodule.mem_span_singleton]
  constructor
  · intro hx
    exact ⟨x none, (eq_smul_secVec a θ hθ hne x hx).symm⟩
  · rintro ⟨c, rfl⟩
    rw [Matrix.mulVec_smul, secVec_eigen a θ hne hF, smul_comm]

end Secular

section Sqrt

variable {k : ℕ} (a : Fin k → ℕ)

/-- Lemma 3.1(ii), description of `E_θ` for `θ² = b ∈ B`, `θ ≠ 0`. -/
theorem mulVec_eq_smul_sqrt_iff (b : ℕ) (hb : ∃ i, a i = b) (θ : ℝ) (hθ : θ ≠ 0)
    (hθb : θ ^ 2 = (b : ℝ)) (x : TV a → ℝ) :
    adjT a *ᵥ x = θ • x ↔
      (x none = 0 ∧
        (∀ i, a i ≠ b → x (some ⟨i, none⟩) = 0 ∧ ∀ j, x (some ⟨i, some j⟩) = 0) ∧
        (∀ i, a i = b → ∀ j, x (some ⟨i, some j⟩) = x (some ⟨i, none⟩) / θ) ∧
        ∑ i ∈ Ib a b, x (some ⟨i, none⟩) = 0) := by
  have hinv : θ⁻¹ * θ = 1 := inv_mul_cancel₀ hθ
  constructor
  · intro hx
    have hl := leaf_eq_div a θ hθ x hx
    have hv := mid_eq a θ hθ x hx
    obtain ⟨h1, _, _⟩ := (P8Basic.mulVec_eq_smul_iff a x θ).1 hx
    obtain ⟨i0, hi0⟩ := hb
    have hc : x none = 0 := by
      have e := hv i0
      have e2 : ((a i0 : ℕ) : ℝ) = θ ^ 2 := by
        rw [hθb]
        exact_mod_cast hi0
      rw [e2, sub_self, zero_mul] at e
      exact (mul_eq_zero.1 e.symm).resolve_left hθ
    have hvz : ∀ i, a i ≠ b → x (some ⟨i, none⟩) = 0 := by
      intro i hi
      have e := hv i
      rw [hc, mul_zero] at e
      have hD : θ ^ 2 - (a i : ℝ) ≠ 0 := by
        rw [hθb, sub_ne_zero]
        exact_mod_cast (Ne.symm hi)
      exact (mul_eq_zero.1 e).resolve_left hD
    refine ⟨hc, fun i hi => ⟨hvz i hi, fun j => by rw [hl i j, hvz i hi, zero_div]⟩,
      fun i _ j => hl i j, ?_⟩
    have hsum : ∑ i ∈ Ib a b, x (some ⟨i, none⟩) = ∑ i, x (some ⟨i, none⟩) := by
      apply Finset.sum_subset (Finset.subset_univ _)
      intro i _ hi
      apply hvz i
      simpa [Ib] using hi
    rw [hsum, ← h1, hc, mul_zero]
  · rintro ⟨hc, hne, heq, hsum⟩
    rw [P8Basic.mulVec_eq_smul_iff]
    refine ⟨?_, fun i => ?_, fun i j => ?_⟩
    · have e : ∑ i ∈ Ib a b, x (some ⟨i, none⟩) = ∑ i, x (some ⟨i, none⟩) := by
        apply Finset.sum_subset (Finset.subset_univ _)
        intro i _ hi
        exact (hne i (by simpa [Ib] using hi)).1
      rw [hc, mul_zero, ← e, hsum]
    · by_cases hi : a i = b
      · simp only [heq i hi, hc, zero_add, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          nsmul_eq_mul]
        have hai : ((a i : ℕ) : ℝ) = θ ^ 2 := by
          rw [hθb]
          exact_mod_cast hi
        rw [hai]
        linear_combination (-(θ * x (some ⟨i, none⟩))) * hinv
      · simp only [(hne i hi).1, (hne i hi).2, hc, mul_zero, Finset.sum_const_zero, add_zero]
    · by_cases hi : a i = b
      · rw [heq i hi j]
        field_simp
      · rw [(hne i hi).1, (hne i hi).2 j, mul_zero]

/-- The coordinates `x_{v_i}`, `i ∈ I_b`. -/
def coordV (b : ℕ) : (TV a → ℝ) →ₗ[ℝ] ({i : Fin k // a i = b} → ℝ) :=
  LinearMap.pi (fun i => LinearMap.proj (some ⟨i.1, none⟩))

/-- The sum of the coordinates. -/
def sumL {ι : Type} [Fintype ι] : (ι → ℝ) →ₗ[ℝ] ℝ where
  toFun α := ∑ i, α i
  map_add' α β := by simp [Finset.sum_add_distrib]
  map_smul' c α := by simp [Finset.mul_sum]

theorem finrank_ker_sumL {ι : Type} [Fintype ι] [Nonempty ι] :
    Module.finrank ℝ (LinearMap.ker (sumL (ι := ι))) = Fintype.card ι - 1 := by
  classical
  have h := LinearMap.finrank_range_add_finrank_ker (sumL (ι := ι))
  have hr : LinearMap.range (sumL (ι := ι)) = ⊤ := by
    rw [LinearMap.range_eq_top]
    intro c
    obtain ⟨i0⟩ := ‹Nonempty ι›
    refine ⟨Pi.single i0 c, ?_⟩
    simp [sumL]
  rw [hr, finrank_top, Module.finrank_self, Module.finrank_fintype_fun_eq_card] at h
  omega

/-- The vector of `E_{±√b}` with `x_{v_i} = α_i` (`i ∈ I_b`). -/
noncomputable def vecOf (b : ℕ) (θ : ℝ) (α : {i : Fin k // a i = b} → ℝ) : TV a → ℝ
  | none => 0
  | some ⟨i, none⟩ => if h : a i = b then α ⟨i, h⟩ else 0
  | some ⟨i, some _⟩ => (if h : a i = b then α ⟨i, h⟩ else 0) / θ

theorem vecOf_mid (b : ℕ) (θ : ℝ) (α : {i : Fin k // a i = b} → ℝ) (i : Fin k) :
    vecOf a b θ α (some ⟨i, none⟩) = if h : a i = b then α ⟨i, h⟩ else 0 := rfl

theorem vecOf_leaf (b : ℕ) (θ : ℝ) (α : {i : Fin k // a i = b} → ℝ) (i : Fin k) (j : Fin (a i)) :
    vecOf a b θ α (some ⟨i, some j⟩) = (if h : a i = b then α ⟨i, h⟩ else 0) / θ := rfl

/-- Lemma 3.1(ii), multiplicity: `dim E_θ = k_b - 1` for `θ² = b ∈ B`, `θ ≠ 0`. -/
theorem finrank_eigenspace_sqrt (b : ℕ) (hb : ∃ i, a i = b) (θ : ℝ) (hθ : θ ≠ 0)
    (hθb : θ ^ 2 = (b : ℝ)) :
    Module.finrank ℝ (Module.End.eigenspace (Matrix.toLin' (adjT a)) θ) = (Ib a b).card - 1 := by
  have hmem : ∀ x, x ∈ Module.End.eigenspace (Matrix.toLin' (adjT a)) θ ↔
      (x none = 0 ∧
        (∀ i, a i ≠ b → x (some ⟨i, none⟩) = 0 ∧ ∀ j, x (some ⟨i, some j⟩) = 0) ∧
        (∀ i, a i = b → ∀ j, x (some ⟨i, some j⟩) = x (some ⟨i, none⟩) / θ) ∧
        ∑ i ∈ Ib a b, x (some ⟨i, none⟩) = 0) := fun x =>
    (P8Basic.mem_eigenspace_iff _ _ _).trans (mulVec_eq_smul_sqrt_iff a b hb θ hθ hθb x)
  have hsub : ∀ f : Fin k → ℝ, ∑ i ∈ Ib a b, f i = ∑ i : {i : Fin k // a i = b}, f i.1 :=
    fun f => Finset.sum_subtype (Ib a b) (fun i => by simp [Ib]) f
  set φ := (coordV a b).domRestrict (Module.End.eigenspace (Matrix.toLin' (adjT a)) θ) with hφ
  have hinj : Function.Injective φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    obtain ⟨hc, hne, heq, _⟩ := (hmem x).1 x.2
    have hv : ∀ i, a i = b → x.1 (some ⟨i, none⟩) = 0 := fun i hi => congrFun hx ⟨i, hi⟩
    apply Subtype.ext
    funext v
    rcases v with _ | ⟨i, _ | j⟩
    · exact hc
    · by_cases hi : a i = b
      · exact hv i hi
      · exact (hne i hi).1
    · by_cases hi : a i = b
      · change x.1 (some ⟨i, some j⟩) = 0
        rw [heq i hi j, hv i hi, zero_div]
      · exact (hne i hi).2 j
  have hrange : LinearMap.range φ = LinearMap.ker (sumL (ι := {i : Fin k // a i = b})) := by
    ext α
    rw [LinearMap.mem_range, LinearMap.mem_ker]
    constructor
    · rintro ⟨x, rfl⟩
      obtain ⟨_, _, _, hs⟩ := (hmem x).1 x.2
      rw [hsub (fun i => x.1 (some ⟨i, none⟩))] at hs
      exact hs
    · intro hα
      have hα' : ∑ i, α i = 0 := hα
      have hx : vecOf a b θ α ∈ Module.End.eigenspace (Matrix.toLin' (adjT a)) θ := by
        rw [hmem]
        refine ⟨rfl, fun i hi => ⟨?_, fun j => ?_⟩, fun i hi j => ?_, ?_⟩
        · rw [vecOf_mid, dite_eq_right hi]
        · rw [vecOf_leaf, dite_eq_right hi, zero_div]
        · rw [vecOf_leaf, vecOf_mid]
        · rw [hsub (fun i => vecOf a b θ α (some ⟨i, none⟩)), ← hα']
          refine Finset.sum_congr rfl (fun i _ => ?_)
          rw [vecOf_mid, dite_eq_left i.2]
      refine ⟨⟨vecOf a b θ α, hx⟩, ?_⟩
      funext i
      change vecOf a b θ α (some ⟨i.1, none⟩) = α i
      rw [vecOf_mid, dite_eq_left i.2]
  rw [← LinearMap.finrank_range_of_inj hinj, hrange]
  obtain ⟨i0, hi0⟩ := hb
  have : Nonempty {i : Fin k // a i = b} := ⟨⟨i0, hi0⟩⟩
  rw [finrank_ker_sumL, Fintype.card_subtype]
  rfl

end Sqrt

end P8Spec
