import Research.Backfill.Paper8.Challenge
import Research.Backfill.Paper8.Proof.Basic
import Research.Backfill.Paper8.Proof.Lin.BaseChange

/-!
# Paper 8 back-fill (agent `lin`): Remark 8.2 (pairing in bipartite graphs)

`A = [[0, C], [Cᵀ, 0]]` with `C` a `0/1` matrix, `θ ≠ 0` with even minimal polynomial, `s`
rational. The paper's argument: `E_{±θ} = {(u, ±Cᵀu/θ) : u ∈ ker(CCᵀ - θ²)}`; if `s ⬝ x = 0` on
`E_θ` then `u ⬝ s₁ θ + u ⬝ C s₂ = 0` on `ker(CCᵀ - θ²)`; over `F = ℚ(θ²)` this kernel condition
splits into `u ⬝ s₁ = 0` and `u ⬝ C s₂ = 0` because `θ ∉ F` (`not_mem_QAdj`), and it passes back to
the real kernel by `dotProduct_map_eq_zero_of_ker`; so `s ⬝ x = 0` on `E_{-θ}` as well.
-/

set_option autoImplicit false

open BackfillPaper8.Challenge Matrix Polynomial

namespace P8Lin

/-- If the minimal polynomial of `θ ≠ 0` over `ℚ` is even, then `θ ∉ ℚ(θ²)`. -/
theorem not_mem_QAdj {θ : ℝ} (hθ : θ ≠ 0) (heven : IsEvenPoly (minpoly ℚ θ)) :
    θ ∉ QAdj (θ ^ 2) := by
  intro hmem
  rw [IntermediateField.mem_adjoin_simple_iff] at hmem
  obtain ⟨r, t, hrt⟩ := hmem
  by_cases ht : aeval (θ ^ 2) t = 0
  · rw [ht, div_zero] at hrt
    exact hθ hrt
  · have h1 : θ * aeval (θ ^ 2) t = aeval (θ ^ 2) r := by
      rw [eq_div_iff ht] at hrt
      exact hrt
    have hpθ : aeval θ (X * t.comp (X ^ 2) - r.comp (X ^ 2)) = 0 := by
      simp only [map_sub, map_mul, aeval_X, aeval_comp, map_pow]
      rw [h1, sub_self]
    have hneg : aeval (-θ) (minpoly ℚ θ) = 0 := by
      have h2 := congrArg (aeval θ) heven
      rw [aeval_comp, minpoly.aeval] at h2
      simpa using h2
    obtain ⟨q, hq⟩ := minpoly.dvd ℚ θ hpθ
    have hpneg : aeval (-θ) (X * t.comp (X ^ 2) - r.comp (X ^ 2)) = 0 := by
      rw [hq, map_mul, hneg, zero_mul]
    simp only [map_sub, map_mul, aeval_X, aeval_comp, map_pow, neg_sq] at hpneg
    have h3 : θ * aeval (θ ^ 2) t = 0 := by linarith
    rcases mul_eq_zero.1 h3 with h | h
    · exact hθ h
    · exact ht h

/-- `a θ + b = 0` with `a, b ∈ ℚ(θ²)` and `θ ∉ ℚ(θ²)` forces `a = b = 0`. -/
theorem eq_zero_of_QAdj {θ : ℝ} (hθ : θ ∉ QAdj (θ ^ 2)) {a b : ℝ} (ha : a ∈ QAdj (θ ^ 2))
    (hb : b ∈ QAdj (θ ^ 2)) (h : a * θ + b = 0) : a = 0 ∧ b = 0 := by
  by_cases ha0 : a = 0
  · refine ⟨ha0, ?_⟩
    rw [ha0, zero_mul, zero_add] at h
    exact h
  · exfalso
    apply hθ
    have hθeq : θ = -b / a := by
      rw [eq_div_iff ha0]
      linarith [mul_comm θ a]
    have hmem : -b / a ∈ QAdj (θ ^ 2) := div_mem (neg_mem hb) ha
    rwa [← hθeq] at hmem

/-- The splitting argument over a subfield: if `(f α ⬝ u) θ + f β ⬝ u = 0` on the real kernel of
`N`, and `f a θ + f b = 0` forces `a = b = 0`, then `f α ⬝ u = f β ⬝ u = 0` on that kernel. -/
theorem kernel_split {F : Type*} [Field F] {m : Type*} [Fintype m] [DecidableEq m]
    (f : F →+* ℝ) (N : Matrix m m F) (α β : m → F) (θ : ℝ)
    (hθ : ∀ a b : F, f a * θ + f b = 0 → a = 0 ∧ b = 0)
    (h : ∀ u : m → ℝ, N.map f *ᵥ u = 0 →
      (fun i => f (α i)) ⬝ᵥ u * θ + (fun i => f (β i)) ⬝ᵥ u = 0)
    (u : m → ℝ) (hu : N.map f *ᵥ u = 0) :
    (fun i => f (α i)) ⬝ᵥ u = 0 ∧ (fun i => f (β i)) ⬝ᵥ u = 0 := by
  have hK : ∀ v : m → F, N *ᵥ v = 0 → α ⬝ᵥ v = 0 ∧ β ⬝ᵥ v = 0 := by
    intro v hv
    have hv' : N.map f *ᵥ (fun i => f (v i)) = 0 := by
      funext i
      have h1 := RingHom.map_mulVec f N v i
      rw [hv] at h1
      simpa [Function.comp_def] using h1.symm
    have h1 := h _ hv'
    have e1 : (fun i => f (α i)) ⬝ᵥ (fun i => f (v i)) = f (α ⬝ᵥ v) :=
      (RingHom.map_dotProduct f α v).symm
    have e2 : (fun i => f (β i)) ⬝ᵥ (fun i => f (v i)) = f (β ⬝ᵥ v) :=
      (RingHom.map_dotProduct f β v).symm
    rw [e1, e2] at h1
    exact hθ _ _ h1
  exact ⟨dotProduct_map_eq_zero_of_ker f N α (fun v hv => (hK v hv).1) u hu,
    dotProduct_map_eq_zero_of_ker f N β (fun v hv => (hK v hv).2) u hu⟩

section Bipartite

variable {m n : Type} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

omit [DecidableEq m] [DecidableEq n] in
/-- Eigenvectors of `[[0, C], [Cᵀ, 0]]`. -/
theorem fromBlocks_eig_iff (C : Matrix m n ℝ) (θ : ℝ) (x : m ⊕ n → ℝ) :
    fromBlocks 0 C Cᵀ 0 *ᵥ x = θ • x ↔
      C *ᵥ (x ∘ Sum.inr) = θ • (x ∘ Sum.inl) ∧ Cᵀ *ᵥ (x ∘ Sum.inl) = θ • (x ∘ Sum.inr) := by
  rw [fromBlocks_mulVec]
  constructor
  · intro h
    refine ⟨funext fun i => ?_, funext fun j => ?_⟩
    · have := congrFun h (Sum.inl i)
      simpa using this
    · have := congrFun h (Sum.inr j)
      simpa using this
  · rintro ⟨h1, h2⟩
    funext k
    rcases k with i | j
    · simpa using congrFun h1 i
    · simpa using congrFun h2 j

omit [DecidableEq m] [DecidableEq n] in
theorem dotProduct_sum_type (x y : m ⊕ n → ℝ) :
    x ⬝ᵥ y = (x ∘ Sum.inl) ⬝ᵥ (y ∘ Sum.inl) + (x ∘ Sum.inr) ⬝ᵥ (y ∘ Sum.inr) := by
  simp [dotProduct, Fintype.sum_sum_type]

omit [DecidableEq n] in
/-- The real kernel of `CCᵀ - θ²` over the field `ℚ(θ²)`: if `(s₁ ⬝ u) θ + (C s₂) ⬝ u = 0` on
`ker(CCᵀ - θ²)`, then `s₁ ⬝ u = 0` and `(C s₂) ⬝ u = 0` there. -/
theorem kernel_split_QAdj (C : Matrix m n ℝ) (hC : ∀ i j, C i j = 0 ∨ C i j = 1) {θ : ℝ}
    (hθF : θ ∉ QAdj (θ ^ 2)) (s1 : m → ℚ) (s2 : n → ℚ)
    (h : ∀ u : m → ℝ, C *ᵥ (Cᵀ *ᵥ u) = θ ^ 2 • u →
      (fun i => (s1 i : ℝ)) ⬝ᵥ u * θ + (C *ᵥ fun j => (s2 j : ℝ)) ⬝ᵥ u = 0)
    (u : m → ℝ) (hu : C *ᵥ (Cᵀ *ᵥ u) = θ ^ 2 • u) :
    (fun i => (s1 i : ℝ)) ⬝ᵥ u = 0 ∧ (C *ᵥ fun j => (s2 j : ℝ)) ⬝ᵥ u = 0 := by
  set F := QAdj (θ ^ 2) with hFdef
  have hmemC : ∀ i j, C i j ∈ F := by
    intro i j
    rcases hC i j with h0 | h1
    · rw [h0]
      exact zero_mem F
    · rw [h1]
      exact one_mem F
  have ht : θ ^ 2 ∈ F := IntermediateField.mem_adjoin_simple_self ℚ (θ ^ 2)
  let f : F →+* ℝ := algebraMap F ℝ
  let CF : Matrix m n F := Matrix.of fun i j => ⟨C i j, hmemC i j⟩
  let NF : Matrix m m F := CF * CFᵀ - diagonal (fun _ => (⟨θ ^ 2, ht⟩ : F))
  let α : m → F := fun i => ⟨(s1 i : ℝ), SubfieldClass.ratCast_mem F (s1 i)⟩
  let β : m → F := CF *ᵥ (fun j => (⟨(s2 j : ℝ), SubfieldClass.ratCast_mem F (s2 j)⟩ : F))
  have hCF : CF.map f = C := by
    ext i j
    rfl
  have hNF : ∀ v : m → ℝ, NF.map f *ᵥ v = C *ᵥ (Cᵀ *ᵥ v) - θ ^ 2 • v := by
    intro v
    have hmap : NF.map f = C * Cᵀ - diagonal (fun _ => θ ^ 2) := by
      rw [← RingHom.mapMatrix_apply, map_sub, RingHom.mapMatrix_apply,
        RingHom.mapMatrix_apply, Matrix.map_mul, transpose_map, hCF,
        diagonal_map (map_zero f)]
      rfl
    rw [hmap, sub_mulVec, ← mulVec_mulVec]
    congr 1
    funext i
    simp [mulVec_diagonal]
  have hβ : (fun i => f (β i)) = C *ᵥ fun j => (s2 j : ℝ) := by
    funext i
    rw [RingHom.map_mulVec f CF _ i, hCF]
    rfl
  have hθK : ∀ a b : F, f a * θ + f b = 0 → a = 0 ∧ b = 0 := by
    intro a b hab
    obtain ⟨ha, hb⟩ := eq_zero_of_QAdj hθF a.2 b.2 hab
    exact ⟨Subtype.ext ha, Subtype.ext hb⟩
  have hsplit := kernel_split f NF α β θ hθK (by
    intro v hv
    rw [hβ]
    exact h v (by rw [hNF, sub_eq_zero] at hv; exact hv)) u (by rw [hNF, hu, sub_self])
  rw [hβ] at hsplit
  exact hsplit

/-- If `P_θ s = 0` then the two halves of every `θ`-eigenvector are orthogonal to the two halves
of `s`. -/
theorem halves_eq_zero (C : Matrix m n ℝ) (hC : ∀ i j, C i j = 0 ∨ C i j = 1) {θ : ℝ}
    (hθ0 : θ ≠ 0) (hθF : θ ∉ QAdj (θ ^ 2)) (s : m ⊕ n → ℚ)
    (hnot : ¬ ProjNe (fromBlocks 0 C Cᵀ 0) θ (fun i => (s i : ℝ)))
    (x : m ⊕ n → ℝ) (hx : fromBlocks 0 C Cᵀ 0 *ᵥ x = θ • x) :
    (x ∘ Sum.inl) ⬝ᵥ (fun i => (s (Sum.inl i) : ℝ)) = 0 ∧
      (x ∘ Sum.inr) ⬝ᵥ (fun j => (s (Sum.inr j) : ℝ)) = 0 := by
  rw [P8Basic.projNe_iff] at hnot
  push Not at hnot
  have hT : ∀ (u : m → ℝ) (w : n → ℝ),
      (Cᵀ *ᵥ u) ⬝ᵥ w = (C *ᵥ w) ⬝ᵥ u := by
    intro u w
    rw [mulVec_transpose, ← dotProduct_mulVec, dotProduct_comm]
  have hU : ∀ u : m → ℝ, C *ᵥ (Cᵀ *ᵥ u) = θ ^ 2 • u →
      (fun i => (s (Sum.inl i) : ℝ)) ⬝ᵥ u * θ +
        (C *ᵥ fun j => (s (Sum.inr j) : ℝ)) ⬝ᵥ u = 0 := by
    intro u hu
    have hxu : fromBlocks 0 C Cᵀ 0 *ᵥ Sum.elim u (θ⁻¹ • (Cᵀ *ᵥ u)) =
        θ • Sum.elim u (θ⁻¹ • (Cᵀ *ᵥ u)) := by
      rw [fromBlocks_eig_iff]
      simp only [Sum.elim_comp_inl, Sum.elim_comp_inr]
      constructor
      · rw [mulVec_smul, hu, smul_smul, pow_two, ← mul_assoc, inv_mul_cancel₀ hθ0, one_mul]
      · rw [smul_smul, mul_inv_cancel₀ hθ0, one_smul]
    have h0 := hnot _ hxu
    rw [dotProduct_sum_type] at h0
    simp only [Function.comp_def, Sum.elim_inl, Sum.elim_inr] at h0
    rw [smul_dotProduct, hT, smul_eq_mul, dotProduct_comm u] at h0
    have h1 : θ * ((fun i => (s (Sum.inl i) : ℝ)) ⬝ᵥ u +
        θ⁻¹ * (C *ᵥ fun j => (s (Sum.inr j) : ℝ)) ⬝ᵥ u) = 0 := by
      rw [h0, mul_zero]
    rw [mul_add, ← mul_assoc, mul_inv_cancel₀ hθ0, one_mul, mul_comm] at h1
    exact h1
  have hxl : C *ᵥ (Cᵀ *ᵥ (x ∘ Sum.inl)) = θ ^ 2 • (x ∘ Sum.inl) := by
    obtain ⟨h1, h2⟩ := (fromBlocks_eig_iff C θ x).1 hx
    rw [h2, mulVec_smul, h1, smul_smul, pow_two]
  obtain ⟨e1, e2⟩ := kernel_split_QAdj C hC hθF (fun i => s (Sum.inl i))
    (fun j => s (Sum.inr j)) hU (x ∘ Sum.inl) hxl
  refine ⟨by rw [dotProduct_comm]; exact e1, ?_⟩
  obtain ⟨_, h2⟩ := (fromBlocks_eig_iff C θ x).1 hx
  have h3 : θ * ((x ∘ Sum.inr) ⬝ᵥ fun j => (s (Sum.inr j) : ℝ)) = 0 := by
    rw [← smul_eq_mul, ← smul_dotProduct, ← h2, hT, e2]
  rcases mul_eq_zero.1 h3 with h | h
  · exact absurd h hθ0
  · exact h

/-- `P_θ s = 0` implies `P_{-θ} s = 0`. -/
theorem not_projNe_neg (C : Matrix m n ℝ) (hC : ∀ i j, C i j = 0 ∨ C i j = 1) {θ : ℝ}
    (hθ0 : θ ≠ 0) (hθF : θ ∉ QAdj (θ ^ 2)) (s : m ⊕ n → ℚ)
    (hnot : ¬ ProjNe (fromBlocks 0 C Cᵀ 0) θ (fun i => (s i : ℝ))) :
    ¬ ProjNe (fromBlocks 0 C Cᵀ 0) (-θ) (fun i => (s i : ℝ)) := by
  rw [P8Basic.projNe_iff]
  push Not
  intro y hy
  have hx : fromBlocks 0 C Cᵀ 0 *ᵥ Sum.elim (y ∘ Sum.inl) (-(y ∘ Sum.inr)) =
      θ • Sum.elim (y ∘ Sum.inl) (-(y ∘ Sum.inr)) := by
    obtain ⟨h1, h2⟩ := (fromBlocks_eig_iff C (-θ) y).1 hy
    rw [fromBlocks_eig_iff]
    simp only [Sum.elim_comp_inl, Sum.elim_comp_inr]
    constructor
    · rw [mulVec_neg, h1, neg_smul, neg_neg]
    · rw [h2, neg_smul, smul_neg]
  obtain ⟨e1, e2⟩ := halves_eq_zero C hC hθ0 hθF s hnot _ hx
  simp only [Sum.elim_comp_inl, Sum.elim_comp_inr, neg_dotProduct, neg_eq_zero] at e1 e2
  rw [dotProduct_sum_type]
  simp only [Function.comp_def] at e1 e2 ⊢
  rw [e1, e2, add_zero]

end Bipartite

/-- The body of **Remark 8.2** (`rem:G`). -/
theorem remark_8_2_body : ∀ (m n : Type) [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (C : Matrix m n ℝ), (∀ i j, C i j = 0 ∨ C i j = 1) → ∀ θ : ℝ, θ ≠ 0 →
    IsEigenvalue (Matrix.fromBlocks 0 C Cᵀ 0) θ → IsEvenPoly (minpoly ℚ θ) →
    ∀ s : m ⊕ n → ℚ,
      (ProjNe (Matrix.fromBlocks 0 C Cᵀ 0) θ (fun i => (s i : ℝ)) ↔
        ProjNe (Matrix.fromBlocks 0 C Cᵀ 0) (-θ) (fun i => (s i : ℝ))) := by
  intro m n _ _ _ _ C hC θ hθ0 _ heven s
  have hθF := not_mem_QAdj hθ0 heven
  have hθF' : -θ ∉ QAdj ((-θ) ^ 2) := by
    rw [neg_sq]
    intro h
    exact hθF (by simpa using neg_mem h)
  constructor
  · intro hp
    by_contra hn
    have := not_projNe_neg C hC (neg_ne_zero.2 hθ0) hθF' s hn
    rw [neg_neg] at this
    exact this hp
  · intro hp
    by_contra hn
    exact not_projNe_neg C hC hθ0 hθF s hn hp

end P8Lin
