import Research.Backfill.Paper8.Proof.Basic

/-!
# Paper 8, known-answer tests (agent `tests`): vectors on `T(a)` written with `mkSw`

A vector on the vertices of `T(a)` is `mkSw a c m l` (value `c` at the centre, `m i` at `v_i`,
`l i j` at the `j`-th leaf of branch `i`). This module gives `A x`, `D_s A D_s x`, `θ • x` and
`∑ x` in this form, equation (3.1) of the paper written componentwise, so that the tests of
`AllEigenvaluesMain`, `condZ` and `secVec` reduce to identities between numbers.
-/

set_option autoImplicit false

open BackfillPaper8.Challenge Matrix

namespace P8Tests

section Vec

variable {k : ℕ} (a : Fin k → ℕ)

@[simp] theorem mkSw_none (c : ℝ) (m : Fin k → ℝ) (l : (i : Fin k) → Fin (a i) → ℝ) :
    mkSw a c m l none = c := rfl

@[simp] theorem mkSw_v (c : ℝ) (m : Fin k → ℝ) (l : (i : Fin k) → Fin (a i) → ℝ) (i : Fin k) :
    mkSw a c m l (some ⟨i, none⟩) = m i := rfl

@[simp] theorem mkSw_l (c : ℝ) (m : Fin k → ℝ) (l : (i : Fin k) → Fin (a i) → ℝ) (i : Fin k)
    (j : Fin (a i)) : mkSw a c m l (some ⟨i, some j⟩) = l i j := rfl

/-- Every vector on `T(a)` is an `mkSw`. -/
theorem eq_mkSw (x : TV a → ℝ) :
    x = mkSw a (x none) (fun i => x (some ⟨i, none⟩)) (fun i j => x (some ⟨i, some j⟩)) := by
  funext v
  rcases v with _ | ⟨i, _ | j⟩ <;> rfl

theorem mkSw_eq_iff {c c' : ℝ} {m m' : Fin k → ℝ} {l l' : (i : Fin k) → Fin (a i) → ℝ} :
    mkSw a c m l = mkSw a c' m' l' ↔ c = c' ∧ (∀ i, m i = m' i) ∧ (∀ i j, l i j = l' i j) := by
  constructor
  · intro h
    exact ⟨congrFun h none, fun i => congrFun h (some ⟨i, none⟩),
      fun i j => congrFun h (some ⟨i, some j⟩)⟩
  · rintro ⟨h1, h2, h3⟩
    funext v
    rcases v with _ | ⟨i, _ | j⟩
    · exact h1
    · exact h2 i
    · exact h3 i j

theorem smul_mkSw (θ c : ℝ) (m : Fin k → ℝ) (l : (i : Fin k) → Fin (a i) → ℝ) :
    θ • mkSw a c m l = mkSw a (θ * c) (fun i => θ * m i) (fun i j => θ * l i j) := by
  funext v
  rcases v with _ | ⟨i, _ | j⟩ <;> rfl

theorem zero_eq_mkSw : (0 : TV a → ℝ) = mkSw a 0 (fun _ => 0) (fun _ _ => 0) := by
  funext v
  rcases v with _ | ⟨i, _ | j⟩ <;> rfl

theorem ones_eq_mkSw : (fun _ => (1 : ℝ) : TV a → ℝ) = mkSw a 1 (fun _ => 1) (fun _ _ => 1) := by
  funext v
  rcases v with _ | ⟨i, _ | j⟩ <;> rfl

/-- `∑_v x_v = x_c + ∑_i (x_{v_i} + ∑_{ℓ ∈ L_i} x_ℓ)`. -/
theorem sum_mkSw (c : ℝ) (m : Fin k → ℝ) (l : (i : Fin k) → Fin (a i) → ℝ) :
    ∑ v, mkSw a c m l v = c + ∑ i, (m i + ∑ j, l i j) :=
  P8Basic.sum_TV a _

/-- Equation (3.1): `(A x)_c = ∑_i x_{v_i}`, `(A x)_{v_i} = x_c + ∑_{ℓ ∈ L_i} x_ℓ`,
`(A x)_ℓ = x_{v_i}`. -/
theorem adjT_mulVec_mkSw (c : ℝ) (m : Fin k → ℝ) (l : (i : Fin k) → Fin (a i) → ℝ) :
    adjT a *ᵥ mkSw a c m l = mkSw a (∑ i, m i) (fun i => c + ∑ j, l i j) (fun i _ => m i) := by
  funext v
  rcases v with _ | ⟨i, _ | j⟩
  · exact P8Basic.mulVec_c a _
  · exact P8Basic.mulVec_v a _ i
  · exact P8Basic.mulVec_l a _ i j

theorem switchMatrix_mulVec_apply {n : Type} [Fintype n] [DecidableEq n] (A : Matrix n n ℝ)
    (s x : n → ℝ) (i : n) :
    (switchMatrix A s *ᵥ x) i = s i * (A *ᵥ (fun j => s j * x j)) i := by
  have hD : diagonal s *ᵥ x = fun j => s j * x j := funext (mulVec_diagonal s x)
  rw [switchMatrix, ← mulVec_mulVec, ← mulVec_mulVec, mulVec_diagonal, hD]

/-- `D_s A D_s x` for `s = mkSw a sc sm sl` and `x = mkSw a xc xm xl`. -/
theorem switch_mulVec_mkSw (sc xc : ℝ) (sm xm : Fin k → ℝ)
    (sl xl : (i : Fin k) → Fin (a i) → ℝ) :
    switchMatrix (adjT a) (mkSw a sc sm sl) *ᵥ mkSw a xc xm xl =
      mkSw a (sc * ∑ i, sm i * xm i) (fun i => sm i * (sc * xc + ∑ j, sl i j * xl i j))
        (fun i j => sl i j * (sm i * xm i)) := by
  have hsx : (fun v => mkSw a sc sm sl v * mkSw a xc xm xl v) =
      mkSw a (sc * xc) (fun i => sm i * xm i) (fun i j => sl i j * xl i j) := by
    funext v
    rcases v with _ | ⟨i, _ | j⟩ <;> rfl
  funext v
  rw [switchMatrix_mulVec_apply, hsx, adjT_mulVec_mkSw]
  rcases v with _ | ⟨i, _ | j⟩ <;> rfl

end Vec

end P8Tests
