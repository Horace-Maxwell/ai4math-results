import Mathlib

/-! Exact finite-alphabet counting recurrence. No numeric table is assumed.
The recurrence counts words, so distinct witnesses for an acceptance predicate
cannot multiply their contribution. This file has not been compiled.
-/
set_option autoImplicit false
noncomputable section
namespace Paper7MomentDP
open scoped BigOperators

def wordSum {A Γ : Type*} [AddCommMonoid Γ] (c : A → Γ)
    {n : ℕ} (w : Fin n → A) : Γ := ∑ i, c (w i)
#print axioms Paper7MomentDP.wordSum

def splitWord (A : Type*) (n : ℕ) :
    (Fin (n + 1) → A) ≃ A × (Fin n → A) where
  toFun w := (w 0, Fin.tail w)
  invFun z := Fin.cons z.1 z.2
  left_inv w := Fin.cons_self_tail w
  right_inv z := by
    rcases z with ⟨a, w⟩
    simp only [Fin.cons_zero, Fin.tail_cons]
#print axioms Paper7MomentDP.splitWord

theorem wordSum_cons {A Γ : Type*} [AddCommMonoid Γ] (c : A → Γ)
    (n : ℕ) (a : A) (w : Fin n → A) :
    wordSum c (Fin.cons a w) = c a + wordSum c w := by
  simp only [wordSum, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]
#print axioms Paper7MomentDP.wordSum_cons

theorem wordSum_head_tail {A Γ : Type*} [AddCommMonoid Γ] (c : A → Γ)
    (n : ℕ) (w : Fin (n + 1) → A) :
    wordSum c w = c (w 0) + wordSum c (Fin.tail w) := by
  change (∑ i : Fin (n + 1), c (w i)) = c (w 0) + ∑ i : Fin n, c (w i.succ)
  exact Fin.sum_univ_succ _
#print axioms Paper7MomentDP.wordSum_head_tail

/-- The first letter and the remaining target give a bijection of actual fibres. -/
def wordFibreEquiv {A Γ : Type*} [AddCommGroup Γ] (c : A → Γ)
    (n : ℕ) (t : Γ) :
    {w : Fin (n + 1) → A // wordSum c w = t} ≃
      Σ a : A, {w : Fin n → A // wordSum c w = t - c a} where
  toFun w := ⟨w.val 0, Fin.tail w.val, by
    apply eq_sub_iff_add_eq.mpr
    calc
      wordSum c (Fin.tail w.val) + c (w.val 0) = wordSum c w.val := by
        rw [wordSum_head_tail c n w.val]
        exact add_comm _ _
      _ = t := w.property⟩
  invFun z := ⟨Fin.cons z.1 z.2.val, by
    rw [wordSum_cons, z.2.property]
    abel⟩
  left_inv w := by
    apply Subtype.ext
    exact Fin.cons_self_tail w.val
  right_inv z := by
    rcases z with ⟨a, w, hw⟩
    apply Sigma.ext rfl
    apply heq_of_eq
    apply Subtype.ext
    funext i
    rfl
#print axioms Paper7MomentDP.wordFibreEquiv

def wordFibreCard {A Γ : Type*} [AddCommMonoid Γ] (c : A → Γ)
    (n : ℕ) (t : Γ) : ℕ := Nat.card {w : Fin n → A // wordSum c w = t}
#print axioms Paper7MomentDP.wordFibreCard

theorem wordFibreCard_zero {A Γ : Type*} [Fintype A] [AddCommMonoid Γ]
    [DecidableEq Γ] (c : A → Γ) (t : Γ) :
    wordFibreCard c 0 t = if t = 0 then 1 else 0 := by
  classical
  unfold wordFibreCard
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  by_cases ht : t = 0
  · simp [wordSum, ht]
  · simp [wordSum, ht, eq_comm]
#print axioms Paper7MomentDP.wordFibreCard_zero

theorem wordFibreCard_succ {A Γ : Type*} [Fintype A] [AddCommGroup Γ]
    (c : A → Γ) (n : ℕ) (t : Γ) :
    wordFibreCard c (n + 1) t = ∑ a : A, wordFibreCard c n (t - c a) := by
  classical
  unfold wordFibreCard
  calc
    Nat.card {w : Fin (n + 1) → A // wordSum c w = t} =
        Nat.card (Σ a : A, {w : Fin n → A // wordSum c w = t - c a}) :=
      Nat.card_congr (wordFibreEquiv c n t)
    _ = _ := by simp only [Nat.card_eq_fintype_card, Fintype.card_sigma]
#print axioms Paper7MomentDP.wordFibreCard_succ

/-- This is the exact counting recurrence. Its un-memoized evaluation is not
offered as a performance solution for the large concrete counts. -/
def wordCountDP {A Γ : Type*} [Fintype A] [AddCommGroup Γ] [DecidableEq Γ]
    (c : A → Γ) : ℕ → Γ → ℕ
  | 0, t => if t = 0 then 1 else 0
  | n + 1, t => ∑ a : A, wordCountDP c n (t - c a)
#print axioms Paper7MomentDP.wordCountDP

theorem wordCountDP_eq_card {A Γ : Type*} [Fintype A] [AddCommGroup Γ]
    [DecidableEq Γ] (c : A → Γ) (n : ℕ) (t : Γ) :
    wordCountDP c n t = wordFibreCard c n t := by
  induction n generalizing t with
  | zero => exact (wordFibreCard_zero c t).symm
  | succ n ih =>
    rw [wordCountDP, wordFibreCard_succ]
    apply Finset.sum_congr rfl
    intro a _
    exact ih (t - c a)
#print axioms Paper7MomentDP.wordCountDP_eq_card

/-- An explicit helper interface for a future checked layer representation.
These equations are not supplied or assumed for any concrete numeric table. -/
def ValidCountLayers {A Γ : Type*} [Fintype A] [AddCommGroup Γ] [DecidableEq Γ]
    (c : A → Γ) (last : ℕ) (L : ℕ → Γ → ℕ) : Prop :=
  (∀ t, L 0 t = if t = 0 then 1 else 0) ∧
    ∀ n, n < last → ∀ t, L (n + 1) t = ∑ a : A, L n (t - c a)
#print axioms Paper7MomentDP.ValidCountLayers

theorem validCountLayers_eq_card {A Γ : Type*} [Fintype A] [AddCommGroup Γ]
    [DecidableEq Γ] (c : A → Γ) (last : ℕ) (L : ℕ → Γ → ℕ)
    (hL : ValidCountLayers c last L) (n : ℕ) (hn : n ≤ last) (t : Γ) :
    L n t = wordFibreCard c n t := by
  induction n generalizing t with
  | zero => exact (hL.1 t).trans (wordFibreCard_zero c t).symm
  | succ n ih =>
    rw [hL.2 n (by omega) t, wordFibreCard_succ]
    apply Finset.sum_congr rfl
    intro a _
    exact ih (by omega) (t - c a)
#print axioms Paper7MomentDP.validCountLayers_eq_card

end Paper7MomentDP
