import Mathlib

/-! A sorted finite set of distinct integers at least 2 dominates 2,3,... . -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace Paper7OddIntegral

theorem sorted_integer_lower (S : Finset ℤ) (hS : ∀ z ∈ S, 2 ≤ z)
    (i : Fin S.card) : (i.val : ℤ) + 2 ≤ S.orderEmbOfFin rfl i := by
  have haux (n : ℕ) : ∀ hn : n < S.card,
      (n : ℤ) + 2 ≤ S.orderEmbOfFin rfl ⟨n, hn⟩ := by
    induction n with
    | zero =>
      intro hn
      simpa only [Nat.cast_zero, zero_add] using
        hS _ (S.orderEmbOfFin_mem rfl ⟨0, hn⟩)
    | succ n ih =>
      intro hn
      have hn' : n < S.card := by omega
      have hprev := ih hn'
      have hlt : S.orderEmbOfFin rfl ⟨n, hn'⟩ < S.orderEmbOfFin rfl ⟨n + 1, hn⟩ :=
        (S.orderEmbOfFin rfl).strictMono (by change n < n + 1; omega)
      push_cast
      omega
  exact haux i.val i.isLt
#print axioms Paper7OddIntegral.sorted_integer_lower

theorem distinct_integer_squares_lower (S : Finset ℤ) (hS : ∀ z ∈ S, 2 ≤ z)
    (k : ℕ) (hk : k ≤ S.card) :
    (∑ v ∈ Finset.Icc 2 (k + 1), (v : ℝ) ^ 2) ≤ ∑ z ∈ S, (z : ℝ) ^ 2 := by
  classical
  let I : Finset ℕ := Finset.Icc 2 (k + 1)
  let f : I → ℤ := fun i => S.orderEmbOfFin rfl
    ⟨i.val - 2, by have hi := Finset.mem_Icc.mp i.property; omega⟩
  have hf : Function.Injective f := by
    intro i j hij
    have he := (S.orderEmbOfFin rfl).injective hij
    have hn := congrArg Fin.val he
    have hi := Finset.mem_Icc.mp i.property
    have hj := Finset.mem_Icc.mp j.property
    apply Subtype.ext
    change i.val - 2 = j.val - 2 at hn
    omega
  have hbound (i : I) : (i.val : ℤ) ≤ f i := by
    have hi := Finset.mem_Icc.mp i.property
    have h := sorted_integer_lower S hS
      ⟨i.val - 2, by omega⟩
    have heq : ((i.val - 2 : ℕ) : ℤ) + 2 = (i.val : ℤ) := by
      exact_mod_cast (Nat.sub_add_cancel hi.1)
    rw [heq] at h
    exact h
  have hs : (∑ i : I, (i.val : ℝ) ^ 2) ≤ ∑ z ∈ S, (z : ℝ) ^ 2 := by
    apply Finset.sum_le_sum_of_injOn f hf.injOn
    · intro z hz
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hz
      exact S.orderEmbOfFin_mem rfl _
    · intro i _
      have hle : (i.val : ℝ) ≤ (f i : ℝ) := by exact_mod_cast hbound i
      have hi0 : (0 : ℝ) ≤ (i.val : ℝ) := Nat.cast_nonneg _
      have hp : 0 ≤ ((f i : ℝ) - (i.val : ℝ)) * ((f i : ℝ) + (i.val : ℝ)) :=
        mul_nonneg (by linarith) (by linarith)
      nlinarith
    · intro z _ _
      exact sq_nonneg _
  calc
    _ = ∑ i : I, (i.val : ℝ) ^ 2 :=
      (Finset.sum_coe_sort I (fun z : ℕ => (z : ℝ) ^ 2)).symm
    _ ≤ _ := hs
#print axioms Paper7OddIntegral.distinct_integer_squares_lower

end Paper7OddIntegral
