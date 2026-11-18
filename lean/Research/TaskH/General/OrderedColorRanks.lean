import Mathlib

/-! Finite injective color blocks extend internally to full color permutations.
No graph, path family, or prescribed permutation is an input. -/

set_option autoImplicit false

namespace TaskH.General

/-- A genuine ordered list avoiding two distinct colors can be placed between
those colors in a full permutation, including the empty and maximal lists. -/
theorem exists_ordered_color_ranks {k s : ℕ} (hsk : s + 2 ≤ k)
    (α β : Fin k) (hab : α ≠ β) (D : Fin s → Fin k)
    (hD : Function.Injective D) (hDa : ∀ i, D i ≠ α) (hDb : ∀ i, D i ≠ β) :
    ∃ π : Equiv.Perm (Fin k),
      π α = ⟨0, by omega⟩ ∧ π β = ⟨s + 1, by omega⟩ ∧
      ∀ i : Fin s, π (D i) = ⟨i.val + 1, by have := i.isLt; omega⟩ := by
  let f : Fin s ⊕ Bool → Fin k
    | Sum.inl i => D i
    | Sum.inr false => α
    | Sum.inr true => β
  let g : Fin s ⊕ Bool → Fin k
    | Sum.inl i => ⟨i.val + 1, by have := i.isLt; omega⟩
    | Sum.inr false => ⟨0, by omega⟩
    | Sum.inr true => ⟨s + 1, by omega⟩
  have hf : Function.Injective f := by
    rintro (i | b) (j | d) he
    · exact congrArg Sum.inl (hD he)
    · cases d with
      | false => exact False.elim (hDa i he)
      | true => exact False.elim (hDb i he)
    · cases b with
      | false => exact False.elim (hDa j he.symm)
      | true => exact False.elim (hDb j he.symm)
    · cases b <;> cases d
      · rfl
      · exact False.elim (hab he)
      · exact False.elim (hab he.symm)
      · rfl
  have hg : Function.Injective g := by
    rintro (i | b) (j | d) he
    · apply congrArg Sum.inl
      apply Fin.ext
      have hv := congrArg Fin.val he
      change i.val + 1 = j.val + 1 at hv
      omega
    · have hv := congrArg Fin.val he
      cases d with
      | false => change i.val + 1 = 0 at hv; omega
      | true => change i.val + 1 = s + 1 at hv; have := i.isLt; omega
    · have hv := congrArg Fin.val he
      cases b with
      | false => change 0 = j.val + 1 at hv; omega
      | true => change s + 1 = j.val + 1 at hv; have := j.isLt; omega
    · have hv := congrArg Fin.val he
      cases b <;> cases d
      · rfl
      · change 0 = s + 1 at hv; omega
      · change s + 1 = 0 at hv; omega
      · rfl
  obtain ⟨π, hπ⟩ := Equiv.Perm.exists_extending_pair f g hf hg
  exact ⟨π, hπ (Sum.inr false), hπ (Sum.inr true), fun i => hπ (Sum.inl i)⟩

/-- Before the first wrap, the actual rotation of zero has its literal rank. -/
theorem rotate_pow_zero_rank {k : ℕ} (hk : 0 < k) (n : ℕ) (hn : n < k) :
    ((finRotate k) ^ n) ⟨0, hk⟩ = ⟨n, hn⟩ := by
  suffices ∀ m (hm : m < k), ((finRotate k) ^ m) ⟨0, hk⟩ = ⟨m, hm⟩ by
    exact this n hn
  intro m
  induction m with
  | zero => intro _; rfl
  | succ m ih =>
    intro hm
    rw [pow_succ', Equiv.Perm.mul_apply, ih (by omega)]
    cases k with
    | zero => omega
    | succ l => exact finRotate_of_lt (by omega)

end TaskH.General

#print axioms TaskH.General.exists_ordered_color_ranks
#print axioms TaskH.General.rotate_pow_zero_rank
