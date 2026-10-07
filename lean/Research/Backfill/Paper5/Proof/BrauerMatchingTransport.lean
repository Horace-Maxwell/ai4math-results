import Research.Backfill.Paper5.Proof.DiagramRanksOccurring

set_option autoImplicit false

namespace CodexPaper5.BrauerMatchingTransport

universe u v

abbrev Nonspecial {L : Type u} (S : L → Prop) := {l : L // ¬ S l}

abbrev Remainder {L : Type u} (X : L → Type v) (rep : ∀ l, X l) (l : L) :=
  {x : X l // x ≠ rep l}

/-- Only the specified representative is removed in a special fibre. -/
abbrev Allowed {L : Type u} (X : L → Type v) (rep : ∀ l, X l) (S : L → Prop) :=
  {z : (Σ l, X l) // S z.1 → z.2 ≠ rep z.1}

open Classical in
noncomputable def splitForward {L : Type u} (X : L → Type v) (rep : ∀ l, X l)
    (S : L → Prop) (z : Allowed X rep S) :
    Nonspecial S ⊕ (Σ l, Remainder X rep l) :=
  if hx : z.val.2 = rep z.val.1 then
    Sum.inl ⟨z.val.1, fun hs => z.property hs hx⟩
  else Sum.inr ⟨z.val.1, ⟨z.val.2, hx⟩⟩

def splitBackward {L : Type u} (X : L → Type v) (rep : ∀ l, X l) (S : L → Prop) :
    Nonspecial S ⊕ (Σ l, Remainder X rep l) → Allowed X rep S
  | Sum.inl a => ⟨⟨a.val, rep a.val⟩, fun hs => (a.property hs).elim⟩
  | Sum.inr ⟨l, x⟩ => ⟨⟨l, x.val⟩, fun _hs => x.property⟩

open Classical in
theorem splitBackward_forward {L : Type u} (X : L → Type v) (rep : ∀ l, X l)
    (S : L → Prop) (z : Allowed X rep S) :
    splitBackward X rep S (splitForward X rep S z) = z := by
  rcases z with ⟨⟨l, x⟩, hz⟩
  apply Subtype.ext
  by_cases hx : x = rep l
  · subst x
    simp only [splitForward, splitBackward, dite_true]
  · simp only [splitForward, splitBackward, dite_eq_right hx]

open Classical in
theorem splitForward_backward {L : Type u} (X : L → Type v) (rep : ∀ l, X l)
    (S : L → Prop) (z : Nonspecial S ⊕ (Σ l, Remainder X rep l)) :
    splitForward X rep S (splitBackward X rep S z) = z := by
  rcases z with a | ⟨l, ⟨x, hx⟩⟩
  · unfold splitBackward splitForward
    exact dite_eq_left (rfl : rep a.val = rep a.val)
  · unfold splitBackward splitForward
    exact dite_eq_right hx

/-- Both inverse laws are on the actual dependent pairs and their actual values. -/
noncomputable def splitEquiv {L : Type u} (X : L → Type v) (rep : ∀ l, X l)
    (S : L → Prop) : Allowed X rep S ≃ Nonspecial S ⊕ (Σ l, Remainder X rep l) where
  toFun := splitForward X rep S
  invFun := splitBackward X rep S
  left_inv := splitBackward_forward X rep S
  right_inv := splitForward_backward X rep S

def sumSwap {L : Type u} (X : L → Type v) (rep : ∀ l, X l) (S : L → Prop)
    (τ : Nonspecial S → Nonspecial S)
    (q : ∀ l, Remainder X rep l → Remainder X rep l) :
    Nonspecial S ⊕ (Σ l, Remainder X rep l) → Nonspecial S ⊕ (Σ l, Remainder X rep l)
  | Sum.inl a => Sum.inl (τ a)
  | Sum.inr ⟨l, x⟩ => Sum.inr ⟨l, q l x⟩

theorem sumSwap_involutive {L : Type u} (X : L → Type v) (rep : ∀ l, X l)
    (S : L → Prop) (τ : Nonspecial S → Nonspecial S)
    (q : ∀ l, Remainder X rep l → Remainder X rep l)
    (hτ : Function.Involutive τ) (hq : ∀ l, Function.Involutive (q l)) :
    Function.Involutive (sumSwap X rep S τ q) := by
  intro z
  rcases z with a | ⟨l, x⟩
  · change (Sum.inl (τ (τ a)) : Nonspecial S ⊕ (Σ j, Remainder X rep j)) = Sum.inl a
    exact congrArg Sum.inl (hτ a)
  · change (Sum.inr (⟨l, q l (q l x)⟩ : Σ j, Remainder X rep j) :
      Nonspecial S ⊕ (Σ j, Remainder X rep j)) = Sum.inr ⟨l, x⟩
    exact congrArg (fun y : Remainder X rep l =>
      (Sum.inr ⟨l, y⟩ : Nonspecial S ⊕ (Σ j, Remainder X rep j))) (hq l x)

theorem sumSwap_ne {L : Type u} (X : L → Type v) (rep : ∀ l, X l)
    (S : L → Prop) (τ : Nonspecial S → Nonspecial S)
    (q : ∀ l, Remainder X rep l → Remainder X rep l)
    (hτ : ∀ a, τ a ≠ a) (hq : ∀ l (x : Remainder X rep l), q l x ≠ x)
    (z : Nonspecial S ⊕ (Σ l, Remainder X rep l)) : sumSwap X rep S τ q z ≠ z := by
  intro h
  rcases z with a | ⟨l, x⟩
  · exact hτ a (Sum.inl.inj h)
  · have hs : (⟨l, q l x⟩ : Σ j, Remainder X rep j) = ⟨l, x⟩ := Sum.inr.inj h
    exact hq l x (eq_of_heq (Sigma.mk.inj_iff.mp hs).2)

/-- Transport the provided actual involutions and their actual relation witnesses. -/
theorem exists_pairing {L : Type u} (X : L → Type v) (rep : ∀ l, X l)
    (S : L → Prop) (τ : Nonspecial S → Nonspecial S)
    (q : ∀ l, Remainder X rep l → Remainder X rep l)
    (hτI : Function.Involutive τ) (hτN : ∀ a, τ a ≠ a)
    (hqI : ∀ l, Function.Involutive (q l))
    (hqN : ∀ l (x : Remainder X rep l), q l x ≠ x)
    (Q : (Σ l, X l) → (Σ l, X l) → Prop)
    (hrep : ∀ a : Nonspecial S,
      Q ⟨a.val, rep a.val⟩ ⟨(τ a).val, rep (τ a).val⟩)
    (hrem : ∀ l (x : Remainder X rep l), Q ⟨l, x.val⟩ ⟨l, (q l x).val⟩) :
    ∃ δ : Allowed X rep S → Allowed X rep S,
      Function.Involutive δ ∧ (∀ a, δ a ≠ a) ∧ ∀ a, Q a.val (δ a).val := by
  let e := splitEquiv X rep S
  let f := sumSwap X rep S τ q
  have hf : Function.Involutive f := sumSwap_involutive X rep S τ q hτI hqI
  have hn : ∀ y, f y ≠ y := sumSwap_ne X rep S τ q hτN hqN
  have hcompat : ∀ y, Q (e.symm y).val (e.symm (f y)).val := by
    intro y
    rcases y with a | ⟨l, x⟩
    · exact hrep a
    · exact hrem l x
  let δ : Allowed X rep S → Allowed X rep S := fun a => e.symm (f (e a))
  refine ⟨δ, ?_, ?_, ?_⟩
  · intro a
    change e.symm (f (e (e.symm (f (e a))))) = a
    rw [e.apply_symm_apply, hf (e a), e.symm_apply_apply]
  · intro a h
    apply hn (e a)
    have he := congrArg e h
    change e (e.symm (f (e a))) = e a at he
    exact (e.apply_symm_apply (f (e a))).symm.trans he
  · intro a
    simpa only [e.symm_apply_apply] using hcompat (e a)

#print axioms CodexPaper5.BrauerMatchingTransport.Nonspecial
#print axioms CodexPaper5.BrauerMatchingTransport.Remainder
#print axioms CodexPaper5.BrauerMatchingTransport.Allowed
#print axioms CodexPaper5.BrauerMatchingTransport.splitForward
#print axioms CodexPaper5.BrauerMatchingTransport.splitBackward
#print axioms CodexPaper5.BrauerMatchingTransport.splitBackward_forward
#print axioms CodexPaper5.BrauerMatchingTransport.splitForward_backward
#print axioms CodexPaper5.BrauerMatchingTransport.splitEquiv
#print axioms CodexPaper5.BrauerMatchingTransport.sumSwap
#print axioms CodexPaper5.BrauerMatchingTransport.sumSwap_involutive
#print axioms CodexPaper5.BrauerMatchingTransport.sumSwap_ne
#print axioms CodexPaper5.BrauerMatchingTransport.exists_pairing

end CodexPaper5.BrauerMatchingTransport
