import Research.Backfill.Paper5.Proof.BrauerMatchingFibres

set_option autoImplicit false

namespace CodexPaper5.BrauerMatching

open BackfillPaper5
open BrauerMatchingFibres

def pairFlip {k : ℕ} (a : Fin k × Bool) : Fin k × Bool := (a.1, !a.2)

theorem pairFlip_involutive (k : ℕ) :
    Function.Involutive (pairFlip (k := k)) := by
  rintro ⟨i, b⟩
  cases b <;> rfl

theorem pairFlip_ne (k : ℕ) (a : Fin k × Bool) : pairFlip a ≠ a := by
  rcases a with ⟨i, b⟩
  cases b <;> intro h <;> cases congrArg Prod.snd h

/-- All generic transport premises are supplied by actual Half representatives and paths. -/
theorem exists_target_pairing (n r : ℕ) (hr : r = 2 ∨ r = 3) (hlt : r < n)
    (hpar : n % 2 = r % 2) (hgap : 4 ≤ n - r) (hodd : Odd (n.choose r)) :
    ∃ δ : Target n r → Target n r,
      Function.Involutive δ ∧ (∀ a, δ a ≠ a) ∧
        ∀ a, Challenge.Compat a.val (δ a).val := by
  classical
  have hle : r ≤ n := Nat.le_of_lt hlt
  have hn : r + 2 ≤ n := by omega
  obtain ⟨k, e, hbound⟩ :=
    BrauerMatchingLabels.exists_label_pairing n r hr hlt hpar hgap hodd
  obtain ⟨rep, hspecial, hp⟩ :=
    exists_representatives n r hr hle hn hpar k e hbound
  let d : (Fin k × Bool) ≃ BrauerMatchingTransport.Nonspecial (special n r) :=
    e.trans (remainingEquivNonspecial n r)
  let τ : BrauerMatchingTransport.Nonspecial (special n r) →
      BrauerMatchingTransport.Nonspecial (special n r) :=
    fun a => d (pairFlip (d.symm a))
  have hτI : Function.Involutive τ := by
    intro a
    change d (pairFlip (d.symm (d (pairFlip (d.symm a))))) = a
    rw [d.symm_apply_apply, pairFlip_involutive k (d.symm a), d.apply_symm_apply]
  have hτN : ∀ a, τ a ≠ a := by
    intro a ha
    apply pairFlip_ne k (d.symm a)
    have he := congrArg d.symm ha
    change d.symm (d (pairFlip (d.symm a))) = d.symm a at he
    exact (d.symm_apply_apply (pairFlip (d.symm a))).symm.trans he
  have hτ : ∀ (i : Fin k) (b : Bool), τ (d (i, b)) = d (i, !b) := by
    intro i b
    change d (pairFlip (d.symm (d (i, b)))) = d (i, !b)
    rw [d.symm_apply_apply]
    rfl
  have hq : ∀ F : HalfCounting.FreeSets n r,
      ∃ q : BrauerMatchingTransport.Remainder (Fib n r) rep F →
          BrauerMatchingTransport.Remainder (Fib n r) rep F,
        Function.Involutive q ∧ ∀ a, q a ≠ a :=
    exists_fibre_pairing n r hle hpar rep
  choose q hqI hqN using hq
  let Q : (Σ F : HalfCounting.FreeSets n r, Fib n r F) →
      (Σ F : HalfCounting.FreeSets n r, Fib n r F) → Prop :=
    fun z w => Challenge.Compat z.2.val w.2.val
  have hrep : ∀ a : BrauerMatchingTransport.Nonspecial (special n r),
      Q ⟨a.val, rep a.val⟩ ⟨(τ a).val, rep (τ a).val⟩ := by
    intro a
    obtain ⟨⟨i, b⟩, rfl⟩ := d.surjective a
    rw [hτ i b]
    cases b
    · change Challenge.Compat (rep (e (i, false)).val).val
        (rep (e (i, true)).val).val
      exact hp i
    · change Challenge.Compat (rep (e (i, true)).val).val
        (rep (e (i, false)).val).val
      exact GammaCompatibility.compat_symm
        (rep (e (i, false)).val).property.1
        (rep (e (i, true)).val).property.1 (hp i)
  have hrem : ∀ (F : HalfCounting.FreeSets n r)
      (a : BrauerMatchingTransport.Remainder (Fib n r) rep F),
      Q ⟨F, a.val⟩ ⟨F, (q F a).val⟩ := by
    intro F a
    change Challenge.Compat a.val.val (q F a).val.val
    exact HalfDiagonal.compat_of_same_free
      (a.val.property.2.trans (q F a).val.property.2.symm)
  obtain ⟨δ, hδI, hδN, hδQ⟩ := BrauerMatchingTransport.exists_pairing
    (Fib n r) rep (special n r) τ q hτI hτN hqI hqN Q hrep hrem
  let E := targetEquivAllowed n r rep hspecial
  let δT : Target n r → Target n r := fun a => E.symm (δ (E a))
  refine ⟨δT, ?_, ?_, ?_⟩
  · intro a
    change E.symm (δ (E (E.symm (δ (E a))))) = a
    rw [E.apply_symm_apply, hδI (E a), E.symm_apply_apply]
  · intro a ha
    apply hδN (E a)
    have he := congrArg E ha
    change E (E.symm (δ (E a))) = E a at he
    exact (E.apply_symm_apply (δ (E a))).symm.trans he
  · intro a
    exact hδQ (E a)

/-- Extend the actual target involution to all Half values, fixing its complement. -/
theorem extend_target_pairing (n r : ℕ) (d : Target n r → Target n r)
    (hdI : Function.Involutive d) (hdN : ∀ a, d a ≠ a)
    (hdC : ∀ a, Challenge.Compat a.val (d a).val) :
    ∃ δ : Challenge.Half n → Challenge.Half n,
      ∀ v ∈ targetSet n r, δ v ∈ targetSet n r ∧
        δ (δ v) = v ∧ δ v ≠ v ∧ Challenge.Compat v (δ v) := by
  classical
  let f : Challenge.Half n → Challenge.Half n :=
    fun v => if hv : v ∈ targetSet n r then (d ⟨v, hv⟩).val else v
  refine ⟨f, ?_⟩
  intro v hv
  let a : Target n r := ⟨v, hv⟩
  have hf : f v = (d a).val := by
    simp only [f, a, dite_eq_left hv]
  have hmem : f v ∈ targetSet n r := by
    rw [hf]
    exact (d a).property
  refine ⟨hmem, ?_, ?_, ?_⟩
  · have hsecond : f (d a).val = (d (d a)).val := by
      simp only [f, dite_eq_left (d a).property]
    rw [hf, hsecond]
    exact congrArg Subtype.val (hdI a)
  · intro heq
    exact hdN a (Subtype.ext (hf.symm.trans heq))
  · rw [hf]
    exact hdC a

theorem check_Lemma54 : Challenge.Lemma54 := by
  intro n r hr hlt hpar hgap hodd
  obtain ⟨d, hdI, hdN, hdC⟩ := exists_target_pairing n r hr hlt hpar hgap hodd
  exact extend_target_pairing n r d hdI hdN hdC

#print axioms CodexPaper5.BrauerMatching.pairFlip
#print axioms CodexPaper5.BrauerMatching.pairFlip_involutive
#print axioms CodexPaper5.BrauerMatching.pairFlip_ne
#print axioms CodexPaper5.BrauerMatching.exists_target_pairing
#print axioms CodexPaper5.BrauerMatching.extend_target_pairing
#print axioms CodexPaper5.BrauerMatching.check_Lemma54

end CodexPaper5.BrauerMatching
