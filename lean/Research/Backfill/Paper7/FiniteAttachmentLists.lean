import Research.Backfill.Paper7.ChallengeV2

/-! Source-only finite bookkeeping. Empty fibers give empty lists; positive
lengths are not needed for the equivalences. No mathematical enumeration is run. -/
set_option autoImplicit false
noncomputable section
namespace Paper7SunAssembly
open BackfillPaper7.Challenge
open scoped Classical

def attachmentFiberEnum {C : Type} [Fintype C] {b : ℕ}
    (root : C → Fin b) (k : Fin b) :
    Fin (Fintype.card {c // root c = k}) ≃ {c // root c = k} :=
  (Fintype.equivFin {c // root c = k}).symm
#print axioms Paper7SunAssembly.attachmentFiberEnum

def attachmentLengths {C : Type} [Fintype C] {b : ℕ}
    (root : C → Fin b) (len : C → ℕ) (k : Fin b) : List ℕ :=
  List.ofFn (fun j => len ((attachmentFiberEnum root k) j).val)
#print axioms Paper7SunAssembly.attachmentLengths

def attachmentBlockEquiv {C : Type} [Fintype C] {b : ℕ}
    (root : C → Fin b) (len : C → ℕ) :
    (Σ k : Fin b, Fin (attachmentLengths root len k).length) ≃ C :=
  (Equiv.sigmaCongrRight fun k =>
    (finCongr (by simp only [attachmentLengths, List.length_ofFn])).trans
      (attachmentFiberEnum root k)).trans (Equiv.sigmaFiberEquiv root)
#print axioms Paper7SunAssembly.attachmentBlockEquiv

theorem attachmentBlock_root {C : Type} [Fintype C] {b : ℕ}
    (root : C → Fin b) (len : C → ℕ) (k : Fin b)
    (j : Fin (attachmentLengths root len k).length) :
    root (attachmentBlockEquiv root len ⟨k, j⟩) = k := by
  exact ((attachmentFiberEnum root k)
    (Fin.cast (by simp only [attachmentLengths, List.length_ofFn]) j)).property
#print axioms Paper7SunAssembly.attachmentBlock_root

theorem attachmentLengths_get {C : Type} [Fintype C] {b : ℕ}
    (root : C → Fin b) (len : C → ℕ) (k : Fin b)
    (j : Fin (attachmentLengths root len k).length) :
    (attachmentLengths root len k).get j = len (attachmentBlockEquiv root len ⟨k, j⟩) := by
  change (List.ofFn (fun i => len ((attachmentFiberEnum root k) i).val)).get j = _
  exact List.get_ofFn (fun i => len ((attachmentFiberEnum root k) i).val) j
#print axioms Paper7SunAssembly.attachmentLengths_get

theorem attachmentBlock_eq_iff {C : Type} [Fintype C] {b : ℕ}
    (root : C → Fin b) (len : C → ℕ) (k k' : Fin b)
    (j : Fin (attachmentLengths root len k).length)
    (j' : Fin (attachmentLengths root len k').length) :
    attachmentBlockEquiv root len ⟨k, j⟩ = attachmentBlockEquiv root len ⟨k', j'⟩ ↔
      k = k' ∧ j.val = j'.val := by
  constructor
  · intro h
    have he := (attachmentBlockEquiv root len).injective h
    exact ⟨congrArg Sigma.fst he,
      congrArg (fun q : Σ k : Fin b, Fin (attachmentLengths root len k).length => q.2.val) he⟩
  · rintro ⟨rfl, hj⟩
    have h : j = j' := Fin.ext hj
    cases h
    rfl
#print axioms Paper7SunAssembly.attachmentBlock_eq_iff

def attachmentArmEquiv {C : Type} [Fintype C] {b : ℕ}
    (root : C → Fin b) (len : C → ℕ) :
    (Σ k : Fin b, Σ j : Fin (attachmentLengths root len k).length,
      Fin ((attachmentLengths root len k).get j)) ≃ Σ c : C, Fin (len c) :=
  (Equiv.sigmaAssoc (fun k j => Fin ((attachmentLengths root len k).get j))).symm.trans
    (Equiv.sigmaCongr (attachmentBlockEquiv root len)
      (fun q => finCongr (attachmentLengths_get root len q.1 q.2)))
#print axioms Paper7SunAssembly.attachmentArmEquiv

theorem attachmentLengths_pos {C : Type} [Fintype C] {b : ℕ}
    (root : C → Fin b) (len : C → ℕ) (hpos : ∀ c, 0 < len c)
    (k : Fin b) (j : Fin (attachmentLengths root len k).length) :
    0 < (attachmentLengths root len k).get j := by
  rw [attachmentLengths_get]
  exact hpos _
#print axioms Paper7SunAssembly.attachmentLengths_pos

theorem attachmentLengths_empty_fiber {C : Type} [Fintype C] {b : ℕ}
    (root : C → Fin b) (len : C → ℕ) (k : Fin b)
    (h : ∀ c, root c ≠ k) : attachmentLengths root len k = [] := by
  have hcard : Fintype.card {c // root c = k} = 0 :=
    Fintype.card_eq_zero_iff.mpr ⟨fun c => h c.val c.property⟩
  apply List.length_eq_zero_iff.mp
  simpa only [attachmentLengths, List.length_ofFn] using hcard
#print axioms Paper7SunAssembly.attachmentLengths_empty_fiber

end Paper7SunAssembly
