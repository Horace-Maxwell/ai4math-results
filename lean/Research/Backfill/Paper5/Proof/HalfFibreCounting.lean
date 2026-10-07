import Research.Backfill.Paper5.Proof.InvolutionCounting

set_option autoImplicit false

namespace CodexPaper5.HalfFibreCounting

open BackfillPaper5
open scoped Nat

abbrev Fibre (D : Challenge.Fam) (n r : ℕ) (F : Finset (Fin n)) :=
  {h : Challenge.Half n // h ∈ Challenge.Hr D n r ∧ h.1 = F}

/-- Fix the specified free set and act by the actual complement function elsewhere. -/
def extend {n : ℕ} (F : Finset (Fin n)) (f : ↥(Fᶜ) → ↥(Fᶜ)) (a : Fin n) : Fin n :=
  if ha : a ∈ F then a else (f ⟨a, Finset.mem_compl.mpr ha⟩).val

theorem extend_of_mem {n : ℕ} (F : Finset (Fin n)) (f : ↥(Fᶜ) → ↥(Fᶜ))
    {a : Fin n} (ha : a ∈ F) : extend F f a = a := by
  simp only [extend, dite_eq_left ha]

theorem extend_coe {n : ℕ} (F : Finset (Fin n)) (f : ↥(Fᶜ) → ↥(Fᶜ)) (a : ↥(Fᶜ)) :
    extend F f a.val = (f a).val := by
  have ha : a.val ∉ F := Finset.mem_compl.mp a.property
  simp only [extend, dite_eq_right ha]

theorem extend_involutive {n : ℕ} (F : Finset (Fin n)) (f : ↥(Fᶜ) → ↥(Fᶜ))
    (hf : Function.Involutive f) : Function.Involutive (extend F f) := by
  intro a
  by_cases ha : a ∈ F
  · simp only [extend_of_mem F f ha]
  · let c : ↥(Fᶜ) := ⟨a, Finset.mem_compl.mpr ha⟩
    have hfirst : extend F f a = (f c).val := extend_coe F f c
    rw [hfirst, extend_coe F f (f c)]
    exact congrArg Subtype.val (hf c)

theorem extend_ne {n : ℕ} (F : Finset (Fin n)) (f : ↥(Fᶜ) → ↥(Fᶜ))
    (hf : ∀ c, f c ≠ c) {a : Fin n} (ha : a ∉ F) : extend F f a ≠ a := by
  intro h
  let c : ↥(Fᶜ) := ⟨a, Finset.mem_compl.mpr ha⟩
  have hc : (f c).val = c.val := (extend_coe F f c).symm.trans h
  exact hf c (Subtype.ext hc)

theorem fibre_fixed {D : Challenge.Fam} {n r : ℕ} {F : Finset (Fin n)}
    (h : Fibre D n r F) {a : Fin n} (ha : a ∈ F) : h.val.2 a = a := by
  apply h.property.1.2.2.1 a
  rwa [h.property.2]

theorem fibre_maps_complement {D : Challenge.Fam} {n r : ℕ} {F : Finset (Fin n)}
    (h : Fibre D n r F) (a : ↥(Fᶜ)) : h.val.2 a.val ∈ Fᶜ := by
  apply Finset.mem_compl.mpr
  intro hf
  have heq : h.val.2 a.val = a.val :=
    (fibre_fixed h hf).symm.trans (h.property.1.2.1 a.val)
  exact (Finset.mem_compl.mp a.property) (heq ▸ hf)

/-- Restriction is well-defined by the actual global involution and fixed free set. -/
def restrict {D : Challenge.Fam} {n r : ℕ} {F : Finset (Fin n)}
    (h : Fibre D n r F) : InvolutionCounting.Inv ↥(Fᶜ) :=
  ⟨fun a => ⟨h.val.2 a.val, fibre_maps_complement h a⟩, by
    intro a
    apply Subtype.ext
    exact h.property.1.2.1 a.val⟩

theorem extend_restrict {D : Challenge.Fam} {n r : ℕ} {F : Finset (Fin n)}
    (h : Fibre D n r F) : (F, extend F (restrict h).val) = h.val := by
  apply Prod.ext h.property.2.symm
  funext a
  by_cases ha : a ∈ F
  · exact (extend_of_mem F (restrict h).val ha).trans (fibre_fixed h ha).symm
  · let c : ↥(Fᶜ) := ⟨a, Finset.mem_compl.mpr ha⟩
    exact extend_coe F (restrict h).val c

def fromInv {n r : ℕ} {F : Finset (Fin n)} (hF : F.card = r)
    (f : InvolutionCounting.Inv ↥(Fᶜ)) : Fibre Challenge.Fam.PB n r F :=
  ⟨(F, extend F f.val), ⟨hF, extend_involutive F f.val f.property,
    fun a ha => extend_of_mem F f.val ha, by intro hD; cases hD⟩, rfl⟩

/-- Both inverse laws concern the entire frozen Half, including its whole-domain function. -/
def invEquiv {n r : ℕ} {F : Finset (Fin n)} (hF : F.card = r) :
    Fibre Challenge.Fam.PB n r F ≃ InvolutionCounting.Inv ↥(Fᶜ) where
  toFun := restrict
  invFun := fromInv hF
  left_inv h := by
    apply Subtype.ext
    exact extend_restrict h
  right_inv f := by
    apply Subtype.ext
    funext a
    apply Subtype.ext
    exact extend_coe F f.val a

def restrictPairing {n r : ℕ} {F : Finset (Fin n)}
    (h : Fibre Challenge.Fam.B n r F) : InvolutionCounting.Pairing ↥(Fᶜ) :=
  ⟨(restrict h).val, (restrict h).property, by
    intro a ha
    have hma : h.val.2 a.val = a.val := congrArg Subtype.val ha
    have hfree : a.val ∉ h.val.1 := by
      rw [h.property.2]
      exact Finset.mem_compl.mp a.property
    exact h.property.1.2.2.2 rfl a.val hfree hma⟩

def fromPairing {n r : ℕ} {F : Finset (Fin n)} (hF : F.card = r)
    (f : InvolutionCounting.Pairing ↥(Fᶜ)) : Fibre Challenge.Fam.B n r F :=
  ⟨(F, extend F f.val), ⟨hF, extend_involutive F f.val f.property.1,
    fun _a ha => extend_of_mem F f.val ha,
    fun _hD _a ha => extend_ne F f.val f.property.2 ha⟩, rfl⟩

def pairingEquiv {n r : ℕ} {F : Finset (Fin n)} (hF : F.card = r) :
    Fibre Challenge.Fam.B n r F ≃ InvolutionCounting.Pairing ↥(Fᶜ) where
  toFun := restrictPairing
  invFun := fromPairing hF
  left_inv h := by
    apply Subtype.ext
    exact extend_restrict h
  right_inv f := by
    apply Subtype.ext
    funext a
    apply Subtype.ext
    exact extend_coe F f.val a

theorem complement_card {n r : ℕ} {F : Finset (Fin n)} (hF : F.card = r) :
    Fintype.card ↥(Fᶜ) = n - r := by
  simp only [Fintype.card_coe, Finset.card_compl, Fintype.card_fin, hF]

theorem card_fibre_PB {n r : ℕ} {F : Finset (Fin n)} (hF : F.card = r) :
    Nat.card (Fibre Challenge.Fam.PB n r F) = Challenge.invCount (n - r) := by
  calc
    Nat.card (Fibre Challenge.Fam.PB n r F) = Nat.card (InvolutionCounting.Inv ↥(Fᶜ)) :=
      Nat.card_congr (invEquiv hF)
    _ = Challenge.invCount (Fintype.card ↥(Fᶜ)) := InvolutionCounting.card_inv ↥(Fᶜ)
    _ = Challenge.invCount (n - r) := congrArg Challenge.invCount (complement_card hF)

theorem even_complement {n r : ℕ} (hle : r ≤ n) (hpar : r % 2 = n % 2) :
    Even (n - r) := by
  rw [Nat.even_iff]
  omega

theorem card_fibre_B {n r : ℕ} {F : Finset (Fin n)} (hF : F.card = r)
    (hle : r ≤ n) (hpar : r % 2 = n % 2) :
    Nat.card (Fibre Challenge.Fam.B n r F) = (n - r - 1)‼ := by
  have heven : Even (Fintype.card ↥(Fᶜ)) := by
    rw [complement_card hF]
    exact even_complement hle hpar
  calc
    Nat.card (Fibre Challenge.Fam.B n r F) = Nat.card (InvolutionCounting.Pairing ↥(Fᶜ)) :=
      Nat.card_congr (pairingEquiv hF)
    _ = (Fintype.card ↥(Fᶜ) - 1)‼ := InvolutionCounting.card_pairing ↥(Fᶜ) heven
    _ = (n - r - 1)‼ := by rw [complement_card hF]

theorem check_FibreCount : Challenge.FibreCount := by
  intro n r hle hpar F hF
  constructor
  · change Nat.card (Fibre Challenge.Fam.B n r F) = (n - r - 1)‼
    exact card_fibre_B hF hle hpar
  · exact InvolutionCounting.odd_doubleFactorial_pred (even_complement hle hpar)

#print axioms CodexPaper5.HalfFibreCounting.Fibre
#print axioms CodexPaper5.HalfFibreCounting.extend
#print axioms CodexPaper5.HalfFibreCounting.extend_of_mem
#print axioms CodexPaper5.HalfFibreCounting.extend_coe
#print axioms CodexPaper5.HalfFibreCounting.extend_involutive
#print axioms CodexPaper5.HalfFibreCounting.extend_ne
#print axioms CodexPaper5.HalfFibreCounting.fibre_fixed
#print axioms CodexPaper5.HalfFibreCounting.fibre_maps_complement
#print axioms CodexPaper5.HalfFibreCounting.restrict
#print axioms CodexPaper5.HalfFibreCounting.extend_restrict
#print axioms CodexPaper5.HalfFibreCounting.fromInv
#print axioms CodexPaper5.HalfFibreCounting.invEquiv
#print axioms CodexPaper5.HalfFibreCounting.restrictPairing
#print axioms CodexPaper5.HalfFibreCounting.fromPairing
#print axioms CodexPaper5.HalfFibreCounting.pairingEquiv
#print axioms CodexPaper5.HalfFibreCounting.complement_card
#print axioms CodexPaper5.HalfFibreCounting.card_fibre_PB
#print axioms CodexPaper5.HalfFibreCounting.even_complement
#print axioms CodexPaper5.HalfFibreCounting.card_fibre_B
#print axioms CodexPaper5.HalfFibreCounting.check_FibreCount

end CodexPaper5.HalfFibreCounting
