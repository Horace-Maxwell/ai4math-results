import Research.Backfill.Paper5.Challenge

set_option autoImplicit false

namespace CodexPaper5.InvolutionCounting

open BackfillPaper5
open scoped Nat

abbrev Inv (A : Type*) := {f : A → A // Function.Involutive f}

abbrev Pairing (A : Type*) :=
  {f : A → A // Function.Involutive f ∧ ∀ a, f a ≠ a}

variable {A B : Type*}

def conjugate (e : A ≃ B) (f : A → A) : B → B := fun b => e (f (e.symm b))

theorem conjugate_involutive (e : A ≃ B) (f : A → A) (hf : Function.Involutive f) :
    Function.Involutive (conjugate e f) := by
  intro b
  change e (f (e.symm (e (f (e.symm b))))) = b
  rw [e.symm_apply_apply, hf, e.apply_symm_apply]

theorem conjugate_ne (e : A ≃ B) (f : A → A) (hf : ∀ a, f a ≠ a) :
    ∀ b, conjugate e f b ≠ b := by
  intro b h
  apply hf (e.symm b)
  apply e.injective
  simpa only [conjugate, e.apply_symm_apply] using h

noncomputable def invCongr (e : A ≃ B) : Inv A ≃ Inv B where
  toFun f := ⟨conjugate e f.val, conjugate_involutive e f.val f.property⟩
  invFun g := ⟨conjugate e.symm g.val, conjugate_involutive e.symm g.val g.property⟩
  left_inv f := by
    apply Subtype.ext
    funext a
    change e.symm (e (f.val (e.symm (e a)))) = f.val a
    simp only [e.symm_apply_apply]
  right_inv g := by
    apply Subtype.ext
    funext b
    change e (e.symm (g.val (e (e.symm b)))) = g.val b
    simp only [e.apply_symm_apply]

noncomputable def pairingCongr (e : A ≃ B) : Pairing A ≃ Pairing B where
  toFun f := ⟨conjugate e f.val, conjugate_involutive e f.val f.property.1,
    conjugate_ne e f.val f.property.2⟩
  invFun g := ⟨conjugate e.symm g.val, conjugate_involutive e.symm g.val g.property.1,
    conjugate_ne e.symm g.val g.property.2⟩
  left_inv f := by
    apply Subtype.ext
    funext a
    change e.symm (e (f.val (e.symm (e a)))) = f.val a
    simp only [e.symm_apply_apply]
  right_inv g := by
    apply Subtype.ext
    funext b
    change e (e.symm (g.val (e (e.symm b)))) = g.val b
    simp only [e.apply_symm_apply]

def invToPerm (f : Inv A) : Equiv.Perm A where
  toFun := f.val
  invFun := f.val
  left_inv := f.property
  right_inv := f.property

theorem invToPerm_mul_self (f : Inv A) : invToPerm f * invToPerm f = 1 := by
  apply Equiv.ext
  intro a
  exact f.property a

def invPermEquiv (A : Type*) : Inv A ≃ {σ : Equiv.Perm A // σ * σ = 1} where
  toFun f := ⟨invToPerm f, invToPerm_mul_self f⟩
  invFun σ := ⟨fun a => σ.val a, by
    intro a
    exact congrArg (fun p : Equiv.Perm A => p a) σ.property⟩
  left_inv f := by
    apply Subtype.ext
    rfl
  right_inv σ := by
    apply Subtype.ext
    apply Equiv.ext
    intro a
    rfl

theorem card_inv (A : Type*) [Fintype A] :
    Nat.card (Inv A) = Challenge.invCount (Fintype.card A) := by
  calc
    Nat.card (Inv A) = Nat.card (Inv (Fin (Fintype.card A))) :=
      Nat.card_congr (invCongr (Fintype.equivFin A))
    _ = Challenge.invCount (Fintype.card A) :=
      Nat.card_congr (invPermEquiv (Fin (Fintype.card A)))

abbrev Partner (a : A) := {b : A // b ≠ a}

abbrev Rest (a b : A) := {x : A // x ≠ a ∧ x ≠ b}

abbrev PartnerData (a : A) := Σ b : Partner a, Pairing (Rest a b.val)

/-- Restriction is well defined because a and its partner form a full two-cycle. -/
def restrictFun (a : A) (f : Pairing A) (x : Rest a (f.val a)) : Rest a (f.val a) :=
  ⟨f.val x.val,
    (fun h => x.property.2 ((f.property.1 x.val).symm.trans (congrArg f.val h))),
    (fun h => x.property.1 ((f.property.1 x.val).symm.trans
      ((congrArg f.val h).trans (f.property.1 a))))⟩

def restrictPairing (a : A) (f : Pairing A) : Pairing (Rest a (f.val a)) :=
  ⟨restrictFun a f,
    (by
      intro x
      apply Subtype.ext
      exact f.property.1 x.val),
    (by
      intro x h
      exact f.property.2 x.val (congrArg Subtype.val h))⟩

def splitPairing (a : A) (f : Pairing A) : PartnerData a :=
  ⟨⟨f.val a, f.property.2 a⟩, restrictPairing a f⟩

/-- Restore the selected two-cycle and the actual pairing on the remaining points. -/
def joinFun [DecidableEq A] (a : A) (b : Partner a) (q : Pairing (Rest a b.val)) (x : A) : A :=
  if ha : x = a then b.val
  else if hb : x = b.val then a
  else (q.val ⟨x, ha, hb⟩).val

theorem joinFun_at_a [DecidableEq A] (a : A) (b : Partner a) (q : Pairing (Rest a b.val)) :
    joinFun a b q a = b.val := by
  unfold joinFun
  rw [dite_eq_left (show a = a from rfl)]

theorem joinFun_at_b [DecidableEq A] (a : A) (b : Partner a) (q : Pairing (Rest a b.val)) :
    joinFun a b q b.val = a := by
  unfold joinFun
  rw [dite_eq_right b.property, dite_eq_left (show b.val = b.val from rfl)]

theorem joinFun_at_rest [DecidableEq A] (a : A) (b : Partner a)
    (q : Pairing (Rest a b.val)) (x : Rest a b.val) :
    joinFun a b q x.val = (q.val x).val := by
  simp only [joinFun, dite_eq_right x.property.1, dite_eq_right x.property.2]

theorem joinFun_involutive [DecidableEq A] (a : A) (b : Partner a)
    (q : Pairing (Rest a b.val)) : Function.Involutive (joinFun a b q) := by
  intro x
  by_cases ha : x = a
  · subst x
    rw [joinFun_at_a, joinFun_at_b]
  · by_cases hb : x = b.val
    · subst x
      rw [joinFun_at_b, joinFun_at_a]
    · let c : Rest a b.val := ⟨x, ha, hb⟩
      have hfirst : joinFun a b q x = (q.val c).val := joinFun_at_rest a b q c
      rw [hfirst, joinFun_at_rest a b q (q.val c)]
      exact congrArg Subtype.val (q.property.1 c)

theorem joinFun_ne [DecidableEq A] (a : A) (b : Partner a)
    (q : Pairing (Rest a b.val)) : ∀ x, joinFun a b q x ≠ x := by
  intro x h
  by_cases ha : x = a
  · subst x
    exact b.property ((joinFun_at_a a b q).symm.trans h)
  · by_cases hb : x = b.val
    · subst x
      exact b.property (((joinFun_at_b a b q).symm.trans h).symm)
    · let c : Rest a b.val := ⟨x, ha, hb⟩
      have hc : (q.val c).val = c.val := (joinFun_at_rest a b q c).symm.trans h
      exact q.property.2 c (Subtype.ext hc)

def joinPairing [DecidableEq A] (a : A) (t : PartnerData a) : Pairing A :=
  ⟨joinFun a t.1 t.2, joinFun_involutive a t.1 t.2, joinFun_ne a t.1 t.2⟩

theorem join_split [DecidableEq A] (a : A) (f : Pairing A) :
    joinPairing a (splitPairing a f) = f := by
  apply Subtype.ext
  funext x
  let b : Partner a := ⟨f.val a, f.property.2 a⟩
  change joinFun a b (restrictPairing a f) x = f.val x
  by_cases ha : x = a
  · subst x
    exact joinFun_at_a a b (restrictPairing a f)
  · by_cases hb : x = f.val a
    · subst x
      rw [joinFun_at_b]
      exact (f.property.1 a).symm
    · let c : Rest a (f.val a) := ⟨x, ha, hb⟩
      exact joinFun_at_rest a b (restrictPairing a f) c

/-- Recover the partner by evaluation at a, then recover the whole remaining function. -/
theorem joinPairing_injective [DecidableEq A] (a : A) : Function.Injective (joinPairing a) := by
  rintro ⟨b, q⟩ ⟨c, s⟩ h
  have hbc : b = c := by
    apply Subtype.ext
    have ha := congrArg (fun f : Pairing A => f.val a) h
    exact (joinFun_at_a a b q).symm.trans (ha.trans (joinFun_at_a a c s))
  cases hbc
  have hqs : q = s := by
    apply Subtype.ext
    funext x
    apply Subtype.ext
    have hx := congrArg (fun f : Pairing A => f.val x.val) h
    exact (joinFun_at_rest a b q x).symm.trans (hx.trans (joinFun_at_rest a b s x))
  cases hqs
  rfl

theorem split_join [DecidableEq A] (a : A) (t : PartnerData a) :
    splitPairing a (joinPairing a t) = t := by
  apply joinPairing_injective a
  exact join_split a (joinPairing a t)

noncomputable def partnerEquiv (a : A) : Pairing A ≃ PartnerData a := by
  classical
  exact
    { toFun := splitPairing a
      invFun := joinPairing a
      left_inv := join_split a
      right_inv := split_join a }

theorem card_partner [Fintype A] [DecidableEq A] (a : A) :
    Fintype.card (Partner a) = Fintype.card A - 1 := by
  calc
    Fintype.card (Partner a) = (Finset.univ.erase a).card :=
      Fintype.card_of_subtype _ (by intro x; simp)
    _ = Fintype.card A - 1 := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ a), Finset.card_univ]

theorem card_rest [Fintype A] [DecidableEq A] (a : A) (b : Partner a) :
    Fintype.card (Rest a b.val) = Fintype.card A - 2 := by
  have hb : b.val ∈ Finset.univ.erase a := by simp [b.property]
  calc
    Fintype.card (Rest a b.val) = ((Finset.univ.erase a).erase b.val).card :=
      Fintype.card_of_subtype _ (by intro x; simp [and_comm])
    _ = (Fintype.card A - 1) - 1 := by
      rw [Finset.card_erase_of_mem hb, Finset.card_erase_of_mem (Finset.mem_univ a),
        Finset.card_univ]
    _ = Fintype.card A - 2 := by omega

theorem card_pairing_step (m : ℕ) :
    Nat.card (Pairing (Fin (2 * m + 2))) =
      (2 * m + 1) * Nat.card (Pairing (Fin (2 * m))) := by
  classical
  let a : Fin (2 * m + 2) := ⟨0, by omega⟩
  have hbcard : Fintype.card (Partner a) = 2 * m + 1 := by
    rw [card_partner, Fintype.card_fin]
    omega
  have hrest (b : Partner a) : Fintype.card (Rest a b.val) = 2 * m := by
    rw [card_rest, Fintype.card_fin]
    omega
  have hfib (b : Partner a) :
      Nat.card (Pairing (Rest a b.val)) = Nat.card (Pairing (Fin (2 * m))) :=
    Nat.card_congr (pairingCongr (Fintype.equivFinOfCardEq (hrest b)))
  calc
    Nat.card (Pairing (Fin (2 * m + 2))) = Nat.card (PartnerData a) :=
      Nat.card_congr (partnerEquiv a)
    _ = ∑ b : Partner a, Nat.card (Pairing (Rest a b.val)) := Nat.card_sigma
    _ = ∑ _b : Partner a, Nat.card (Pairing (Fin (2 * m))) :=
      Finset.sum_congr rfl (fun b _ => hfib b)
    _ = (2 * m + 1) * Nat.card (Pairing (Fin (2 * m))) := by
      simp only [Finset.sum_const, Finset.card_univ, hbcard, nsmul_eq_mul, Nat.cast_id]

theorem card_pairing_zero : Nat.card (Pairing (Fin 0)) = 1 := by
  let z : Pairing (Fin 0) :=
    ⟨id, (by intro a; rfl), (by intro a; exact Fin.elim0 a)⟩
  exact Nat.card_of_subsingleton z

theorem card_pairing_even_fin (m : ℕ) :
    Nat.card (Pairing (Fin (2 * m))) = (2 * m - 1)‼ := by
  induction m with
  | zero => simpa only [Nat.mul_zero, Nat.zero_sub, Nat.doubleFactorial] using card_pairing_zero
  | succ m ih =>
    have hs : 2 * (m + 1) = 2 * m + 2 := by omega
    rw [hs, card_pairing_step, ih]
    have hp : 2 * m + 2 - 1 = 2 * m + 1 := by omega
    rw [hp, Nat.doubleFactorial_add_one]

theorem odd_doubleFactorial_even_pred (m : ℕ) : Odd ((2 * m - 1)‼) := by
  induction m with
  | zero => exact ⟨0, rfl⟩
  | succ m ih =>
    have hs : 2 * (m + 1) - 1 = 2 * m + 1 := by omega
    rw [hs, Nat.doubleFactorial_add_one]
    exact (show Odd (2 * m + 1) from ⟨m, rfl⟩).mul ih

theorem card_pairing (A : Type*) [Fintype A] (h : Even (Fintype.card A)) :
    Nat.card (Pairing A) = (Fintype.card A - 1)‼ := by
  obtain ⟨m, hm⟩ := h
  have hc : Fintype.card A = 2 * m := by omega
  calc
    Nat.card (Pairing A) = Nat.card (Pairing (Fin (2 * m))) :=
      Nat.card_congr (pairingCongr (Fintype.equivFinOfCardEq hc))
    _ = (2 * m - 1)‼ := card_pairing_even_fin m
    _ = (Fintype.card A - 1)‼ := by rw [hc]

theorem odd_doubleFactorial_pred {k : ℕ} (h : Even k) : Odd ((k - 1)‼) := by
  obtain ⟨m, hm⟩ := h
  have hk : k = 2 * m := by omega
  rw [hk]
  exact odd_doubleFactorial_even_pred m

#print axioms CodexPaper5.InvolutionCounting.Inv
#print axioms CodexPaper5.InvolutionCounting.Pairing
#print axioms CodexPaper5.InvolutionCounting.conjugate
#print axioms CodexPaper5.InvolutionCounting.conjugate_involutive
#print axioms CodexPaper5.InvolutionCounting.conjugate_ne
#print axioms CodexPaper5.InvolutionCounting.invCongr
#print axioms CodexPaper5.InvolutionCounting.pairingCongr
#print axioms CodexPaper5.InvolutionCounting.invToPerm
#print axioms CodexPaper5.InvolutionCounting.invToPerm_mul_self
#print axioms CodexPaper5.InvolutionCounting.invPermEquiv
#print axioms CodexPaper5.InvolutionCounting.card_inv
#print axioms CodexPaper5.InvolutionCounting.Partner
#print axioms CodexPaper5.InvolutionCounting.Rest
#print axioms CodexPaper5.InvolutionCounting.PartnerData
#print axioms CodexPaper5.InvolutionCounting.restrictFun
#print axioms CodexPaper5.InvolutionCounting.restrictPairing
#print axioms CodexPaper5.InvolutionCounting.splitPairing
#print axioms CodexPaper5.InvolutionCounting.joinFun
#print axioms CodexPaper5.InvolutionCounting.joinFun_at_a
#print axioms CodexPaper5.InvolutionCounting.joinFun_at_b
#print axioms CodexPaper5.InvolutionCounting.joinFun_at_rest
#print axioms CodexPaper5.InvolutionCounting.joinFun_involutive
#print axioms CodexPaper5.InvolutionCounting.joinFun_ne
#print axioms CodexPaper5.InvolutionCounting.joinPairing
#print axioms CodexPaper5.InvolutionCounting.join_split
#print axioms CodexPaper5.InvolutionCounting.joinPairing_injective
#print axioms CodexPaper5.InvolutionCounting.split_join
#print axioms CodexPaper5.InvolutionCounting.partnerEquiv
#print axioms CodexPaper5.InvolutionCounting.card_partner
#print axioms CodexPaper5.InvolutionCounting.card_rest
#print axioms CodexPaper5.InvolutionCounting.card_pairing_step
#print axioms CodexPaper5.InvolutionCounting.card_pairing_zero
#print axioms CodexPaper5.InvolutionCounting.card_pairing_even_fin
#print axioms CodexPaper5.InvolutionCounting.odd_doubleFactorial_even_pred
#print axioms CodexPaper5.InvolutionCounting.card_pairing
#print axioms CodexPaper5.InvolutionCounting.odd_doubleFactorial_pred

end CodexPaper5.InvolutionCounting
