import Research.Backfill.Paper5.Proof.ReesCoreCompat
import Research.Backfill.Paper5.Proof.Lemma42

set_option autoImplicit false

namespace CodexPaper5

open BackfillPaper5 Function

namespace ReesEven

/-- The previously proved explicit map B has exactly the frozen multiplication and map.
The parity image of the identity diagonal is the zero diagonal required by that proof. -/
theorem fB_complete {r : ℕ} {H : Type} [Finite H]
    (P : H → H → Option (Challenge.Sym r)) (hdiag : ∀ l, P l l = some 1)
    (L : H → H → H) (δ : Equiv.Perm H) (t : H → ZMod 2)
    (hL : Challenge.IsLatin L) (ht : ∀ μ, t (δ μ) = t μ + 1) :
    Challenge.IsCompleteMapping (Challenge.mulZ2 (Challenge.sgnMat P)) (Challenge.fB L δ t) := by
  have hzero : ∀ l, Challenge.sgnMat P l l = some 0 := by
    intro l
    simp only [Challenge.sgnMat, hdiag, Option.map_some, CycleRemarks.sgn_one]
  change ReesCoreCompat.IsCompleteMapping (ReesCoreCompat.mul (Challenge.sgnMat P))
    (ReesCoreCompat.fB L δ t)
  exact ReesCoreCompat.lemmaB (Challenge.sgnMat P) L δ t hzero ht
    (fun i => (hL.1 i).1) (fun l => (hL.2 l).1)

/-- Pair a set of even cardinality by transporting the exchange of two equal summands;
the summand label gives the required parity function. -/
theorem exists_pairing (H : Type) [Finite H] (heven : Even (Nat.card H)) :
    ∃ (δ : Equiv.Perm H) (t : H → ZMod 2), ∀ μ, t (δ μ) = t μ + 1 := by
  classical
  let := Fintype.ofFinite H
  obtain ⟨k, hk⟩ := heven
  have hcard : Fintype.card H = Fintype.card (Fin k ⊕ Fin k) := by
    simpa only [Nat.card_eq_fintype_card, Fintype.card_sum, Fintype.card_fin] using hk
  let e : H ≃ (Fin k ⊕ Fin k) := Fintype.equivOfCardEq hcard
  let δ : Equiv.Perm H := (e.trans (Equiv.sumComm (Fin k) (Fin k))).trans e.symm
  let bit : (Fin k ⊕ Fin k) → ZMod 2 := Sum.elim (fun _ => 0) (fun _ => 1)
  let t : H → ZMod 2 := fun μ => bit (e μ)
  refine ⟨δ, t, ?_⟩
  intro μ
  change bit (e (e.symm (Sum.swap (e μ)))) = bit (e μ) + 1
  rw [e.apply_symm_apply]
  cases e μ <;> norm_num [bit]
  all_goals decide +kernel

/-- Every finite nonempty set has a Latin square, transported from addition modulo its size. -/
theorem exists_latin (H : Type) [Finite H] [Nonempty H] :
    ∃ L : H → H → H, Challenge.IsLatin L := by
  classical
  let := Fintype.ofFinite H
  let e : H ≃ ZMod (Fintype.card H) :=
    (Fintype.equivFin H).trans (ZMod.finEquiv (Fintype.card H)).toEquiv
  let L : H → H → H := fun i l => e.symm (e i + e l)
  refine ⟨L, ?_, ?_⟩
  · intro i
    apply Function.Injective.bijective_of_finite
    intro l m hlm
    apply e.injective
    have hsum := congrArg e hlm
    change e (e.symm (e i + e l)) = e (e.symm (e i + e m)) at hsum
    simp only [e.apply_symm_apply] at hsum
    exact add_left_cancel hsum
  · intro l
    apply Function.Injective.bijective_of_finite
    intro i j hij
    apply e.injective
    have hsum := congrArg e hij
    change e (e.symm (e i + e l)) = e (e.symm (e j + e l)) at hsum
    simp only [e.apply_symm_apply] at hsum
    exact add_right_cancel hsum

end ReesEven

/-- Complete frozen Lemma 4.3: the map B, existence of the pairing and labels, and the actual
lift to the symmetric-group Rees semigroup are all included. -/
theorem check_Lemma43 : Challenge.Lemma43 := by
  intro r hr H _ _ P hdiag
  constructor
  · intro L δ t hL ht
    exact ReesEven.fB_complete P hdiag L δ t hL ht
  · intro heven
    obtain ⟨δ, t, ht⟩ := ReesEven.exists_pairing H heven
    refine ⟨⟨δ, t, ht⟩, ?_⟩
    obtain ⟨L, hL⟩ := ReesEven.exists_latin H
    exact CodexPaper5.check_Lemma42 r hr H P hdiag
      ⟨Challenge.fB L δ t, ReesEven.fB_complete P hdiag L δ t hL ht⟩

#print axioms CodexPaper5.ReesEven.fB_complete
#print axioms CodexPaper5.ReesEven.exists_pairing
#print axioms CodexPaper5.ReesEven.exists_latin
#print axioms CodexPaper5.check_Lemma43

end CodexPaper5
