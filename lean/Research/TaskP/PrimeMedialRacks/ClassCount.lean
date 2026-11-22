import Research.TaskP.PrimeMedialRacks.Affine
import Research.TaskP.PrimeMedialRacks.IsoTransfer

namespace TaskP.PrimeMedialRacks

open Challenge

def HasRep {n : ℕ} (P : Operation (Fin n) → Prop) (q : IsoClass n) : Prop :=
  ∃ op, Quotient.mk (isoSetoid n) op = q ∧ P op

theorem classCount_eq {n : ℕ} (P : Operation (Fin n) → Prop) :
    classCount n P = Nat.card {q // HasRep P q} := by
  simp only [classCount, HasRep, ← Nat.card_eq_fintype_card]

/-- Split isomorphism classes of A by membership in an isomorphism-invariant subclass B. -/
theorem classCount_partition {n : ℕ} (A B : Operation (Fin n) → Prop)
    (hBA : ∀ t, B t → A t) (hB : ∀ s t, Isomorphic s t → B s → B t) :
    classCount n A = classCount n B + classCount n (fun t => A t ∧ ¬ B t) := by
  classical
  let C := fun t => A t ∧ ¬ B t
  have split (q : IsoClass n) : HasRep A q ↔ HasRep B q ∨ HasRep C q := by
    constructor
    · rintro ⟨t, ht, ha⟩
      by_cases hb : B t
      · exact Or.inl ⟨t, ht, hb⟩
      · exact Or.inr ⟨t, ht, ha, hb⟩
    · rintro (⟨t, ht, hb⟩ | ⟨t, ht, hc⟩)
      · exact ⟨t, ht, hBA t hb⟩
      · exact ⟨t, ht, hc.1⟩
  have disj : Disjoint (HasRep B) (HasRep C) := by
    intro _ hb hc q hq
    obtain ⟨s, hs, hbs⟩ := hb q hq
    obtain ⟨t, ht, hat, hbt⟩ := hc q hq
    exact hbt (hB s t (Quotient.exact (hs.trans ht.symm)) hbs)
  rw [classCount_eq, classCount_eq, classCount_eq,
    Nat.card_congr (Equiv.subtypeEquivRight split),
    Nat.card_congr (subtypeOrEquiv (HasRep B) (HasRep C) disj), Nat.card_sum]

abbrev Parameter (p : ℕ) := {k : ZMod p // k ≠ 0 ∧ k ≠ 1}

variable {p : ℕ} [Fact p.Prime]

theorem parameter_card : Nat.card (Parameter p) = p - 2 := by
  classical
  let e : Parameter p ≃ {k : ZMod p // ¬ (k = 0 ∨ k = 1)} :=
    Equiv.subtypeEquivRight (fun _ => not_or.symm)
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_subtype_compl,
    Fintype.card_subtype_eq_or_eq_of_ne zero_ne_one, ZMod.card]

noncomputable def labels (p : ℕ) [Fact p.Prime] : Fin p ≃ ZMod p :=
  Fintype.equivOfCardEq (by simp [ZMod.card])

noncomputable def affineTable (k : ZMod p) : Operation (Fin p) :=
  fun x y => (labels p).symm (affine k (labels p x) (labels p y))

theorem affineTable_iso (k : ZMod p) : Isomorphic (affineTable k) (affine k) :=
  ⟨labels p, fun _ _ => Equiv.apply_symm_apply _ _⟩

/-- If the actual multiplication tables in a class are exhausted by the affine family,
the quotient counts its pairwise distinct parameters exactly. -/
theorem count_affine_models (P : Operation (Fin p) → Prop)
    (realizes : ∀ k : Parameter p, P (affineTable k.1))
    (covers : ∀ op, P op → ∃ k : Parameter p, Isomorphic op (affine k.1)) :
    classCount p P = p - 2 := by
  let f : Parameter p → {q // HasRep P q} := fun k =>
    ⟨Quotient.mk _ (affineTable k.1), affineTable k.1, rfl, realizes k⟩
  have hinj : Function.Injective f := by
    intro k l h
    have e : Isomorphic (affineTable k.1) (affineTable l.1) := Quotient.exact (congrArg Subtype.val h)
    apply Subtype.ext
    exact affine_parameter_unique k.2.1 k.2.2
      (iso_trans (iso_symm (affineTable_iso _)) (iso_trans e (affineTable_iso _)))
  have hsurj : Function.Surjective f := by
    rintro ⟨q, t, ht, hP⟩
    obtain ⟨k, hk⟩ := covers t hP
    refine ⟨k, Subtype.ext ?_⟩
    exact (Quotient.sound (iso_trans (affineTable_iso _) (iso_symm hk))).trans ht
  rw [classCount_eq, ← Nat.card_congr (Equiv.ofBijective f ⟨hinj, hsurj⟩), parameter_card]

end TaskP.PrimeMedialRacks
