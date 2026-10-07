import Research.Backfill.Paper5.Proof.DiagramPrincipalFactor

set_option autoImplicit false

namespace CodexPaper5.PartialBrauerThree

open BackfillPaper5

section Proofs

open Classical

/-- The actual partial Brauer half with the unique nonfree point a. -/
def missingHalf (a : Fin 3) : Challenge.Half 3 :=
  (Finset.univ.erase a, id)

theorem missingHalf_isHalf (a : Fin 3) :
    Challenge.IsHalf Challenge.Fam.PB 3 2 (missingHalf a) := by
  refine ⟨?_, (fun b => rfl), (fun b _ => rfl), ?_⟩
  · change (Finset.univ.erase a).card = 2
    rw [Finset.card_erase_of_mem (Finset.mem_univ a), Finset.card_univ,
      Fintype.card_fin]
  · intro hB
    cases hB

def missingSub (a : Fin 3) : Challenge.HSub Challenge.Fam.PB 3 2 :=
  ⟨missingHalf a, missingHalf_isHalf a⟩

/-- Every genuine rank-2 half on three points has a singleton complement. -/
theorem complement_singleton (h : Challenge.HSub Challenge.Fam.PB 3 2) :
    ∃ a : Fin 3, h.val.1ᶜ = {a} := by
  apply Finset.card_eq_one.mp
  rw [Finset.card_compl, Fintype.card_fin, h.property.1]

/-- The whole matching function is the identity, including the nonfree point. -/
theorem half_matching_eq_id (h : Challenge.HSub Challenge.Fam.PB 3 2) :
    h.val.2 = id := by
  obtain ⟨a, ha⟩ := complement_singleton h
  funext b
  by_cases hb : b ∈ h.val.1
  · exact h.property.2.2.1 b hb
  · have hba : b = a := by
      have hc : b ∈ h.val.1ᶜ := Finset.mem_compl.mpr hb
      rw [ha] at hc
      exact Finset.mem_singleton.mp hc
    have hmba : h.val.2 b = a := by
      have hc : h.val.2 b ∈ h.val.1ᶜ :=
        Finset.mem_compl.mpr (DiagramCoordinates.half_maps_nonfree h.property hb)
      rw [ha] at hc
      exact Finset.mem_singleton.mp hc
    exact hmba.trans hba.symm

/-- Both the actual free set and the whole matching function recover a canonical half. -/
theorem half_eq_missingHalf (h : Challenge.HSub Challenge.Fam.PB 3 2) :
    ∃ a : Fin 3, h.val = missingHalf a := by
  obtain ⟨a, ha⟩ := complement_singleton h
  refine ⟨a, ?_⟩
  apply Prod.ext
  · change h.val.1 = Finset.univ.erase a
    rw [← Finset.compl_singleton, ← ha, compl_compl]
  · exact half_matching_eq_id h

theorem missingSub_injective : Function.Injective missingSub := by
  intro a b hab
  have hF : Finset.univ.erase a = Finset.univ.erase b :=
    congrArg (fun h : Challenge.HSub Challenge.Fam.PB 3 2 => h.val.1) hab
  by_contra hne
  have ha : a ∈ Finset.univ.erase b :=
    Finset.mem_erase.mpr ⟨hne, Finset.mem_univ a⟩
  rw [← hF] at ha
  exact (Finset.notMem_erase a Finset.univ) ha

theorem missingSub_surjective : Function.Surjective missingSub := by
  intro h
  obtain ⟨a, ha⟩ := half_eq_missingHalf h
  refine ⟨a, ?_⟩
  apply Subtype.ext
  exact ha.symm

theorem missingSub_bijective : Function.Bijective missingSub :=
  ⟨missingSub_injective, missingSub_surjective⟩

/-- Index a real half by its missing point, with inverse the real canonical half. -/
noncomputable def indexEquiv : Challenge.HSub Challenge.Fam.PB 3 2 ≃ Fin 3 :=
  (Equiv.ofBijective missingSub missingSub_bijective).symm

theorem indexEquiv_missingSub (a : Fin 3) : indexEquiv (missingSub a) = a := by
  change (Equiv.ofBijective missingSub missingSub_bijective).symm
    ((Equiv.ofBijective missingSub missingSub_bijective) a) = a
  exact (Equiv.ofBijective missingSub missingSub_bijective).symm_apply_apply a

theorem missingSub_indexEquiv (h : Challenge.HSub Challenge.Fam.PB 3 2) :
    missingSub (indexEquiv h) = h := by
  change (Equiv.ofBijective missingSub missingSub_bijective)
    ((Equiv.ofBijective missingSub missingSub_bijective).symm h) = h
  exact (Equiv.ofBijective missingSub missingSub_bijective).apply_symm_apply h

theorem indexEquiv_symm (a : Fin 3) : indexEquiv.symm a = missingSub a := rfl

theorem half_eq_of_free_eq (l i : Challenge.HSub Challenge.Fam.PB 3 2)
    (hF : l.val.1 = i.val.1) : l = i := by
  apply Subtype.ext
  apply Prod.ext
  · exact hF
  · exact (half_matching_eq_id l).trans (half_matching_eq_id i).symm

theorem indexEquiv_eq_iff_free_eq (l i : Challenge.HSub Challenge.Fam.PB 3 2) :
    indexEquiv l = indexEquiv i ↔ l.val.1 = i.val.1 := by
  constructor
  · intro h
    exact congrArg (fun h : Challenge.HSub Challenge.Fam.PB 3 2 => h.val.1)
      (indexEquiv.injective h)
  · intro hF
    exact congrArg indexEquiv (half_eq_of_free_eq l i hF)

theorem gammaEdge_false (l i : Challenge.HSub Challenge.Fam.PB 3 2) (a b : Fin 3) :
    ¬ Challenge.GammaEdge l.val i.val a b := by
  rw [Challenge.GammaEdge, half_matching_eq_id l, half_matching_eq_id i]
  rintro (⟨heq, hne⟩ | ⟨heq, hne⟩)
  · exact hne heq.symm
  · exact hne heq.symm

/-- The actual symmetrized graph has no edges, including in the reverse relation. -/
theorem gammaGraph_eq_bot (l i : Challenge.HSub Challenge.Fam.PB 3 2) :
    Challenge.gammaGraph l.val i.val = ⊥ := by
  apply SimpleGraph.ext
  funext a b
  apply propext
  change (a ≠ b ∧
    (Challenge.GammaEdge l.val i.val a b ∨ Challenge.GammaEdge l.val i.val b a)) ↔ False
  simp only [gammaEdge_false l i a b, gammaEdge_false l i b a, false_or, and_false]

theorem compat_iff_free_eq (l i : Challenge.HSub Challenge.Fam.PB 3 2) :
    Challenge.Compat l.val i.val ↔ l.val.1 = i.val.1 := by
  constructor
  · intro hc
    have hsub : l.val.1 ⊆ i.val.1 := by
      intro a ha
      obtain ⟨e, he, hp⟩ := hc a ha
      rw [gammaGraph_eq_bot l i] at hp
      have hae : a = e := SimpleGraph.reachable_bot.mp hp
      exact hae.symm ▸ he
    apply Finset.eq_of_subset_of_card_le hsub
    rw [i.property.1, l.property.1]
  · exact HalfDiagonal.compat_of_same_free

theorem compat_iff_index_eq (l i : Challenge.HSub Challenge.Fam.PB 3 2) :
    Challenge.Compat l.val i.val ↔ indexEquiv l = indexEquiv i :=
  (compat_iff_free_eq l i).trans (indexEquiv_eq_iff_free_eq l i).symm

/-- The actual choice-defined sandwich matrix is exactly the Brandt diagonal matrix. -/
theorem sandSub_eq_delta (l i : Challenge.HSub Challenge.Fam.PB 3 2) :
    Challenge.sandSub Challenge.Fam.PB 3 2 l i =
      Challenge.delta3 (indexEquiv l) (indexEquiv i) := by
  by_cases hF : l.val.1 = i.val.1
  · have hc := HalfDiagonal.compat_of_same_free hF
    have hp := HalfDiagonal.pSand_eq_one_of_same_free l.property i.property hF
    have he := (indexEquiv_eq_iff_free_eq l i).mpr hF
    rw [DiagramPrincipalFactor.sandSub_eq_some_of_compat l i hc, hp,
      Challenge.delta3, ite_eq_left he]
  · have hc : ¬ Challenge.Compat l.val i.val :=
      fun h => hF ((compat_iff_free_eq l i).mp h)
    have he : indexEquiv l ≠ indexEquiv i :=
      fun h => hF ((indexEquiv_eq_iff_free_eq l i).mp h)
    rw [DiagramPrincipalFactor.sandSub_eq_none_of_not_compat l i hc,
      Challenge.delta3, ite_eq_right he]

/-- A rank-2 PB3 diagram exists by gluing the real canonical half to itself. -/
theorem rankOccurs : Challenge.RankOccurs Challenge.Fam.PB 3 2 := by
  let h := missingHalf (0 : Fin 3)
  have hh : Challenge.IsHalf Challenge.Fam.PB 3 2 h := missingHalf_isHalf 0
  have hx := DiagramCoordinates.glue_mem_Jr hh hh (Equiv.refl h.1)
  exact ⟨DiagramCoordinates.glue h h (Equiv.refl h.1), hx.1, hx.2⟩

noncomputable def coordIndexEquiv :
    DiagramPrincipalFactor.Coord Challenge.Fam.PB 3 2 ≃
      Fin 3 × Challenge.Sym 2 × Fin 3 :=
  indexEquiv.prodCongr ((Equiv.refl (Challenge.Sym 2)).prodCongr indexEquiv)

noncomputable def reesIndexEquiv :
    Option (DiagramPrincipalFactor.Coord Challenge.Fam.PB 3 2) ≃
      Challenge.Rees0 (Challenge.Sym 2) (Fin 3) (Fin 3) :=
  Equiv.optionCongr coordIndexEquiv

/-- Relabel both real half coordinates and preserve all four Option product cases. -/
theorem reesIndexEquiv_mul
    (x y : Option (DiagramPrincipalFactor.Coord Challenge.Fam.PB 3 2)) :
    reesIndexEquiv (Challenge.rees0Mul (Challenge.sandSub Challenge.Fam.PB 3 2) x y) =
      Challenge.rees0Mul Challenge.delta3 (reesIndexEquiv x) (reesIndexEquiv y) := by
  cases x with
  | none =>
    cases y with
    | none => rfl
    | some y => rfl
  | some x =>
    cases y with
    | none => rfl
    | some y =>
      rcases x with ⟨i, g, l⟩
      rcases y with ⟨j, h, m⟩
      change ((Challenge.sandSub Challenge.Fam.PB 3 2 l j).map
        (fun p => (i, g * p * h, m))).map coordIndexEquiv =
        (Challenge.delta3 (indexEquiv l) (indexEquiv j)).map
          (fun p => (indexEquiv i, g * p * h, indexEquiv m))
      rw [sandSub_eq_delta l j]
      cases Challenge.delta3 (indexEquiv l) (indexEquiv j) with
      | none => rfl
      | some p => rfl

/-- The actual principal factor Equiv, composed with the actual missing-point coordinates. -/
noncomputable def principalBrandtEquiv :
    Option (Challenge.Jr Challenge.Fam.PB 3 2) ≃
      Challenge.Rees0 (Challenge.Sym 2) (Fin 3) (Fin 3) :=
  (DiagramPrincipalFactor.principalEquiv Challenge.Fam.PB 3 2 rankOccurs).trans reesIndexEquiv

theorem principalBrandtEquiv_mul (x y : Option (Challenge.Jr Challenge.Fam.PB 3 2)) :
    principalBrandtEquiv (Challenge.pfMul Challenge.dmul (Challenge.Jr Challenge.Fam.PB 3 2) x y) =
      Challenge.rees0Mul Challenge.delta3 (principalBrandtEquiv x) (principalBrandtEquiv y) := by
  change reesIndexEquiv
    (DiagramPrincipalFactor.principalEquiv Challenge.Fam.PB 3 2 rankOccurs
      (Challenge.pfMul Challenge.dmul (Challenge.Jr Challenge.Fam.PB 3 2) x y)) =
    Challenge.rees0Mul Challenge.delta3
      (reesIndexEquiv (DiagramPrincipalFactor.principalEquiv Challenge.Fam.PB 3 2 rankOccurs x))
      (reesIndexEquiv (DiagramPrincipalFactor.principalEquiv Challenge.Fam.PB 3 2 rankOccurs y))
  rw [DiagramPrincipalFactor.principalEquiv_mul]
  exact reesIndexEquiv_mul _ _

theorem magmaIso :
    Challenge.MagmaIso
      (Challenge.pfMul Challenge.dmul (Challenge.Jr Challenge.Fam.PB 3 2))
      (Challenge.rees0Mul Challenge.delta3) :=
  ⟨principalBrandtEquiv, principalBrandtEquiv_mul⟩

end Proofs

#print axioms CodexPaper5.PartialBrauerThree.missingHalf
#print axioms CodexPaper5.PartialBrauerThree.missingHalf_isHalf
#print axioms CodexPaper5.PartialBrauerThree.missingSub
#print axioms CodexPaper5.PartialBrauerThree.complement_singleton
#print axioms CodexPaper5.PartialBrauerThree.half_matching_eq_id
#print axioms CodexPaper5.PartialBrauerThree.half_eq_missingHalf
#print axioms CodexPaper5.PartialBrauerThree.missingSub_injective
#print axioms CodexPaper5.PartialBrauerThree.missingSub_surjective
#print axioms CodexPaper5.PartialBrauerThree.missingSub_bijective
#print axioms CodexPaper5.PartialBrauerThree.indexEquiv
#print axioms CodexPaper5.PartialBrauerThree.indexEquiv_missingSub
#print axioms CodexPaper5.PartialBrauerThree.missingSub_indexEquiv
#print axioms CodexPaper5.PartialBrauerThree.indexEquiv_symm
#print axioms CodexPaper5.PartialBrauerThree.half_eq_of_free_eq
#print axioms CodexPaper5.PartialBrauerThree.indexEquiv_eq_iff_free_eq
#print axioms CodexPaper5.PartialBrauerThree.gammaEdge_false
#print axioms CodexPaper5.PartialBrauerThree.gammaGraph_eq_bot
#print axioms CodexPaper5.PartialBrauerThree.compat_iff_free_eq
#print axioms CodexPaper5.PartialBrauerThree.compat_iff_index_eq
#print axioms CodexPaper5.PartialBrauerThree.sandSub_eq_delta
#print axioms CodexPaper5.PartialBrauerThree.rankOccurs
#print axioms CodexPaper5.PartialBrauerThree.coordIndexEquiv
#print axioms CodexPaper5.PartialBrauerThree.reesIndexEquiv
#print axioms CodexPaper5.PartialBrauerThree.reesIndexEquiv_mul
#print axioms CodexPaper5.PartialBrauerThree.principalBrandtEquiv
#print axioms CodexPaper5.PartialBrauerThree.principalBrandtEquiv_mul
#print axioms CodexPaper5.PartialBrauerThree.magmaIso

end CodexPaper5.PartialBrauerThree
