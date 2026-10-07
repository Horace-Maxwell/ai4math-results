import Research.Backfill.Paper5.Proof.DiagramIdempotent

set_option autoImplicit false

namespace CodexPaper5.DiagramUnitGroup

open BackfillPaper5

/-- The full-rank half has every point free and no nontrivial half-diagram arc. -/
def fullHalf (n : ℕ) : Challenge.Half n := (Finset.univ, id)

theorem fullHalf_mem_hr (D : Challenge.Fam) (n : ℕ) :
    fullHalf n ∈ Challenge.Hr D n n := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [fullHalf]
  · intro a
    rfl
  · intro a _ha
    rfl
  · intro _hD a ha
    exact (ha (Finset.mem_univ a)).elim

/-- Full rank determines both the free set and the entire half-diagram function. -/
theorem eq_fullHalf_of_mem_hr {D : Challenge.Fam} {n : ℕ} {l : Challenge.Half n}
    (hl : l ∈ Challenge.Hr D n n) : l = fullHalf n := by
  have hf : l.1 = Finset.univ :=
    Finset.eq_univ_of_card l.1 (by simpa only [Fintype.card_fin] using hl.1)
  apply Prod.ext
  · exact hf
  · funext a
    exact hl.2.2.1 a (by simp only [hf, Finset.mem_univ])

theorem topHalf_eq_full_of_mem_Jr {D : Challenge.Fam} {n : ℕ}
    {x : Challenge.Pt n → Challenge.Pt n} (hx : x ∈ Challenge.Jr D n n) :
    Challenge.topHalf x = fullHalf n :=
  eq_fullHalf_of_mem_hr (DiagramExtraction.topHalf_mem_hr hx)

theorem botHalf_eq_full_of_mem_Jr {D : Challenge.Fam} {n : ℕ}
    {x : Challenge.Pt n → Challenge.Pt n} (hx : x ∈ Challenge.Jr D n n) :
    Challenge.botHalf x = fullHalf n :=
  eq_fullHalf_of_mem_hr (DiagramExtraction.botHalf_mem_hr hx)

theorem eDiag_fullHalf (n : ℕ) : Challenge.eDiag (fullHalf n) = Challenge.idD n := by
  funext p
  cases p <;> simp [Challenge.eDiag, fullHalf, Challenge.idD]

theorem idD_mem_Jr (D : Challenge.Fam) (n : ℕ) :
    Challenge.idD n ∈ Challenge.Jr D n n := by
  simpa only [eDiag_fullHalf] using
    DiagramIdempotent.eDiag_mem_Jr (fullHalf_mem_hr D n)

theorem gCoord_idD (n : ℕ) : Challenge.gCoord n (Challenge.idD n) = 1 := by
  simpa only [eDiag_fullHalf] using
    DiagramIdempotent.gCoord_eDiag (fullHalf_mem_hr Challenge.Fam.PB n)

theorem rank_idD (n : ℕ) : Challenge.rank (Challenge.idD n) = n :=
  (idD_mem_Jr Challenge.Fam.PB n).2

/-- The rank bound only counts a subset of Fin n and does not require graph legality. -/
theorem rank_le_n {n : ℕ} (x : Challenge.Pt n → Challenge.Pt n) : Challenge.rank x ≤ n := by
  change (Challenge.topHalf x).1.card ≤ n
  simpa only [Fintype.card_fin] using (Challenge.topHalf x).1.card_le_univ

/-- The actual diagram with two full halves and prescribed frozen permutation coordinate. -/
noncomputable def unitDiagram (D : Challenge.Fam) (n : ℕ) (g : Challenge.Sym n) :
    Challenge.Jr D n n :=
  let hl := fullHalf_mem_hr D n
  ⟨DiagramCoordinates.assemble (fullHalf n) (fullHalf n) hl.1 hl.1 g,
    DiagramCoordinates.glue_mem_Jr hl hl
      (DiagramCoordinates.orderedLink (fullHalf n) (fullHalf n) hl.1 hl.1 g)⟩

theorem topHalf_unitDiagram (D : Challenge.Fam) (n : ℕ) (g : Challenge.Sym n) :
    Challenge.topHalf (unitDiagram D n g).val = fullHalf n :=
  DiagramCoordinates.topHalf_glue (fullHalf_mem_hr D n)
    (DiagramCoordinates.orderedLink (fullHalf n) (fullHalf n)
      (fullHalf_mem_hr D n).1 (fullHalf_mem_hr D n).1 g)

theorem botHalf_unitDiagram (D : Challenge.Fam) (n : ℕ) (g : Challenge.Sym n) :
    Challenge.botHalf (unitDiagram D n g).val = fullHalf n :=
  DiagramCoordinates.botHalf_glue (fullHalf_mem_hr D n)
    (DiagramCoordinates.orderedLink (fullHalf n) (fullHalf n)
      (fullHalf_mem_hr D n).1 (fullHalf_mem_hr D n).1 g)

theorem gCoord_unitDiagram (D : Challenge.Fam) (n : ℕ) (g : Challenge.Sym n) :
    Challenge.gCoord n (unitDiagram D n g).val = g :=
  DiagramCoordinates.assemble_gCoord (fullHalf_mem_hr D n) (fullHalf_mem_hr D n) g

/-- Reassembly from the actual coordinate recovers every full-rank diagram as a subtype. -/
theorem unitDiagram_gCoord (D : Challenge.Fam) (n : ℕ) (x : Challenge.Jr D n n) :
    unitDiagram D n (Challenge.gCoord n x.val) = x := by
  apply Subtype.ext
  apply DiagramIdempotent.eq_of_coordinates (unitDiagram D n (Challenge.gCoord n x.val)).property
    x.property
  · exact (topHalf_unitDiagram D n _).trans (topHalf_eq_full_of_mem_Jr x.property).symm
  · exact (botHalf_unitDiagram D n _).trans (botHalf_eq_full_of_mem_Jr x.property).symm
  · exact gCoord_unitDiagram D n _

/-- Forward is actual assembly, inverse is the frozen choice-defined coordinate. -/
noncomputable def unitEquiv (D : Challenge.Fam) (n : ℕ) :
    Challenge.Sym n ≃ Challenge.Jr D n n where
  toFun := unitDiagram D n
  invFun := fun x => Challenge.gCoord n x.val
  left_inv := gCoord_unitDiagram D n
  right_inv := unitDiagram_gCoord D n

/-- The coordinate group product is sent to the actual stack product, in the frozen order. -/
theorem unitDiagram_mul (D : Challenge.Fam) (n : ℕ) (g h : Challenge.Sym n) :
    (unitDiagram D n (g * h)).val =
      Challenge.dmul (unitDiagram D n g).val (unitDiagram D n h).val := by
  obtain ⟨hm, ht, hb, hg⟩ := DiagramIdempotent.sameHalf_mul (fullHalf_mem_hr D n)
    (unitDiagram D n g).property (unitDiagram D n h).property
    (topHalf_unitDiagram D n g) (botHalf_unitDiagram D n g)
    (topHalf_unitDiagram D n h) (botHalf_unitDiagram D n h)
  apply DiagramIdempotent.eq_of_coordinates (unitDiagram D n (g * h)).property hm
  · exact (topHalf_unitDiagram D n (g * h)).trans ht.symm
  · exact (botHalf_unitDiagram D n (g * h)).trans hb.symm
  · have hg' : Challenge.gCoord n
        (Challenge.dmul (unitDiagram D n g).val (unitDiagram D n h).val) = g * h := by
      simpa only [gCoord_unitDiagram] using hg
    exact (gCoord_unitDiagram D n (g * h)).trans hg'.symm

theorem unitDiagram_one (D : Challenge.Fam) (n : ℕ) :
    (unitDiagram D n 1).val = Challenge.idD n := by
  apply DiagramIdempotent.eq_of_coordinates (unitDiagram D n 1).property (idD_mem_Jr D n)
  · exact (topHalf_unitDiagram D n 1).trans
      (topHalf_eq_full_of_mem_Jr (idD_mem_Jr D n)).symm
  · exact (botHalf_unitDiagram D n 1).trans
      (botHalf_eq_full_of_mem_Jr (idD_mem_Jr D n)).symm
  · exact (gCoord_unitDiagram D n 1).trans (gCoord_idD n).symm

/-- Any genuine two-sided inverse forces the rank to be full; one product already gives the bound. -/
theorem rank_eq_of_two_sided_inverse {D : Challenge.Fam} {n : ℕ}
    {x : Challenge.Pt n → Challenge.Pt n} (hx : x ∈ Challenge.Dset D n)
    (hinv : ∃ y ∈ Challenge.Dset D n,
      Challenge.dmul x y = Challenge.idD n ∧ Challenge.dmul y x = Challenge.idD n) :
    Challenge.rank x = n := by
  obtain ⟨y, hy, hxy, _hyx⟩ := hinv
  have hxpb : Challenge.IsPB x :=
    DiagramExtraction.isPB_of_mem_Jr (D := D) (r := Challenge.rank x) ⟨hx, rfl⟩
  have hypb : Challenge.IsPB y :=
    DiagramExtraction.isPB_of_mem_Jr (D := D) (r := Challenge.rank y) ⟨hy, rfl⟩
  have hn : n ≤ Challenge.rank x := by
    simpa only [hxy, rank_idD] using DiagramRank.rank_dmul_le_left hxpb hypb
  exact Nat.le_antisymm (rank_le_n x) hn

/-- The inverse permutation supplies a real legal graph inverse on both sides, also for n=0. -/
theorem two_sided_inverse_of_rank_eq {D : Challenge.Fam} {n : ℕ}
    {x : Challenge.Pt n → Challenge.Pt n} (hx : x ∈ Challenge.Dset D n)
    (hr : Challenge.rank x = n) :
    ∃ y ∈ Challenge.Dset D n,
      Challenge.dmul x y = Challenge.idD n ∧ Challenge.dmul y x = Challenge.idD n := by
  have hxr : x ∈ Challenge.Jr D n n := ⟨hx, hr⟩
  let g : Challenge.Sym n := Challenge.gCoord n x
  let y := (unitDiagram D n g⁻¹).val
  have he : unitDiagram D n g = ⟨x, hxr⟩ := unitDiagram_gCoord D n ⟨x, hxr⟩
  have hex : (unitDiagram D n g).val = x := congrArg Subtype.val he
  refine ⟨y, (unitDiagram D n g⁻¹).property.1, ?_, ?_⟩
  · calc
      Challenge.dmul x y =
          Challenge.dmul (unitDiagram D n g).val (unitDiagram D n g⁻¹).val :=
        congrArg (fun z => Challenge.dmul z y) hex.symm
      _ = (unitDiagram D n (g * g⁻¹)).val := (unitDiagram_mul D n g g⁻¹).symm
      _ = (unitDiagram D n 1).val :=
        congrArg (fun k : Challenge.Sym n => (unitDiagram D n k).val) (mul_inv_cancel g)
      _ = Challenge.idD n := unitDiagram_one D n
  · calc
      Challenge.dmul y x =
          Challenge.dmul (unitDiagram D n g⁻¹).val (unitDiagram D n g).val :=
        congrArg (fun z => Challenge.dmul y z) hex.symm
      _ = (unitDiagram D n (g⁻¹ * g)).val := (unitDiagram_mul D n g⁻¹ g).symm
      _ = (unitDiagram D n 1).val :=
        congrArg (fun k : Challenge.Sym n => (unitDiagram D n k).val) (inv_mul_cancel g)
      _ = Challenge.idD n := unitDiagram_one D n

theorem check_UnitsAreSym : Challenge.UnitsAreSym := by
  intro D n
  refine ⟨?_, unitEquiv D n, ?_⟩
  · intro x hx
    exact ⟨rank_eq_of_two_sided_inverse hx, two_sided_inverse_of_rank_eq hx⟩
  · intro g h
    exact unitDiagram_mul D n g h

#print axioms CodexPaper5.DiagramUnitGroup.fullHalf
#print axioms CodexPaper5.DiagramUnitGroup.fullHalf_mem_hr
#print axioms CodexPaper5.DiagramUnitGroup.eq_fullHalf_of_mem_hr
#print axioms CodexPaper5.DiagramUnitGroup.topHalf_eq_full_of_mem_Jr
#print axioms CodexPaper5.DiagramUnitGroup.botHalf_eq_full_of_mem_Jr
#print axioms CodexPaper5.DiagramUnitGroup.eDiag_fullHalf
#print axioms CodexPaper5.DiagramUnitGroup.idD_mem_Jr
#print axioms CodexPaper5.DiagramUnitGroup.gCoord_idD
#print axioms CodexPaper5.DiagramUnitGroup.rank_idD
#print axioms CodexPaper5.DiagramUnitGroup.rank_le_n
#print axioms CodexPaper5.DiagramUnitGroup.unitDiagram
#print axioms CodexPaper5.DiagramUnitGroup.topHalf_unitDiagram
#print axioms CodexPaper5.DiagramUnitGroup.botHalf_unitDiagram
#print axioms CodexPaper5.DiagramUnitGroup.gCoord_unitDiagram
#print axioms CodexPaper5.DiagramUnitGroup.unitDiagram_gCoord
#print axioms CodexPaper5.DiagramUnitGroup.unitEquiv
#print axioms CodexPaper5.DiagramUnitGroup.unitDiagram_mul
#print axioms CodexPaper5.DiagramUnitGroup.unitDiagram_one
#print axioms CodexPaper5.DiagramUnitGroup.rank_eq_of_two_sided_inverse
#print axioms CodexPaper5.DiagramUnitGroup.two_sided_inverse_of_rank_eq
#print axioms CodexPaper5.DiagramUnitGroup.check_UnitsAreSym

end CodexPaper5.DiagramUnitGroup
