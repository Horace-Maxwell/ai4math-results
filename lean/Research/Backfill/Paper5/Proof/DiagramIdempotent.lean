import Research.Backfill.Paper5.Proof.DiagramCoordinates
import Research.Backfill.Paper5.Proof.DiagramProductCoordinates

set_option autoImplicit false

namespace CodexPaper5.DiagramIdempotent

open BackfillPaper5

/-- The frozen diagonal diagram is the actual glue along the identity on its free points. -/
theorem eDiag_eq_glue_refl {n : ℕ} (l : Challenge.Half n) :
    Challenge.eDiag l = DiagramCoordinates.glue l l (Equiv.refl l.1) := by
  funext p
  cases p with
  | inl a =>
    by_cases ha : a ∈ l.1
    · simp [Challenge.eDiag, DiagramCoordinates.glue, ha]
    · simp [Challenge.eDiag, DiagramCoordinates.glue, ha]
  | inr a =>
    by_cases ha : a ∈ l.1
    · simp [Challenge.eDiag, DiagramCoordinates.glue, ha]
    · simp [Challenge.eDiag, DiagramCoordinates.glue, ha]

theorem eDiag_mem_Jr {D : Challenge.Fam} {n r : ℕ} {l : Challenge.Half n}
    (hl : l ∈ Challenge.Hr D n r) : Challenge.eDiag l ∈ Challenge.Jr D n r := by
  rw [eDiag_eq_glue_refl]
  exact DiagramCoordinates.glue_mem_Jr hl hl (Equiv.refl l.1)

theorem topHalf_eDiag {D : Challenge.Fam} {n r : ℕ} {l : Challenge.Half n}
    (hl : l ∈ Challenge.Hr D n r) : Challenge.topHalf (Challenge.eDiag l) = l := by
  rw [eDiag_eq_glue_refl]
  exact DiagramCoordinates.topHalf_glue hl (Equiv.refl l.1)

theorem botHalf_eDiag {D : Challenge.Fam} {n r : ℕ} {l : Challenge.Half n}
    (hl : l ∈ Challenge.Hr D n r) : Challenge.botHalf (Challenge.eDiag l) = l := by
  rw [eDiag_eq_glue_refl]
  exact DiagramCoordinates.botHalf_glue hl (Equiv.refl l.1)

/-- Every actual through block of eDiag joins a free point to the same bottom point. -/
theorem repG_eDiag_one {D : Challenge.Fam} {n r : ℕ} {l : Challenge.Half n}
    (hl : l ∈ Challenge.Hr D n r) : Challenge.RepG r (Challenge.eDiag l) 1 := by
  intro k a b hab hk
  have ha : a ∈ l.1 := by
    by_contra ha
    have hbad : Sum.inl (l.2 a) = Sum.inr b := by
      simpa only [Challenge.eDiag, ite_eq_right ha] using hab
    exact Sum.inl_ne_inr hbad
  have hab' : a = b := by
    have hsame : (Sum.inr a : Challenge.Pt n) = Sum.inr b := by
      simpa only [Challenge.eDiag, ite_eq_left ha] using hab
    exact Sum.inr.inj hsame
  subst b
  rw [topHalf_eDiag hl] at hk
  rw [botHalf_eDiag hl]
  change k.val = Challenge.pos l.1 a
  exact hk.symm

theorem gCoord_eDiag {D : Challenge.Fam} {n r : ℕ} {l : Challenge.Half n}
    (hl : l ∈ Challenge.Hr D n r) : Challenge.gCoord r (Challenge.eDiag l) = 1 :=
  DiagramExtraction.gCoord_eq_of_repG (eDiag_mem_Jr hl) 1 (repG_eDiag_one hl)

/-- The complete frozen multiplication clause for any two diagrams with the same two halves. -/
theorem sameHalf_mul {D : Challenge.Fam} {n r : ℕ} {l : Challenge.Half n}
    (hl : l ∈ Challenge.Hr D n r) {x y : Challenge.Pt n → Challenge.Pt n}
    (hx : x ∈ Challenge.Jr D n r) (hy : y ∈ Challenge.Jr D n r)
    (htx : Challenge.topHalf x = l) (hbx : Challenge.botHalf x = l)
    (hty : Challenge.topHalf y = l) (hby : Challenge.botHalf y = l) :
    Challenge.dmul x y ∈ Challenge.Jr D n r ∧
      Challenge.topHalf (Challenge.dmul x y) = l ∧
      Challenge.botHalf (Challenge.dmul x y) = l ∧
      Challenge.gCoord r (Challenge.dmul x y) = Challenge.gCoord r x * Challenge.gCoord r y := by
  have hc : Challenge.Compat (Challenge.botHalf x) (Challenge.topHalf y) := by
    rw [hbx, hty]
    exact HalfDiagonal.compat_of_same_free rfl
  refine ⟨DiagramMultiplication.dmul_mem_Jr_of_compat hx hy hc,
    (DiagramMultiplication.topHalf_dmul_of_compat hx hy hc).trans htx,
    (DiagramMultiplication.botHalf_dmul_of_compat hx hy hc).trans hby, ?_⟩
  calc
    Challenge.gCoord r (Challenge.dmul x y) =
        Challenge.gCoord r x * Challenge.pSand r (Challenge.botHalf x) (Challenge.topHalf y) *
          Challenge.gCoord r y := DiagramProductCoordinates.gCoord_dmul_of_compat hx hy hc
    _ = Challenge.gCoord r x * Challenge.gCoord r y := by
      rw [hbx, hty, HalfDiagonal.pSand_eq_one_of_same_free hl hl rfl, mul_one]

/-- Actual diagram equality follows from reconstruction, without a RankOccurs assumption. -/
theorem eq_of_coordinates {D : Challenge.Fam} {n r : ℕ}
    {x y : Challenge.Pt n → Challenge.Pt n}
    (hx : x ∈ Challenge.Jr D n r) (hy : y ∈ Challenge.Jr D n r)
    (ht : Challenge.topHalf x = Challenge.topHalf y)
    (hb : Challenge.botHalf x = Challenge.botHalf y)
    (hg : Challenge.gCoord r x = Challenge.gCoord r y) : x = y :=
  (DiagramCoordinates.assemble_of_mem_Jr hx).trans
    ((DiagramCoordinates.assemble_congr
      (hL₁ := (DiagramExtraction.topHalf_mem_hr hx).1)
      (hL₂ := (DiagramExtraction.topHalf_mem_hr hy).1)
      (hI₁ := (DiagramExtraction.botHalf_mem_hr hx).1)
      (hI₂ := (DiagramExtraction.botHalf_mem_hr hy).1) ht hb hg).trans
        (DiagramCoordinates.assemble_of_mem_Jr hy).symm)

/-- Idempotence is equality of the frozen Pt-to-Pt functions under the actual stack product. -/
theorem eDiag_idempotent {D : Challenge.Fam} {n r : ℕ} {l : Challenge.Half n}
    (hl : l ∈ Challenge.Hr D n r) :
    Challenge.dmul (Challenge.eDiag l) (Challenge.eDiag l) = Challenge.eDiag l := by
  have he := eDiag_mem_Jr hl
  have ht := topHalf_eDiag hl
  have hb := botHalf_eDiag hl
  obtain ⟨hm, htm, hbm, hgm⟩ := sameHalf_mul hl he he ht hb ht hb
  apply eq_of_coordinates hm he
  · exact htm.trans ht.symm
  · exact hbm.trans hb.symm
  · simpa only [gCoord_eDiag hl, one_mul] using hgm

theorem check_IdempotentE : Challenge.IdempotentE := by
  intro D n r l hl
  refine ⟨eDiag_mem_Jr hl, topHalf_eDiag hl, botHalf_eDiag hl, gCoord_eDiag hl,
    eDiag_idempotent hl, ?_⟩
  intro x hx y hy htx hbx hty hby
  exact sameHalf_mul hl hx hy htx hbx hty hby

#print axioms CodexPaper5.DiagramIdempotent.eDiag_eq_glue_refl
#print axioms CodexPaper5.DiagramIdempotent.eDiag_mem_Jr
#print axioms CodexPaper5.DiagramIdempotent.topHalf_eDiag
#print axioms CodexPaper5.DiagramIdempotent.botHalf_eDiag
#print axioms CodexPaper5.DiagramIdempotent.repG_eDiag_one
#print axioms CodexPaper5.DiagramIdempotent.gCoord_eDiag
#print axioms CodexPaper5.DiagramIdempotent.sameHalf_mul
#print axioms CodexPaper5.DiagramIdempotent.eq_of_coordinates
#print axioms CodexPaper5.DiagramIdempotent.eDiag_idempotent
#print axioms CodexPaper5.DiagramIdempotent.check_IdempotentE

end CodexPaper5.DiagramIdempotent
