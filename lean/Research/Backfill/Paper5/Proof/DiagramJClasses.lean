import Research.Backfill.Paper5.Proof.DiagramIdempotent

set_option autoImplicit false

namespace CodexPaper5.DiagramJClasses

open BackfillPaper5

theorem isPB_of_mem_Dset {D : Challenge.Fam} {n : ℕ}
    {x : Challenge.Pt n → Challenge.Pt n} (hx : x ∈ Challenge.Dset D n) :
    Challenge.IsPB x :=
  DiagramExtraction.isPB_of_mem_Jr (D := D) (r := Challenge.rank x) ⟨hx, rfl⟩

/-- Each side of the actual left-associated sandwich can only reduce the middle rank. -/
theorem rank_sandwich_le {n : ℕ} {a y b : Challenge.Pt n → Challenge.Pt n}
    (ha : Challenge.IsPB a) (hy : Challenge.IsPB y) (hb : Challenge.IsPB b) :
    Challenge.rank (Challenge.dmul (Challenge.dmul a y) b) ≤ Challenge.rank y :=
  (DiagramRank.rank_dmul_le_left (DiagramProduct.dmul_isPB ha hy) hb).trans
    (DiagramRank.rank_dmul_le_right ha hy)

/-- Frozen mutual left-associated factorization implies equality of ranks. -/
theorem rank_eq_of_JRel {D : Challenge.Fam} {n : ℕ}
    {x y : Challenge.Pt n → Challenge.Pt n}
    (hx : x ∈ Challenge.Dset D n) (hy : y ∈ Challenge.Dset D n)
    (hrel : Challenge.JRel Challenge.dmul (Challenge.Dset D n) x y) :
    Challenge.rank x = Challenge.rank y := by
  obtain ⟨a, ha, b, hb, c, hc, d, hd, hxy, hyx⟩ := hrel
  apply Nat.le_antisymm
  · calc
      Challenge.rank x = Challenge.rank (Challenge.dmul (Challenge.dmul a y) b) :=
        congrArg Challenge.rank hxy
      _ ≤ Challenge.rank y :=
        rank_sandwich_le (isPB_of_mem_Dset ha) (isPB_of_mem_Dset hy) (isPB_of_mem_Dset hb)
  · calc
      Challenge.rank y = Challenge.rank (Challenge.dmul (Challenge.dmul c x) d) :=
        congrArg Challenge.rank hyx
      _ ≤ Challenge.rank x :=
        rank_sandwich_le (isPB_of_mem_Dset hc) (isPB_of_mem_Dset hx) (isPB_of_mem_Dset hd)

/-- Actual assembly supplies a legal diagram and all three prescribed coordinates. -/
theorem assemble_spec {D : Challenge.Fam} {n r : ℕ} {l i : Challenge.Half n}
    (hl : l ∈ Challenge.Hr D n r) (hi : i ∈ Challenge.Hr D n r) (g : Challenge.Sym r) :
    DiagramCoordinates.assemble l i hl.1 hi.1 g ∈ Challenge.Jr D n r ∧
      Challenge.topHalf (DiagramCoordinates.assemble l i hl.1 hi.1 g) = l ∧
      Challenge.botHalf (DiagramCoordinates.assemble l i hl.1 hi.1 g) = i ∧
      Challenge.gCoord r (DiagramCoordinates.assemble l i hl.1 hi.1 g) = g :=
  ⟨DiagramCoordinates.glue_mem_Jr hl hi (DiagramCoordinates.orderedLink l i hl.1 hi.1 g),
    DiagramCoordinates.topHalf_glue hl (DiagramCoordinates.orderedLink l i hl.1 hi.1 g),
    DiagramCoordinates.botHalf_glue hi (DiagramCoordinates.orderedLink l i hl.1 hi.1 g),
    DiagramCoordinates.assemble_gCoord hl hi g⟩

/-- Only the two middle halves must match; the exterior halves are unrestricted. -/
theorem mul_of_matching_halves {D : Challenge.Fam} {n r : ℕ}
    {x y : Challenge.Pt n → Challenge.Pt n}
    (hx : x ∈ Challenge.Jr D n r) (hy : y ∈ Challenge.Jr D n r)
    (hmid : Challenge.botHalf x = Challenge.topHalf y) :
    Challenge.dmul x y ∈ Challenge.Jr D n r ∧
      Challenge.topHalf (Challenge.dmul x y) = Challenge.topHalf x ∧
      Challenge.botHalf (Challenge.dmul x y) = Challenge.botHalf y ∧
      Challenge.gCoord r (Challenge.dmul x y) = Challenge.gCoord r x * Challenge.gCoord r y := by
  have hfree := congrArg Prod.fst hmid
  have hc := HalfDiagonal.compat_of_same_free hfree
  refine ⟨DiagramMultiplication.dmul_mem_Jr_of_compat hx hy hc,
    DiagramMultiplication.topHalf_dmul_of_compat hx hy hc,
    DiagramMultiplication.botHalf_dmul_of_compat hx hy hc, ?_⟩
  rw [DiagramProductCoordinates.gCoord_dmul_of_compat hx hy hc,
    HalfDiagonal.pSand_eq_one_of_same_free
      (DiagramExtraction.botHalf_mem_hr hx) (DiagramExtraction.topHalf_mem_hr hy) hfree,
    mul_one]

/-- Equal-rank diagrams have real legal sandwich factors with the frozen left parentheses. -/
theorem exists_sandwich_factors {D : Challenge.Fam} {n r : ℕ}
    {x y : Challenge.Pt n → Challenge.Pt n}
    (hx : x ∈ Challenge.Jr D n r) (hy : y ∈ Challenge.Jr D n r) :
    ∃ a ∈ Challenge.Jr D n r, ∃ b ∈ Challenge.Jr D n r,
      x = Challenge.dmul (Challenge.dmul a y) b := by
  have htx := DiagramExtraction.topHalf_mem_hr hx
  have hbx := DiagramExtraction.botHalf_mem_hr hx
  have hty := DiagramExtraction.topHalf_mem_hr hy
  have hby := DiagramExtraction.botHalf_mem_hr hy
  let a := DiagramCoordinates.assemble (Challenge.topHalf x) (Challenge.topHalf y)
    htx.1 hty.1 (Challenge.gCoord r x * (Challenge.gCoord r y)⁻¹)
  let b := DiagramCoordinates.assemble (Challenge.botHalf y) (Challenge.botHalf x)
    hby.1 hbx.1 (1 : Challenge.Sym r)
  have has : a ∈ Challenge.Jr D n r ∧ Challenge.topHalf a = Challenge.topHalf x ∧
      Challenge.botHalf a = Challenge.topHalf y ∧
      Challenge.gCoord r a = Challenge.gCoord r x * (Challenge.gCoord r y)⁻¹ :=
    assemble_spec htx hty _
  have hbs : b ∈ Challenge.Jr D n r ∧ Challenge.topHalf b = Challenge.botHalf y ∧
      Challenge.botHalf b = Challenge.botHalf x ∧ Challenge.gCoord r b = 1 :=
    assemble_spec hby hbx _
  obtain ⟨ha, hta, hba, hga⟩ := has
  obtain ⟨hb, htb, hbb, hgb⟩ := hbs
  obtain ⟨hay, htay, hbay, hgay⟩ := mul_of_matching_halves ha hy hba
  have hgay' : Challenge.gCoord r (Challenge.dmul a y) = Challenge.gCoord r x := by
    rw [hgay, hga, mul_assoc, inv_mul_cancel, mul_one]
  obtain ⟨hab, htab, hbab, hgab⟩ :=
    mul_of_matching_halves hay hb (hbay.trans htb.symm)
  refine ⟨a, ha, b, hb, ?_⟩
  symm
  apply DiagramIdempotent.eq_of_coordinates hab hx
  · exact htab.trans (htay.trans hta)
  · exact hbab.trans hbb
  · simpa only [hgay', hgb, mul_one] using hgab

/-- Both actual factorization directions use the same rank, without a new occurrence premise. -/
theorem JRel_of_rank_eq {D : Challenge.Fam} {n : ℕ}
    {x y : Challenge.Pt n → Challenge.Pt n}
    (hx : x ∈ Challenge.Dset D n) (hy : y ∈ Challenge.Dset D n)
    (hr : Challenge.rank x = Challenge.rank y) :
    Challenge.JRel Challenge.dmul (Challenge.Dset D n) x y := by
  have hx' : x ∈ Challenge.Jr D n (Challenge.rank x) := ⟨hx, rfl⟩
  have hy' : y ∈ Challenge.Jr D n (Challenge.rank x) := ⟨hy, hr.symm⟩
  obtain ⟨a, ha, b, hb, hxy⟩ := exists_sandwich_factors hx' hy'
  obtain ⟨c, hc, d, hd, hyx⟩ := exists_sandwich_factors hy' hx'
  exact ⟨a, ha.1, b, hb.1, c, hc.1, d, hd.1, hxy, hyx⟩

theorem check_JClassesAreRankClasses : Challenge.JClassesAreRankClasses := by
  intro D n x hx y hy
  exact ⟨rank_eq_of_JRel hx hy, JRel_of_rank_eq hx hy⟩

#print axioms CodexPaper5.DiagramJClasses.isPB_of_mem_Dset
#print axioms CodexPaper5.DiagramJClasses.rank_sandwich_le
#print axioms CodexPaper5.DiagramJClasses.rank_eq_of_JRel
#print axioms CodexPaper5.DiagramJClasses.assemble_spec
#print axioms CodexPaper5.DiagramJClasses.mul_of_matching_halves
#print axioms CodexPaper5.DiagramJClasses.exists_sandwich_factors
#print axioms CodexPaper5.DiagramJClasses.JRel_of_rank_eq
#print axioms CodexPaper5.DiagramJClasses.check_JClassesAreRankClasses

end CodexPaper5.DiagramJClasses
