import Research.Backfill.Paper5.Supplement.FullPaperStatement
import Research.Backfill.Paper5.Proof.DiagramIdempotent

set_option autoImplicit false

namespace CodexPaper5.FullPaperCorner

open BackfillPaper5
open CodexPaper5.FullPaperStatement

/-- Assemble an actual diagram with both halves equal to the specified half. -/
noncomputable def assembleCorner {D : Challenge.Fam} {n r : ℕ}
    {l : Challenge.Half n} (hl : l ∈ Challenge.Hr D n r)
    (g : Challenge.Sym r) : Corner D n r l :=
  ⟨DiagramCoordinates.assemble l l hl.1 hl.1 g,
    DiagramCoordinates.glue_mem_Jr hl hl (DiagramCoordinates.orderedLink l l hl.1 hl.1 g),
    DiagramCoordinates.topHalf_glue hl _, DiagramCoordinates.botHalf_glue hl _⟩

theorem assembleCorner_gCoord {D : Challenge.Fam} {n r : ℕ}
    {l : Challenge.Half n} (hl : l ∈ Challenge.Hr D n r) (g : Challenge.Sym r) :
    Challenge.gCoord r (assembleCorner hl g).val = g :=
  DiagramCoordinates.assemble_gCoord hl hl g

/-- The two inverse maps use the frozen coordinate and its actual diagram reconstruction. -/
noncomputable def coordinateEquiv {D : Challenge.Fam} {n r : ℕ}
    {l : Challenge.Half n} (hl : l ∈ Challenge.Hr D n r) :
    Corner D n r l ≃ Challenge.Sym r where
  toFun x := Challenge.gCoord r x.val
  invFun g := assembleCorner hl g
  left_inv x := by
    apply Subtype.ext
    apply DiagramIdempotent.eq_of_coordinates
      (assembleCorner hl (Challenge.gCoord r x.val)).property.1 x.property.1
    · exact (assembleCorner hl (Challenge.gCoord r x.val)).property.2.1.trans
        x.property.2.1.symm
    · exact (assembleCorner hl (Challenge.gCoord r x.val)).property.2.2.trans
        x.property.2.2.symm
    · exact assembleCorner_gCoord hl (Challenge.gCoord r x.val)
  right_inv g := assembleCorner_gCoord hl g

theorem coordinateEquiv_apply {D : Challenge.Fam} {n r : ℕ}
    {l : Challenge.Half n} (hl : l ∈ Challenge.Hr D n r)
    (x : Corner D n r l) : coordinateEquiv hl x = Challenge.gCoord r x.val := rfl

/-- The actual stack product stays in this corner. -/
noncomputable def actualMul {D : Challenge.Fam} {n r : ℕ}
    {l : Challenge.Half n} (hl : l ∈ Challenge.Hr D n r)
    (x y : Corner D n r l) : Corner D n r l :=
  ⟨Challenge.dmul x.val y.val,
    (DiagramIdempotent.sameHalf_mul hl x.property.1 y.property.1
      x.property.2.1 x.property.2.2 y.property.2.1 y.property.2.2).1,
    (DiagramIdempotent.sameHalf_mul hl x.property.1 y.property.1
      x.property.2.1 x.property.2.2 y.property.2.1 y.property.2.2).2.1,
    (DiagramIdempotent.sameHalf_mul hl x.property.1 y.property.1
      x.property.2.1 x.property.2.2 y.property.2.1 y.property.2.2).2.2.1⟩

theorem coordinateEquiv_actualMul {D : Challenge.Fam} {n r : ℕ}
    {l : Challenge.Half n} (hl : l ∈ Challenge.Hr D n r)
    (x y : Corner D n r l) :
    coordinateEquiv hl (actualMul hl x y) = coordinateEquiv hl x * coordinateEquiv hl y :=
  (DiagramIdempotent.sameHalf_mul hl x.property.1 y.property.1
    x.property.2.1 x.property.2.2 y.property.2.1 y.property.2.2).2.2.2

def diagonalCorner {D : Challenge.Fam} {n r : ℕ}
    {l : Challenge.Half n} (hl : l ∈ Challenge.Hr D n r) : Corner D n r l :=
  ⟨Challenge.eDiag l, DiagramIdempotent.eDiag_mem_Jr hl,
    DiagramIdempotent.topHalf_eDiag hl, DiagramIdempotent.botHalf_eDiag hl⟩

theorem coordinateEquiv_diagonalCorner {D : Challenge.Fam} {n r : ℕ}
    {l : Challenge.Half n} (hl : l ∈ Challenge.Hr D n r) :
    coordinateEquiv hl (diagonalCorner hl) = 1 := DiagramIdempotent.gCoord_eDiag hl

/-- Pull back the genuine symmetric group, without a global instance on diagrams. -/
@[instance_reducible]
noncomputable def cornerGroup {D : Challenge.Fam} {n r : ℕ}
    {l : Challenge.Half n} (hl : l ∈ Challenge.Hr D n r) : Group (Corner D n r l) :=
  (coordinateEquiv hl).group

noncomputable def cornerMulEquiv {D : Challenge.Fam} {n r : ℕ}
    {l : Challenge.Half n} (hl : l ∈ Challenge.Hr D n r) :
    let _ : Group (Corner D n r l) := cornerGroup hl
    Corner D n r l ≃* Challenge.Sym r := by
  let _ : Group (Corner D n r l) := cornerGroup hl
  exact (coordinateEquiv hl).mulEquiv

/-- Injectivity identifies the pulled back multiplication with the actual stack product. -/
theorem cornerGroup_mul_val {D : Challenge.Fam} {n r : ℕ}
    {l : Challenge.Half n} (hl : l ∈ Challenge.Hr D n r)
    (x y : Corner D n r l) :
    (@Mul.mul (Corner D n r l) (cornerGroup hl).toMul x y).val =
      Challenge.dmul x.val y.val := by
  change ((coordinateEquiv hl).symm
    (coordinateEquiv hl x * coordinateEquiv hl y)).val = Challenge.dmul x.val y.val
  have h : (coordinateEquiv hl).symm
      (coordinateEquiv hl x * coordinateEquiv hl y) = actualMul hl x y := by
    apply (coordinateEquiv hl).injective
    rw [Equiv.apply_symm_apply, coordinateEquiv_actualMul]
  exact congrArg Subtype.val h

theorem cornerGroup_one_val {D : Challenge.Fam} {n r : ℕ}
    {l : Challenge.Half n} (hl : l ∈ Challenge.Hr D n r) :
    (@One.one (Corner D n r l) (cornerGroup hl).toOne).val = Challenge.eDiag l := by
  change ((coordinateEquiv hl).symm 1).val = Challenge.eDiag l
  have h : (coordinateEquiv hl).symm 1 = diagonalCorner hl := by
    apply (coordinateEquiv hl).injective
    rw [Equiv.apply_symm_apply, coordinateEquiv_diagonalCorner]
  exact congrArg Subtype.val h

theorem cornerMulEquiv_apply {D : Challenge.Fam} {n r : ℕ}
    {l : Challenge.Half n} (hl : l ∈ Challenge.Hr D n r)
    (x : Corner D n r l) :
    let _ : Group (Corner D n r l) := cornerGroup hl
    cornerMulEquiv hl x = Challenge.gCoord r x.val := rfl

theorem check_CornerGroupAligned : CodexPaper5.FullPaperStatement.CornerGroupAligned := by
  intro D n r l hl
  refine ⟨cornerGroup hl, ?_⟩
  let _ : Group (Corner D n r l) := cornerGroup hl
  refine ⟨cornerMulEquiv hl, ?_, ?_, ?_⟩
  · intro x y
    exact cornerGroup_mul_val hl x y
  · exact cornerGroup_one_val hl
  · intro x
    exact cornerMulEquiv_apply hl x

end CodexPaper5.FullPaperCorner

#print axioms CodexPaper5.FullPaperCorner.assembleCorner
#print axioms CodexPaper5.FullPaperCorner.assembleCorner_gCoord
#print axioms CodexPaper5.FullPaperCorner.coordinateEquiv
#print axioms CodexPaper5.FullPaperCorner.coordinateEquiv_apply
#print axioms CodexPaper5.FullPaperCorner.actualMul
#print axioms CodexPaper5.FullPaperCorner.coordinateEquiv_actualMul
#print axioms CodexPaper5.FullPaperCorner.diagonalCorner
#print axioms CodexPaper5.FullPaperCorner.coordinateEquiv_diagonalCorner
#print axioms CodexPaper5.FullPaperCorner.cornerGroup
#print axioms CodexPaper5.FullPaperCorner.cornerMulEquiv
#print axioms CodexPaper5.FullPaperCorner.cornerGroup_mul_val
#print axioms CodexPaper5.FullPaperCorner.cornerGroup_one_val
#print axioms CodexPaper5.FullPaperCorner.cornerMulEquiv_apply
#print axioms CodexPaper5.FullPaperCorner.check_CornerGroupAligned
