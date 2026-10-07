import Research.Backfill.Paper5.Proof.BrauerTriangle
import Research.Backfill.Paper5.Proof.DiagramIdempotent

set_option autoImplicit false

namespace CodexPaper5.BrauerTriangleProduct

open BackfillPaper5

/-- The frozen threefold left-associated diagram product, using the actual stack operation. -/
theorem check_TriangleProduct : Challenge.TriangleProduct := by
  classical
  intro n r hr hn hpar
  obtain ⟨hf, h01, h12, h20, _, _, _, hsign⟩ :=
    BrauerTriangle.check_Lemma52 n r hr hn hpar
  let e : Fin 3 → Challenge.Pt n → Challenge.Pt n :=
    fun j => Challenge.eDiag (Challenge.triHalf n r j)
  let x01 := Challenge.dmul (e 0) (e 1)
  let x012 := Challenge.dmul x01 (e 2)
  let x := Challenge.dmul x012 (e 0)
  let p01 := Challenge.pSand r (Challenge.triHalf n r 0) (Challenge.triHalf n r 1)
  let p12 := Challenge.pSand r (Challenge.triHalf n r 1) (Challenge.triHalf n r 2)
  let p20 := Challenge.pSand r (Challenge.triHalf n r 2) (Challenge.triHalf n r 0)
  have he (j : Fin 3) : e j ∈ Challenge.Jr Challenge.Fam.B n r :=
    DiagramIdempotent.eDiag_mem_Jr (hf j)
  have het (j : Fin 3) : Challenge.topHalf (e j) = Challenge.triHalf n r j :=
    DiagramIdempotent.topHalf_eDiag (hf j)
  have heb (j : Fin 3) : Challenge.botHalf (e j) = Challenge.triHalf n r j :=
    DiagramIdempotent.botHalf_eDiag (hf j)
  have heg (j : Fin 3) : Challenge.gCoord r (e j) = 1 :=
    DiagramIdempotent.gCoord_eDiag (hf j)
  have hc01 : Challenge.Compat (Challenge.botHalf (e 0)) (Challenge.topHalf (e 1)) := by
    rw [heb 0, het 1]
    exact h01
  have hx01 : x01 ∈ Challenge.Jr Challenge.Fam.B n r :=
    DiagramMultiplication.dmul_mem_Jr_of_compat (he 0) (he 1) hc01
  have ht01 : Challenge.topHalf x01 = Challenge.triHalf n r 0 :=
    (DiagramMultiplication.topHalf_dmul_of_compat (he 0) (he 1) hc01).trans (het 0)
  have hb01 : Challenge.botHalf x01 = Challenge.triHalf n r 1 :=
    (DiagramMultiplication.botHalf_dmul_of_compat (he 0) (he 1) hc01).trans (heb 1)
  have hg01 : Challenge.gCoord r x01 = p01 := by
    calc
      Challenge.gCoord r x01 =
          Challenge.gCoord r (e 0) *
            Challenge.pSand r (Challenge.botHalf (e 0)) (Challenge.topHalf (e 1)) *
              Challenge.gCoord r (e 1) :=
        DiagramProductCoordinates.gCoord_dmul_of_compat (he 0) (he 1) hc01
      _ = p01 := by rw [heg 0, heg 1, heb 0, het 1, one_mul, mul_one]
  have hc12 : Challenge.Compat (Challenge.botHalf x01) (Challenge.topHalf (e 2)) := by
    rw [hb01, het 2]
    exact h12
  have hx012 : x012 ∈ Challenge.Jr Challenge.Fam.B n r :=
    DiagramMultiplication.dmul_mem_Jr_of_compat hx01 (he 2) hc12
  have ht012 : Challenge.topHalf x012 = Challenge.triHalf n r 0 :=
    (DiagramMultiplication.topHalf_dmul_of_compat hx01 (he 2) hc12).trans ht01
  have hb012 : Challenge.botHalf x012 = Challenge.triHalf n r 2 :=
    (DiagramMultiplication.botHalf_dmul_of_compat hx01 (he 2) hc12).trans (heb 2)
  have hg012 : Challenge.gCoord r x012 = p01 * p12 := by
    calc
      Challenge.gCoord r x012 =
          Challenge.gCoord r x01 * Challenge.pSand r (Challenge.botHalf x01) (Challenge.topHalf (e 2)) *
            Challenge.gCoord r (e 2) :=
        DiagramProductCoordinates.gCoord_dmul_of_compat hx01 (he 2) hc12
      _ = p01 * p12 := by rw [hg01, hb01, het 2, heg 2, mul_one]
  have hc20 : Challenge.Compat (Challenge.botHalf x012) (Challenge.topHalf (e 0)) := by
    rw [hb012, het 0]
    exact h20
  have hx : x ∈ Challenge.Jr Challenge.Fam.B n r :=
    DiagramMultiplication.dmul_mem_Jr_of_compat hx012 (he 0) hc20
  have htx : Challenge.topHalf x = Challenge.triHalf n r 0 :=
    (DiagramMultiplication.topHalf_dmul_of_compat hx012 (he 0) hc20).trans ht012
  have hbx : Challenge.botHalf x = Challenge.triHalf n r 0 :=
    (DiagramMultiplication.botHalf_dmul_of_compat hx012 (he 0) hc20).trans (heb 0)
  have hgx : Challenge.gCoord r x = p01 * p12 * p20 := by
    calc
      Challenge.gCoord r x =
          Challenge.gCoord r x012 *
            Challenge.pSand r (Challenge.botHalf x012) (Challenge.topHalf (e 0)) *
              Challenge.gCoord r (e 0) :=
        DiagramProductCoordinates.gCoord_dmul_of_compat hx012 (he 0) hc20
      _ = p01 * p12 * p20 := by rw [hg012, hb012, het 0, heg 0, mul_one]
  change x ∈ Challenge.Jr Challenge.Fam.B n r ∧
    Challenge.topHalf x = Challenge.triHalf n r 0 ∧
    Challenge.botHalf x = Challenge.triHalf n r 0 ∧
    Challenge.gCoord r x = p01 * p12 * p20 ∧ Challenge.sgn (Challenge.gCoord r x) = 1
  refine ⟨hx, htx, hbx, hgx, ?_⟩
  rw [hgx]
  exact hsign

#print axioms CodexPaper5.BrauerTriangleProduct.check_TriangleProduct

end CodexPaper5.BrauerTriangleProduct
