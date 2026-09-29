import Research.Backfill.Paper3.Proof.Small.Cubic
import Research.Backfill.Paper3.Proof.Small.Counts
import Research.Backfill.Paper3.Proof.Small.Counts6

/-!
# Table 1 and the counts of Table 4

Each graph is identified with an edge mask by an explicit isomorphism (checked by the kernel on
all pairs of vertices), `N_{≤t}` is transported along it (`P3Basic.iCount_iso`) and computed by
`nleB` (`iCount_maskGraph`); the values of `nleB` are the kernel computations of
`Research.Backfill.Paper3.Proof.Small.Counts` and `Research.Backfill.Paper3.Proof.Small.Counts6`.
-/

set_option autoImplicit false

namespace P3Small

open Finset SimpleGraph BackfillPaper3.Challenge

/-- The labelling `(k, inl i) ↦ 2dk + i`, `(k, inr j) ↦ 2dk + d + j` of `m` copies of
`Fin d ⊕ Fin d`. -/
def eBlocks (m d : ℕ) : Fin m × (Fin d ⊕ Fin d) ≃ Fin (m * (d + d)) :=
  (Equiv.prodCongr (Equiv.refl (Fin m)) finSumFinEquiv).trans finProdFinEquiv

/-- `H_3` (canonical labelling) is the mask graph `maskH3`. -/
def isoH3 : Hd 3 0 0 0 0 ≃g maskGraph 12 maskH3 where
  toEquiv := eBlocks 2 3
  map_rel_iff' := by decide +kernel

/-- `2 K_{3,3}` is the mask graph `maskK23`. -/
def isoK23 : KddUnion 2 3 ≃g maskGraph 12 maskK23 where
  toEquiv := eBlocks 2 3
  map_rel_iff' := by decide +kernel

/-- `3 K_4` is the mask graph `maskK34` (`(k, i) ↦ 4k + i`). -/
def isoK34 : threeK4 ≃g maskGraph 12 maskK34 where
  toEquiv := finProdFinEquiv
  map_rel_iff' := by decide +kernel

/-- `2 K_{2,2}` is the mask graph `maskK22`. -/
def isoK22 : KddUnion 2 2 ≃g maskGraph 8 maskK22 where
  toEquiv := eBlocks 2 2
  map_rel_iff' := by decide +kernel

/-- `C_8` is the mask graph `maskC8`. -/
def isoC8 : cycleGraph 8 ≃g maskGraph 8 maskC8 where
  toEquiv := Equiv.refl _
  map_rel_iff' := by decide +kernel

/-- `1 K_{3,3}` is the mask graph `k33Mask`. -/
def isoK13 : KddUnion 1 3 ≃g maskGraph 6 k33Mask where
  toEquiv := eBlocks 1 3
  map_rel_iff' := by decide +kernel

theorem iCount_K33 (t : ℕ) : iCount (Kdd 3) t = nleB 6 k33Mask t := by
  rw [P3Basic.iCount_iso isoK33, iCount_maskGraph]

theorem iCount_prism (t : ℕ) : iCount prism t = nleB 6 prismMask t := by
  rw [P3Basic.iCount_iso isoPrism, iCount_maskGraph]

theorem iCount_K13 (t : ℕ) : iCount (KddUnion 1 3) t = nleB 6 k33Mask t := by
  rw [P3Basic.iCount_iso isoK13, iCount_maskGraph]

theorem iCount_H3 (t : ℕ) : iCount (Hd 3 0 0 0 0) t = nleB 12 maskH3 t := by
  rw [P3Basic.iCount_iso isoH3, iCount_maskGraph]

theorem iCount_K23 (t : ℕ) : iCount (KddUnion 2 3) t = nleB 12 maskK23 t := by
  rw [P3Basic.iCount_iso isoK23, iCount_maskGraph]

theorem iCount_K34 (t : ℕ) : iCount threeK4 t = nleB 12 maskK34 t := by
  rw [P3Basic.iCount_iso isoK34, iCount_maskGraph]

theorem iCount_K22 (t : ℕ) : iCount (KddUnion 2 2) t = nleB 8 maskK22 t := by
  rw [P3Basic.iCount_iso isoK22, iCount_maskGraph]

theorem iCount_C8 (t : ℕ) : iCount (cycleGraph 8) t = nleB 8 maskC8 t := by
  rw [P3Basic.iCount_iso isoC8, iCount_maskGraph]

/-- Table 1: `N_{≤t}` of `K_{3,3}` and of the prism for `t = 0, …, 9`. -/
theorem table1 : Table1 := by
  unfold Table1
  constructor
  · rw [List.map_congr_left fun t _ => iCount_K33 t]
    exact table1_k33
  · rw [List.map_congr_left fun t _ => iCount_prism t]
    exact table1_prism

/-- §9, Table 4 and Remark 4: `28 > 24`, `111 > 105`, `527 > 495`, `4002 > 3981`. -/
theorem table4Counts : Table4Counts := by
  unfold Table4Counts
  exact ⟨(iCount_prism 1).trans nleB_prism_one, (iCount_K33 1).trans nleB_k33_one,
    (iCount_C8 1).trans nleB_C8, (iCount_K22 1).trans nleB_K22,
    (iCount_H3 1).trans nleB_H3, (iCount_K23 1).trans nleB_K23_one,
    (iCount_K34 10).trans nleB_K34, (iCount_K23 10).trans nleB_K23_ten⟩

end P3Small
