import Research.Backfill.Paper4.Proof.TriangleFreeEnumerationFamily

/-! Finite triangle-free enumeration certificate candidate.
Formal acceptance and resource measurements are recorded separately.
This module does not on its own establish the frozen ClassCount target. -/
set_option autoImplicit false
set_option maxRecDepth 4096

namespace CodexPaper4.TriangleFreeEnumerationValidity
open SimpleGraph TriangleFreeEnumerationCore TriangleFreeEnumerationFamily

theorem rep_valid_1_00 : (reps 1 0).Connected ∧ (reps 1 0).CliqueFree 3 := by
  constructor
  · exact connected_of_rank (reps 1 0) (0 : Fin 1)
      (fun v => ([0] : List ℕ).getD v.val 0)
      (by decide +kernel) (by decide +kernel)
  · decide +kernel

theorem valid_level_1 : ∀ i : Fin (repCount 1),
    (reps 1 i).Connected ∧ (reps 1 i).CliqueFree 3 := by
  intro i
  fin_cases i
  · exact rep_valid_1_00

theorem rep_valid_2_00 : (reps 2 0).Connected ∧ (reps 2 0).CliqueFree 3 := by
  constructor
  · exact connected_of_rank (reps 2 0) (0 : Fin 2)
      (fun v => ([0, 1] : List ℕ).getD v.val 0)
      (by decide +kernel) (by decide +kernel)
  · decide +kernel

theorem valid_level_2 : ∀ i : Fin (repCount 2),
    (reps 2 i).Connected ∧ (reps 2 i).CliqueFree 3 := by
  intro i
  fin_cases i
  · exact rep_valid_2_00

theorem rep_valid_3_00 : (reps 3 0).Connected ∧ (reps 3 0).CliqueFree 3 := by
  constructor
  · exact connected_of_rank (reps 3 0) (0 : Fin 3)
      (fun v => ([0, 1, 1] : List ℕ).getD v.val 0)
      (by decide +kernel) (by decide +kernel)
  · decide +kernel

theorem valid_level_3 : ∀ i : Fin (repCount 3),
    (reps 3 i).Connected ∧ (reps 3 i).CliqueFree 3 := by
  intro i
  fin_cases i
  · exact rep_valid_3_00

theorem rep_valid_4_00 : (reps 4 0).Connected ∧ (reps 4 0).CliqueFree 3 := by
  constructor
  · exact connected_of_rank (reps 4 0) (0 : Fin 4)
      (fun v => ([0, 2, 2, 1] : List ℕ).getD v.val 0)
      (by decide +kernel) (by decide +kernel)
  · decide +kernel

theorem rep_valid_4_01 : (reps 4 1).Connected ∧ (reps 4 1).CliqueFree 3 := by
  constructor
  · exact connected_of_rank (reps 4 1) (0 : Fin 4)
      (fun v => ([0, 1, 2, 1] : List ℕ).getD v.val 0)
      (by decide +kernel) (by decide +kernel)
  · decide +kernel

theorem rep_valid_4_02 : (reps 4 2).Connected ∧ (reps 4 2).CliqueFree 3 := by
  constructor
  · exact connected_of_rank (reps 4 2) (0 : Fin 4)
      (fun v => ([0, 1, 2, 1] : List ℕ).getD v.val 0)
      (by decide +kernel) (by decide +kernel)
  · decide +kernel

theorem valid_level_4 : ∀ i : Fin (repCount 4),
    (reps 4 i).Connected ∧ (reps 4 i).CliqueFree 3 := by
  intro i
  fin_cases i
  · exact rep_valid_4_00
  · exact rep_valid_4_01
  · exact rep_valid_4_02

theorem rep_valid_5_00 : (reps 5 0).Connected ∧ (reps 5 0).CliqueFree 3 := by
  constructor
  · exact connected_of_rank (reps 5 0) (0 : Fin 5)
      (fun v => ([0, 2, 2, 2, 1] : List ℕ).getD v.val 0)
      (by decide +kernel) (by decide +kernel)
  · decide +kernel

theorem rep_valid_5_01 : (reps 5 1).Connected ∧ (reps 5 1).CliqueFree 3 := by
  constructor
  · exact connected_of_rank (reps 5 1) (0 : Fin 5)
      (fun v => ([0, 3, 3, 2, 1] : List ℕ).getD v.val 0)
      (by decide +kernel) (by decide +kernel)
  · decide +kernel

theorem rep_valid_5_02 : (reps 5 2).Connected ∧ (reps 5 2).CliqueFree 3 := by
  constructor
  · exact connected_of_rank (reps 5 2) (0 : Fin 5)
      (fun v => ([0, 1, 2, 3, 1] : List ℕ).getD v.val 0)
      (by decide +kernel) (by decide +kernel)
  · decide +kernel

theorem rep_valid_5_03 : (reps 5 3).Connected ∧ (reps 5 3).CliqueFree 3 := by
  constructor
  · exact connected_of_rank (reps 5 3) (0 : Fin 5)
      (fun v => ([0, 1, 3, 2, 2] : List ℕ).getD v.val 0)
      (by decide +kernel) (by decide +kernel)
  · decide +kernel

theorem rep_valid_5_04 : (reps 5 4).Connected ∧ (reps 5 4).CliqueFree 3 := by
  constructor
  · exact connected_of_rank (reps 5 4) (0 : Fin 5)
      (fun v => ([0, 1, 2, 2, 1] : List ℕ).getD v.val 0)
      (by decide +kernel) (by decide +kernel)
  · decide +kernel

theorem rep_valid_5_05 : (reps 5 5).Connected ∧ (reps 5 5).CliqueFree 3 := by
  constructor
  · exact connected_of_rank (reps 5 5) (0 : Fin 5)
      (fun v => ([0, 2, 1, 1, 1] : List ℕ).getD v.val 0)
      (by decide +kernel) (by decide +kernel)
  · decide +kernel

theorem valid_level_5 : ∀ i : Fin (repCount 5),
    (reps 5 i).Connected ∧ (reps 5 i).CliqueFree 3 := by
  intro i
  fin_cases i
  · exact rep_valid_5_00
  · exact rep_valid_5_01
  · exact rep_valid_5_02
  · exact rep_valid_5_03
  · exact rep_valid_5_04
  · exact rep_valid_5_05

theorem rep_valid_6_00 : (reps 6 0).Connected ∧ (reps 6 0).CliqueFree 3 := by
  constructor
  · exact connected_of_rank (reps 6 0) (0 : Fin 6)
      (fun v => ([0, 2, 2, 2, 2, 1] : List ℕ).getD v.val 0)
      (by decide +kernel) (by decide +kernel)
  · decide +kernel

theorem rep_valid_6_01 : (reps 6 1).Connected ∧ (reps 6 1).CliqueFree 3 := by
  constructor
  · exact connected_of_rank (reps 6 1) (0 : Fin 6)
      (fun v => ([0, 1, 2, 3, 2, 2] : List ℕ).getD v.val 0)
      (by decide +kernel) (by decide +kernel)
  · decide +kernel

theorem rep_valid_6_02 : (reps 6 2).Connected ∧ (reps 6 2).CliqueFree 3 := by
  constructor
  · exact connected_of_rank (reps 6 2) (0 : Fin 6)
      (fun v => ([0, 1, 1, 1, 2, 2] : List ℕ).getD v.val 0)
      (by decide +kernel) (by decide +kernel)
  · decide +kernel

theorem rep_valid_6_03 : (reps 6 3).Connected ∧ (reps 6 3).CliqueFree 3 := by
  constructor
  · exact connected_of_rank (reps 6 3) (0 : Fin 6)
      (fun v => ([0, 1, 2, 2, 3, 3] : List ℕ).getD v.val 0)
      (by decide +kernel) (by decide +kernel)
  · decide +kernel

theorem rep_valid_6_04 : (reps 6 4).Connected ∧ (reps 6 4).CliqueFree 3 := by
  constructor
  · exact connected_of_rank (reps 6 4) (0 : Fin 6)
      (fun v => ([0, 3, 3, 2, 1, 1] : List ℕ).getD v.val 0)
      (by decide +kernel) (by decide +kernel)
  · decide +kernel

theorem rep_valid_6_05 : (reps 6 5).Connected ∧ (reps 6 5).CliqueFree 3 := by
  constructor
  · exact connected_of_rank (reps 6 5) (0 : Fin 6)
      (fun v => ([0, 1, 4, 3, 2, 1] : List ℕ).getD v.val 0)
      (by decide +kernel) (by decide +kernel)
  · decide +kernel

theorem rep_valid_6_06 : (reps 6 6).Connected ∧ (reps 6 6).CliqueFree 3 := by
  constructor
  · exact connected_of_rank (reps 6 6) (0 : Fin 6)
      (fun v => ([0, 2, 1, 1, 1, 1] : List ℕ).getD v.val 0)
      (by decide +kernel) (by decide +kernel)
  · decide +kernel

theorem rep_valid_6_07 : (reps 6 7).Connected ∧ (reps 6 7).CliqueFree 3 := by
  constructor
  · exact connected_of_rank (reps 6 7) (0 : Fin 6)
      (fun v => ([0, 2, 1, 1, 1, 2] : List ℕ).getD v.val 0)
      (by decide +kernel) (by decide +kernel)
  · decide +kernel

theorem rep_valid_6_08 : (reps 6 8).Connected ∧ (reps 6 8).CliqueFree 3 := by
  constructor
  · exact connected_of_rank (reps 6 8) (0 : Fin 6)
      (fun v => ([0, 4, 1, 3, 2, 2] : List ℕ).getD v.val 0)
      (by decide +kernel) (by decide +kernel)
  · decide +kernel

theorem rep_valid_6_09 : (reps 6 9).Connected ∧ (reps 6 9).CliqueFree 3 := by
  constructor
  · exact connected_of_rank (reps 6 9) (0 : Fin 6)
      (fun v => ([0, 2, 2, 3, 1, 1] : List ℕ).getD v.val 0)
      (by decide +kernel) (by decide +kernel)
  · decide +kernel

theorem rep_valid_6_10 : (reps 6 10).Connected ∧ (reps 6 10).CliqueFree 3 := by
  constructor
  · exact connected_of_rank (reps 6 10) (0 : Fin 6)
      (fun v => ([0, 1, 2, 2, 1, 2] : List ℕ).getD v.val 0)
      (by decide +kernel) (by decide +kernel)
  · decide +kernel

theorem rep_valid_6_11 : (reps 6 11).Connected ∧ (reps 6 11).CliqueFree 3 := by
  constructor
  · exact connected_of_rank (reps 6 11) (0 : Fin 6)
      (fun v => ([0, 1, 2, 3, 2, 1] : List ℕ).getD v.val 0)
      (by decide +kernel) (by decide +kernel)
  · decide +kernel

theorem rep_valid_6_12 : (reps 6 12).Connected ∧ (reps 6 12).CliqueFree 3 := by
  constructor
  · exact connected_of_rank (reps 6 12) (0 : Fin 6)
      (fun v => ([0, 2, 1, 2, 3, 2] : List ℕ).getD v.val 0)
      (by decide +kernel) (by decide +kernel)
  · decide +kernel

theorem rep_valid_6_13 : (reps 6 13).Connected ∧ (reps 6 13).CliqueFree 3 := by
  constructor
  · exact connected_of_rank (reps 6 13) (0 : Fin 6)
      (fun v => ([0, 2, 1, 3, 3, 2] : List ℕ).getD v.val 0)
      (by decide +kernel) (by decide +kernel)
  · decide +kernel

theorem rep_valid_6_14 : (reps 6 14).Connected ∧ (reps 6 14).CliqueFree 3 := by
  constructor
  · exact connected_of_rank (reps 6 14) (0 : Fin 6)
      (fun v => ([0, 1, 2, 1, 2, 1] : List ℕ).getD v.val 0)
      (by decide +kernel) (by decide +kernel)
  · decide +kernel

theorem rep_valid_6_15 : (reps 6 15).Connected ∧ (reps 6 15).CliqueFree 3 := by
  constructor
  · exact connected_of_rank (reps 6 15) (0 : Fin 6)
      (fun v => ([0, 1, 2, 2, 1, 1] : List ℕ).getD v.val 0)
      (by decide +kernel) (by decide +kernel)
  · decide +kernel

theorem rep_valid_6_16 : (reps 6 16).Connected ∧ (reps 6 16).CliqueFree 3 := by
  constructor
  · exact connected_of_rank (reps 6 16) (0 : Fin 6)
      (fun v => ([0, 2, 2, 2, 1, 1] : List ℕ).getD v.val 0)
      (by decide +kernel) (by decide +kernel)
  · decide +kernel

theorem rep_valid_6_17 : (reps 6 17).Connected ∧ (reps 6 17).CliqueFree 3 := by
  constructor
  · exact connected_of_rank (reps 6 17) (0 : Fin 6)
      (fun v => ([0, 1, 2, 3, 2, 1] : List ℕ).getD v.val 0)
      (by decide +kernel) (by decide +kernel)
  · decide +kernel

theorem rep_valid_6_18 : (reps 6 18).Connected ∧ (reps 6 18).CliqueFree 3 := by
  constructor
  · exact connected_of_rank (reps 6 18) (0 : Fin 6)
      (fun v => ([0, 1, 2, 1, 2, 1] : List ℕ).getD v.val 0)
      (by decide +kernel) (by decide +kernel)
  · decide +kernel

theorem valid_level_6 : ∀ i : Fin (repCount 6),
    (reps 6 i).Connected ∧ (reps 6 i).CliqueFree 3 := by
  intro i
  fin_cases i
  · exact rep_valid_6_00
  · exact rep_valid_6_01
  · exact rep_valid_6_02
  · exact rep_valid_6_03
  · exact rep_valid_6_04
  · exact rep_valid_6_05
  · exact rep_valid_6_06
  · exact rep_valid_6_07
  · exact rep_valid_6_08
  · exact rep_valid_6_09
  · exact rep_valid_6_10
  · exact rep_valid_6_11
  · exact rep_valid_6_12
  · exact rep_valid_6_13
  · exact rep_valid_6_14
  · exact rep_valid_6_15
  · exact rep_valid_6_16
  · exact rep_valid_6_17
  · exact rep_valid_6_18

theorem rep_valid_7_00 : (reps 7 0).Connected ∧ (reps 7 0).CliqueFree 3 := by
  constructor
  · exact connected_of_rank (reps 7 0) (0 : Fin 7)
      (fun v => ([0, 2, 2, 2, 2, 2, 1] : List ℕ).getD v.val 0)
      (by decide +kernel) (by decide +kernel)
  · decide +kernel

theorem rep_valid_7_01 : (reps 7 1).Connected ∧ (reps 7 1).CliqueFree 3 := by
  constructor
  · exact connected_of_rank (reps 7 1) (0 : Fin 7)
      (fun v => ([0, 1, 2, 3, 3, 3, 3] : List ℕ).getD v.val 0)
      (by decide +kernel) (by decide +kernel)
  · decide +kernel

theorem rep_valid_7_02 : (reps 7 2).Connected ∧ (reps 7 2).CliqueFree 3 := by
  constructor
  · exact connected_of_rank (reps 7 2) (0 : Fin 7)
      (fun v => ([0, 1, 2, 2, 2, 3, 3] : List ℕ).getD v.val 0)
      (by decide +kernel) (by decide +kernel)
  · decide +kernel

theorem rep_valid_7_03 : (reps 7 3).Connected ∧ (reps 7 3).CliqueFree 3 := by
  constructor
  · exact connected_of_rank (reps 7 3) (0 : Fin 7)
      (fun v => ([0, 1, 2, 2, 2, 3, 3] : List ℕ).getD v.val 0)
      (by decide +kernel) (by decide +kernel)
  · decide +kernel

theorem rep_valid_7_04 : (reps 7 4).Connected ∧ (reps 7 4).CliqueFree 3 := by
  constructor
  · exact connected_of_rank (reps 7 4) (0 : Fin 7)
      (fun v => ([0, 1, 2, 2, 2, 3, 4] : List ℕ).getD v.val 0)
      (by decide +kernel) (by decide +kernel)
  · decide +kernel

theorem rep_valid_7_05 : (reps 7 5).Connected ∧ (reps 7 5).CliqueFree 3 := by
  constructor
  · exact connected_of_rank (reps 7 5) (0 : Fin 7)
      (fun v => ([0, 2, 3, 3, 1, 4, 4] : List ℕ).getD v.val 0)
      (by decide +kernel) (by decide +kernel)
  · decide +kernel

theorem rep_valid_7_06 : (reps 7 6).Connected ∧ (reps 7 6).CliqueFree 3 := by
  constructor
  · exact connected_of_rank (reps 7 6) (0 : Fin 7)
      (fun v => ([0, 1, 2, 1, 1, 3, 3] : List ℕ).getD v.val 0)
      (by decide +kernel) (by decide +kernel)
  · decide +kernel

theorem rep_valid_7_07 : (reps 7 7).Connected ∧ (reps 7 7).CliqueFree 3 := by
  constructor
  · exact connected_of_rank (reps 7 7) (0 : Fin 7)
      (fun v => ([0, 1, 4, 2, 2, 3, 3] : List ℕ).getD v.val 0)
      (by decide +kernel) (by decide +kernel)
  · decide +kernel

theorem rep_valid_7_08 : (reps 7 8).Connected ∧ (reps 7 8).CliqueFree 3 := by
  constructor
  · exact connected_of_rank (reps 7 8) (0 : Fin 7)
      (fun v => ([0, 2, 4, 1, 3, 5, 5] : List ℕ).getD v.val 0)
      (by decide +kernel) (by decide +kernel)
  · decide +kernel

theorem rep_valid_7_09 : (reps 7 9).Connected ∧ (reps 7 9).CliqueFree 3 := by
  constructor
  · exact connected_of_rank (reps 7 9) (0 : Fin 7)
      (fun v => ([0, 1, 2, 1, 1, 2, 2] : List ℕ).getD v.val 0)
      (by decide +kernel) (by decide +kernel)
  · decide +kernel

theorem rep_valid_7_10 : (reps 7 10).Connected ∧ (reps 7 10).CliqueFree 3 := by
  constructor
  · exact connected_of_rank (reps 7 10) (0 : Fin 7)
      (fun v => ([0, 1, 2, 3, 4, 5, 1] : List ℕ).getD v.val 0)
      (by decide +kernel) (by decide +kernel)
  · decide +kernel

theorem rep_valid_7_11 : (reps 7 11).Connected ∧ (reps 7 11).CliqueFree 3 := by
  constructor
  · exact connected_of_rank (reps 7 11) (0 : Fin 7)
      (fun v => ([0, 2, 3, 1, 1, 3, 3] : List ℕ).getD v.val 0)
      (by decide +kernel) (by decide +kernel)
  · decide +kernel

theorem rep_valid_7_12 : (reps 7 12).Connected ∧ (reps 7 12).CliqueFree 3 := by
  constructor
  · exact connected_of_rank (reps 7 12) (0 : Fin 7)
      (fun v => ([0, 3, 2, 3, 2, 1, 2] : List ℕ).getD v.val 0)
      (by decide +kernel) (by decide +kernel)
  · decide +kernel

theorem rep_valid_7_13 : (reps 7 13).Connected ∧ (reps 7 13).CliqueFree 3 := by
  constructor
  · exact connected_of_rank (reps 7 13) (0 : Fin 7)
      (fun v => ([0, 1, 3, 2, 2, 4, 4] : List ℕ).getD v.val 0)
      (by decide +kernel) (by decide +kernel)
  · decide +kernel

theorem rep_valid_7_14 : (reps 7 14).Connected ∧ (reps 7 14).CliqueFree 3 := by
  constructor
  · exact connected_of_rank (reps 7 14) (0 : Fin 7)
      (fun v => ([0, 2, 3, 1, 1, 2, 2] : List ℕ).getD v.val 0)
      (by decide +kernel) (by decide +kernel)
  · decide +kernel

theorem rep_valid_7_15 : (reps 7 15).Connected ∧ (reps 7 15).CliqueFree 3 := by
  constructor
  · exact connected_of_rank (reps 7 15) (0 : Fin 7)
      (fun v => ([0, 2, 3, 1, 1, 4, 3] : List ℕ).getD v.val 0)
      (by decide +kernel) (by decide +kernel)
  · decide +kernel

theorem rep_valid_7_16 : (reps 7 16).Connected ∧ (reps 7 16).CliqueFree 3 := by
  constructor
  · exact connected_of_rank (reps 7 16) (0 : Fin 7)
      (fun v => ([0, 1, 1, 2, 1, 1, 2] : List ℕ).getD v.val 0)
      (by decide +kernel) (by decide +kernel)
  · decide +kernel

theorem rep_valid_7_17 : (reps 7 17).Connected ∧ (reps 7 17).CliqueFree 3 := by
  constructor
  · exact connected_of_rank (reps 7 17) (0 : Fin 7)
      (fun v => ([0, 1, 2, 3, 4, 2, 3] : List ℕ).getD v.val 0)
      (by decide +kernel) (by decide +kernel)
  · decide +kernel

theorem rep_valid_7_18 : (reps 7 18).Connected ∧ (reps 7 18).CliqueFree 3 := by
  constructor
  · exact connected_of_rank (reps 7 18) (0 : Fin 7)
      (fun v => ([0, 1, 2, 3, 1, 2, 3] : List ℕ).getD v.val 0)
      (by decide +kernel) (by decide +kernel)
  · decide +kernel

theorem rep_valid_7_19 : (reps 7 19).Connected ∧ (reps 7 19).CliqueFree 3 := by
  constructor
  · exact connected_of_rank (reps 7 19) (0 : Fin 7)
      (fun v => ([0, 1, 1, 2, 2, 1, 3] : List ℕ).getD v.val 0)
      (by decide +kernel) (by decide +kernel)
  · decide +kernel

theorem rep_valid_7_20 : (reps 7 20).Connected ∧ (reps 7 20).CliqueFree 3 := by
  constructor
  · exact connected_of_rank (reps 7 20) (0 : Fin 7)
      (fun v => ([0, 2, 1, 2, 2, 1, 2] : List ℕ).getD v.val 0)
      (by decide +kernel) (by decide +kernel)
  · decide +kernel

theorem rep_valid_7_21 : (reps 7 21).Connected ∧ (reps 7 21).CliqueFree 3 := by
  constructor
  · exact connected_of_rank (reps 7 21) (0 : Fin 7)
      (fun v => ([0, 2, 3, 1, 1, 4, 4] : List ℕ).getD v.val 0)
      (by decide +kernel) (by decide +kernel)
  · decide +kernel

theorem rep_valid_7_22 : (reps 7 22).Connected ∧ (reps 7 22).CliqueFree 3 := by
  constructor
  · exact connected_of_rank (reps 7 22) (0 : Fin 7)
      (fun v => ([0, 4, 3, 1, 1, 2, 2] : List ℕ).getD v.val 0)
      (by decide +kernel) (by decide +kernel)
  · decide +kernel

theorem rep_valid_7_23 : (reps 7 23).Connected ∧ (reps 7 23).CliqueFree 3 := by
  constructor
  · exact connected_of_rank (reps 7 23) (0 : Fin 7)
      (fun v => ([0, 2, 3, 1, 1, 5, 4] : List ℕ).getD v.val 0)
      (by decide +kernel) (by decide +kernel)
  · decide +kernel

theorem rep_valid_7_24 : (reps 7 24).Connected ∧ (reps 7 24).CliqueFree 3 := by
  constructor
  · exact connected_of_rank (reps 7 24) (0 : Fin 7)
      (fun v => ([0, 2, 1, 2, 1, 1, 2] : List ℕ).getD v.val 0)
      (by decide +kernel) (by decide +kernel)
  · decide +kernel

theorem rep_valid_7_25 : (reps 7 25).Connected ∧ (reps 7 25).CliqueFree 3 := by
  constructor
  · exact connected_of_rank (reps 7 25) (0 : Fin 7)
      (fun v => ([0, 1, 2, 3, 3, 2, 1] : List ℕ).getD v.val 0)
      (by decide +kernel) (by decide +kernel)
  · decide +kernel

theorem rep_valid_7_26 : (reps 7 26).Connected ∧ (reps 7 26).CliqueFree 3 := by
  constructor
  · exact connected_of_rank (reps 7 26) (0 : Fin 7)
      (fun v => ([0, 1, 2, 1, 1, 3, 3] : List ℕ).getD v.val 0)
      (by decide +kernel) (by decide +kernel)
  · decide +kernel

theorem rep_valid_7_27 : (reps 7 27).Connected ∧ (reps 7 27).CliqueFree 3 := by
  constructor
  · exact connected_of_rank (reps 7 27) (0 : Fin 7)
      (fun v => ([0, 2, 2, 1, 1, 2, 2] : List ℕ).getD v.val 0)
      (by decide +kernel) (by decide +kernel)
  · decide +kernel

theorem rep_valid_7_28 : (reps 7 28).Connected ∧ (reps 7 28).CliqueFree 3 := by
  constructor
  · exact connected_of_rank (reps 7 28) (0 : Fin 7)
      (fun v => ([0, 2, 2, 1, 1, 2, 3] : List ℕ).getD v.val 0)
      (by decide +kernel) (by decide +kernel)
  · decide +kernel

theorem rep_valid_7_29 : (reps 7 29).Connected ∧ (reps 7 29).CliqueFree 3 := by
  constructor
  · exact connected_of_rank (reps 7 29) (0 : Fin 7)
      (fun v => ([0, 2, 2, 1, 1, 3, 3] : List ℕ).getD v.val 0)
      (by decide +kernel) (by decide +kernel)
  · decide +kernel

theorem rep_valid_7_30 : (reps 7 30).Connected ∧ (reps 7 30).CliqueFree 3 := by
  constructor
  · exact connected_of_rank (reps 7 30) (0 : Fin 7)
      (fun v => ([0, 2, 2, 1, 1, 3, 1] : List ℕ).getD v.val 0)
      (by decide +kernel) (by decide +kernel)
  · decide +kernel

theorem rep_valid_7_31 : (reps 7 31).Connected ∧ (reps 7 31).CliqueFree 3 := by
  constructor
  · exact connected_of_rank (reps 7 31) (0 : Fin 7)
      (fun v => ([0, 1, 2, 3, 2, 2, 3] : List ℕ).getD v.val 0)
      (by decide +kernel) (by decide +kernel)
  · decide +kernel

theorem rep_valid_7_32 : (reps 7 32).Connected ∧ (reps 7 32).CliqueFree 3 := by
  constructor
  · exact connected_of_rank (reps 7 32) (0 : Fin 7)
      (fun v => ([0, 1, 2, 3, 3, 2, 2] : List ℕ).getD v.val 0)
      (by decide +kernel) (by decide +kernel)
  · decide +kernel

theorem rep_valid_7_33 : (reps 7 33).Connected ∧ (reps 7 33).CliqueFree 3 := by
  constructor
  · exact connected_of_rank (reps 7 33) (0 : Fin 7)
      (fun v => ([0, 2, 2, 1, 1, 2, 3] : List ℕ).getD v.val 0)
      (by decide +kernel) (by decide +kernel)
  · decide +kernel

theorem rep_valid_7_34 : (reps 7 34).Connected ∧ (reps 7 34).CliqueFree 3 := by
  constructor
  · exact connected_of_rank (reps 7 34) (0 : Fin 7)
      (fun v => ([0, 2, 3, 2, 1, 3, 4] : List ℕ).getD v.val 0)
      (by decide +kernel) (by decide +kernel)
  · decide +kernel

theorem rep_valid_7_35 : (reps 7 35).Connected ∧ (reps 7 35).CliqueFree 3 := by
  constructor
  · exact connected_of_rank (reps 7 35) (0 : Fin 7)
      (fun v => ([0, 3, 2, 3, 1, 2, 3] : List ℕ).getD v.val 0)
      (by decide +kernel) (by decide +kernel)
  · decide +kernel

theorem rep_valid_7_36 : (reps 7 36).Connected ∧ (reps 7 36).CliqueFree 3 := by
  constructor
  · exact connected_of_rank (reps 7 36) (0 : Fin 7)
      (fun v => ([0, 2, 2, 1, 2, 1, 1] : List ℕ).getD v.val 0)
      (by decide +kernel) (by decide +kernel)
  · decide +kernel

theorem rep_valid_7_37 : (reps 7 37).Connected ∧ (reps 7 37).CliqueFree 3 := by
  constructor
  · exact connected_of_rank (reps 7 37) (0 : Fin 7)
      (fun v => ([0, 2, 2, 1, 1, 3, 4] : List ℕ).getD v.val 0)
      (by decide +kernel) (by decide +kernel)
  · decide +kernel

theorem rep_valid_7_38 : (reps 7 38).Connected ∧ (reps 7 38).CliqueFree 3 := by
  constructor
  · exact connected_of_rank (reps 7 38) (0 : Fin 7)
      (fun v => ([0, 1, 3, 4, 3, 1, 2] : List ℕ).getD v.val 0)
      (by decide +kernel) (by decide +kernel)
  · decide +kernel

theorem rep_valid_7_39 : (reps 7 39).Connected ∧ (reps 7 39).CliqueFree 3 := by
  constructor
  · exact connected_of_rank (reps 7 39) (0 : Fin 7)
      (fun v => ([0, 1, 2, 3, 1, 2, 3] : List ℕ).getD v.val 0)
      (by decide +kernel) (by decide +kernel)
  · decide +kernel

theorem rep_valid_7_40 : (reps 7 40).Connected ∧ (reps 7 40).CliqueFree 3 := by
  constructor
  · exact connected_of_rank (reps 7 40) (0 : Fin 7)
      (fun v => ([0, 1, 2, 3, 2, 1, 2] : List ℕ).getD v.val 0)
      (by decide +kernel) (by decide +kernel)
  · decide +kernel

theorem rep_valid_7_41 : (reps 7 41).Connected ∧ (reps 7 41).CliqueFree 3 := by
  constructor
  · exact connected_of_rank (reps 7 41) (0 : Fin 7)
      (fun v => ([0, 1, 2, 2, 2, 1, 1] : List ℕ).getD v.val 0)
      (by decide +kernel) (by decide +kernel)
  · decide +kernel

theorem rep_valid_7_42 : (reps 7 42).Connected ∧ (reps 7 42).CliqueFree 3 := by
  constructor
  · exact connected_of_rank (reps 7 42) (0 : Fin 7)
      (fun v => ([0, 2, 2, 2, 1, 1, 2] : List ℕ).getD v.val 0)
      (by decide +kernel) (by decide +kernel)
  · decide +kernel

theorem rep_valid_7_43 : (reps 7 43).Connected ∧ (reps 7 43).CliqueFree 3 := by
  constructor
  · exact connected_of_rank (reps 7 43) (0 : Fin 7)
      (fun v => ([0, 2, 2, 2, 1, 1, 3] : List ℕ).getD v.val 0)
      (by decide +kernel) (by decide +kernel)
  · decide +kernel

theorem rep_valid_7_44 : (reps 7 44).Connected ∧ (reps 7 44).CliqueFree 3 := by
  constructor
  · exact connected_of_rank (reps 7 44) (0 : Fin 7)
      (fun v => ([0, 1, 2, 3, 2, 1, 2] : List ℕ).getD v.val 0)
      (by decide +kernel) (by decide +kernel)
  · decide +kernel

theorem rep_valid_7_45 : (reps 7 45).Connected ∧ (reps 7 45).CliqueFree 3 := by
  constructor
  · exact connected_of_rank (reps 7 45) (0 : Fin 7)
      (fun v => ([0, 1, 2, 3, 2, 1, 1] : List ℕ).getD v.val 0)
      (by decide +kernel) (by decide +kernel)
  · decide +kernel

theorem rep_valid_7_46 : (reps 7 46).Connected ∧ (reps 7 46).CliqueFree 3 := by
  constructor
  · exact connected_of_rank (reps 7 46) (0 : Fin 7)
      (fun v => ([0, 2, 1, 2, 2, 1, 2] : List ℕ).getD v.val 0)
      (by decide +kernel) (by decide +kernel)
  · decide +kernel

theorem rep_valid_7_47 : (reps 7 47).Connected ∧ (reps 7 47).CliqueFree 3 := by
  constructor
  · exact connected_of_rank (reps 7 47) (0 : Fin 7)
      (fun v => ([0, 1, 1, 2, 1, 2, 3] : List ℕ).getD v.val 0)
      (by decide +kernel) (by decide +kernel)
  · decide +kernel

theorem rep_valid_7_48 : (reps 7 48).Connected ∧ (reps 7 48).CliqueFree 3 := by
  constructor
  · exact connected_of_rank (reps 7 48) (0 : Fin 7)
      (fun v => ([0, 1, 1, 2, 2, 1, 1] : List ℕ).getD v.val 0)
      (by decide +kernel) (by decide +kernel)
  · decide +kernel

theorem rep_valid_7_49 : (reps 7 49).Connected ∧ (reps 7 49).CliqueFree 3 := by
  constructor
  · exact connected_of_rank (reps 7 49) (0 : Fin 7)
      (fun v => ([0, 1, 2, 1, 2, 2, 1] : List ℕ).getD v.val 0)
      (by decide +kernel) (by decide +kernel)
  · decide +kernel

theorem rep_valid_7_50 : (reps 7 50).Connected ∧ (reps 7 50).CliqueFree 3 := by
  constructor
  · exact connected_of_rank (reps 7 50) (0 : Fin 7)
      (fun v => ([0, 1, 2, 1, 1, 2, 2] : List ℕ).getD v.val 0)
      (by decide +kernel) (by decide +kernel)
  · decide +kernel

theorem rep_valid_7_51 : (reps 7 51).Connected ∧ (reps 7 51).CliqueFree 3 := by
  constructor
  · exact connected_of_rank (reps 7 51) (0 : Fin 7)
      (fun v => ([0, 1, 2, 3, 2, 1, 1] : List ℕ).getD v.val 0)
      (by decide +kernel) (by decide +kernel)
  · decide +kernel

theorem rep_valid_7_52 : (reps 7 52).Connected ∧ (reps 7 52).CliqueFree 3 := by
  constructor
  · exact connected_of_rank (reps 7 52) (0 : Fin 7)
      (fun v => ([0, 1, 2, 1, 2, 1, 1] : List ℕ).getD v.val 0)
      (by decide +kernel) (by decide +kernel)
  · decide +kernel

theorem rep_valid_7_53 : (reps 7 53).Connected ∧ (reps 7 53).CliqueFree 3 := by
  constructor
  · exact connected_of_rank (reps 7 53) (0 : Fin 7)
      (fun v => ([0, 2, 1, 1, 1, 1, 1] : List ℕ).getD v.val 0)
      (by decide +kernel) (by decide +kernel)
  · decide +kernel

theorem rep_valid_7_54 : (reps 7 54).Connected ∧ (reps 7 54).CliqueFree 3 := by
  constructor
  · exact connected_of_rank (reps 7 54) (0 : Fin 7)
      (fun v => ([0, 2, 3, 1, 1, 2, 2] : List ℕ).getD v.val 0)
      (by decide +kernel) (by decide +kernel)
  · decide +kernel

theorem rep_valid_7_55 : (reps 7 55).Connected ∧ (reps 7 55).CliqueFree 3 := by
  constructor
  · exact connected_of_rank (reps 7 55) (0 : Fin 7)
      (fun v => ([0, 2, 1, 1, 2, 1, 3] : List ℕ).getD v.val 0)
      (by decide +kernel) (by decide +kernel)
  · decide +kernel

theorem rep_valid_7_56 : (reps 7 56).Connected ∧ (reps 7 56).CliqueFree 3 := by
  constructor
  · exact connected_of_rank (reps 7 56) (0 : Fin 7)
      (fun v => ([0, 1, 2, 2, 2, 1, 1] : List ℕ).getD v.val 0)
      (by decide +kernel) (by decide +kernel)
  · decide +kernel

theorem rep_valid_7_57 : (reps 7 57).Connected ∧ (reps 7 57).CliqueFree 3 := by
  constructor
  · exact connected_of_rank (reps 7 57) (0 : Fin 7)
      (fun v => ([0, 1, 2, 1, 1, 2, 2] : List ℕ).getD v.val 0)
      (by decide +kernel) (by decide +kernel)
  · decide +kernel

theorem rep_valid_7_58 : (reps 7 58).Connected ∧ (reps 7 58).CliqueFree 3 := by
  constructor
  · exact connected_of_rank (reps 7 58) (0 : Fin 7)
      (fun v => ([0, 1, 1, 2, 1, 1, 2] : List ℕ).getD v.val 0)
      (by decide +kernel) (by decide +kernel)
  · decide +kernel

theorem valid_level_7 : ∀ i : Fin (repCount 7),
    (reps 7 i).Connected ∧ (reps 7 i).CliqueFree 3 := by
  intro i
  fin_cases i
  · exact rep_valid_7_00
  · exact rep_valid_7_01
  · exact rep_valid_7_02
  · exact rep_valid_7_03
  · exact rep_valid_7_04
  · exact rep_valid_7_05
  · exact rep_valid_7_06
  · exact rep_valid_7_07
  · exact rep_valid_7_08
  · exact rep_valid_7_09
  · exact rep_valid_7_10
  · exact rep_valid_7_11
  · exact rep_valid_7_12
  · exact rep_valid_7_13
  · exact rep_valid_7_14
  · exact rep_valid_7_15
  · exact rep_valid_7_16
  · exact rep_valid_7_17
  · exact rep_valid_7_18
  · exact rep_valid_7_19
  · exact rep_valid_7_20
  · exact rep_valid_7_21
  · exact rep_valid_7_22
  · exact rep_valid_7_23
  · exact rep_valid_7_24
  · exact rep_valid_7_25
  · exact rep_valid_7_26
  · exact rep_valid_7_27
  · exact rep_valid_7_28
  · exact rep_valid_7_29
  · exact rep_valid_7_30
  · exact rep_valid_7_31
  · exact rep_valid_7_32
  · exact rep_valid_7_33
  · exact rep_valid_7_34
  · exact rep_valid_7_35
  · exact rep_valid_7_36
  · exact rep_valid_7_37
  · exact rep_valid_7_38
  · exact rep_valid_7_39
  · exact rep_valid_7_40
  · exact rep_valid_7_41
  · exact rep_valid_7_42
  · exact rep_valid_7_43
  · exact rep_valid_7_44
  · exact rep_valid_7_45
  · exact rep_valid_7_46
  · exact rep_valid_7_47
  · exact rep_valid_7_48
  · exact rep_valid_7_49
  · exact rep_valid_7_50
  · exact rep_valid_7_51
  · exact rep_valid_7_52
  · exact rep_valid_7_53
  · exact rep_valid_7_54
  · exact rep_valid_7_55
  · exact rep_valid_7_56
  · exact rep_valid_7_57
  · exact rep_valid_7_58

theorem representatives_valid (n : ℕ) (hn : 1 ≤ n) (hn7 : n ≤ 7) :
    ∀ i : Fin (repCount n), (reps n i).Connected ∧ (reps n i).CliqueFree 3 := by
  interval_cases n
  · exact valid_level_1
  · exact valid_level_2
  · exact valid_level_3
  · exact valid_level_4
  · exact valid_level_5
  · exact valid_level_6
  · exact valid_level_7

#print axioms representatives_valid

end CodexPaper4.TriangleFreeEnumerationValidity
