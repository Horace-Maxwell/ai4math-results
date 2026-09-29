import Research.Backfill.Paper3.Proof.Num.Bridge

/-!
# Coefficient lists of `P_d` and `P_{H_d}` for `d = 2, 3, 4`

`P_d = toPoly (pdList d)` is evaluated to an explicit list, and the explicit list of `P_{H_d}`
(any choice of the switched edges) is justified by the rearranged Lemma 6 identity, checked on
lists by the kernel.
-/

set_option autoImplicit false

namespace P3Num

open BackfillPaper3.Challenge

def K2 : List ℕ := [7, 4, 4, 0, 1]

def H2 : List ℕ := [47, 64, 60, 40, 28, 8, 8, 0, 1]

def K3 : List ℕ := [15, 9, 18, 6, 9, 0, 6, 0, 0, 1]

def H3 : List ℕ :=
  [207, 320, 569, 556, 622, 466, 472, 260, 267, 124, 118, 36, 48, 18, 0, 12, 0, 0, 1]

def K4 : List ℕ := [31, 16, 48, 32, 44, 0, 48, 0, 12, 16, 0, 0, 8, 0, 0, 0, 1]

def H4 : List ℕ :=
  [863, 1192, 3052, 3800, 5566, 5260, 7148, 5410, 6520, 4966, 5316, 3012, 4228, 2088, 1812, 1978,
    920, 542, 976, 136, 262, 256, 96, 0, 88, 32, 0, 0, 16, 0, 0, 0, 1]

theorem pdList_two : pdList 2 = K2 := by decide +kernel

theorem pdList_three : pdList 3 = K3 := by decide +kernel

theorem pdList_four : pdList 4 = K4 := by decide +kernel

theorem hId_two : hLhs 2 H2 = hRhs 2 := by decide +kernel

theorem hId_three : hLhs 3 H3 = hRhs 3 := by decide +kernel

theorem hId_four : hLhs 4 H4 = hRhs 4 := by decide +kernel

theorem Pd_two : Pd 2 = toPoly K2 := by rw [Pd_eq_toPoly, pdList_two]

theorem Pd_three : Pd 3 = toPoly K3 := by rw [Pd_eq_toPoly, pdList_three]

theorem Pd_four : Pd 4 = toPoly K4 := by rw [Pd_eq_toPoly, pdList_four]

theorem edgePoly_H2 (a₁ b₁ a₂ b₂ : Fin 2) : edgePoly (Hd 2 a₁ b₁ a₂ b₂) = toPoly H2 :=
  edgePoly_Hd_eq 2 le_rfl H2 hId_two a₁ b₁ a₂ b₂

theorem edgePoly_H3 (a₁ b₁ a₂ b₂ : Fin 3) : edgePoly (Hd 3 a₁ b₁ a₂ b₂) = toPoly H3 :=
  edgePoly_Hd_eq 3 (by norm_num) H3 hId_three a₁ b₁ a₂ b₂

theorem edgePoly_H4 (a₁ b₁ a₂ b₂ : Fin 4) : edgePoly (Hd 4 a₁ b₁ a₂ b₂) = toPoly H4 :=
  edgePoly_Hd_eq 4 (by norm_num) H4 hId_four a₁ b₁ a₂ b₂

end P3Num
