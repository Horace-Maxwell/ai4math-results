import Research.Backfill.Paper3.Proof.Small.Defs

/-!
# Small graphs: kernel counts for Table 4 (core Lean only)

`N_{≤t}` of the edge masks of `H_3`, `2 K_{3,3}`, `3 K_4` (twelve vertices), `2 K_{2,2}` and
`C_8` (eight vertices), evaluated by the kernel (`decide +kernel`).
-/

set_option autoImplicit false

namespace P3Small

theorem nleB_H3 : nleB 12 maskH3 1 = 527 := by decide +kernel

theorem nleB_K23_one : nleB 12 maskK23 1 = 495 := by decide +kernel

theorem nleB_K23_ten : nleB 12 maskK23 10 = 3981 := by decide +kernel

theorem nleB_K34 : nleB 12 maskK34 10 = 4002 := by decide +kernel

theorem nleB_K22 : nleB 8 maskK22 1 = 105 := by decide +kernel

theorem nleB_C8 : nleB 8 maskC8 1 = 111 := by decide +kernel

end P3Small
