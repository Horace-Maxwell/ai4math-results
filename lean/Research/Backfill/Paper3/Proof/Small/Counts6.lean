import Research.Backfill.Paper3.Proof.Small.Defs

/-!
# Small graphs: kernel counts on six vertices (core Lean only)

The two rows of Table 1 (`N_{≤t}` of `K_{3,3}` and of the prism for `t = 0, …, 9`), and the
comparison `N_{≤t}(prism) ≤ N_{≤t}(K_{3,3})` for `t ≤ 9`, `t ≠ 1`, on the edge masks
`k33Mask`, `prismMask`; evaluated by the kernel (`decide +kernel`).
-/

set_option autoImplicit false

namespace P3Small

theorem table1_k33 : (List.range 10).map (fun t => nleB 6 k33Mask t) =
    [15, 24, 42, 48, 57, 57, 63, 63, 63, 64] := by decide +kernel

theorem table1_prism : (List.range 10).map (fun t => nleB 6 prismMask t) =
    [13, 28, 40, 48, 57, 57, 63, 63, 63, 64] := by decide +kernel

theorem nleB_k33_one : nleB 6 k33Mask 1 = 24 := by decide +kernel

theorem nleB_prism_one : nleB 6 prismMask 1 = 28 := by decide +kernel

theorem nleB_k33_nine : nleB 6 k33Mask 9 = 64 := by decide +kernel

/-- `N_{≤t}(prism) ≤ N_{≤t}(K_{3,3})` for `t < 10`, `t ≠ 1`. -/
theorem prism_le_k33_small :
    nall 10 (fun t => Nat.beq t 1 || Nat.ble (nleB 6 prismMask t) (nleB 6 k33Mask t)) = true := by
  decide +kernel

end P3Small
