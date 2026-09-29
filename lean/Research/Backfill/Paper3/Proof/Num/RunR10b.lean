import Research.Backfill.Paper3.Proof.Num.Data

/-!
# Kernel run for Remark 10(b)

`d = 2`, `m = 100` (`n = 400`), `γ = 1/4`, threshold `200`: with `a` and `g` the prefix sums up to
`200` of `P_2^{100}` and `P_{H_2}^{50}` (truncation at degree `201`), the kernel checks
`(10^19 + 125) a ≤ 10^19 g < (10^19 + 135) a`.
-/

set_option autoImplicit false

namespace P3Num

/-- The two inequalities of Remark 10(b), cleared of denominators. -/
def r10bOK : Bool :=
  let s := runSt K2 H2 201 (fun _ => []) 100
  and (Nat.ble ((10 ^ 19 + 125) * sumL (takeL 201 s.A)) (10 ^ 19 * sumL (takeL 201 s.B)))
    (Nat.blt (10 ^ 19 * sumL (takeL 201 s.B)) ((10 ^ 19 + 135) * sumL (takeL 201 s.A)))

theorem run_R10b : r10bOK = true := by
  decide +kernel

end P3Num
