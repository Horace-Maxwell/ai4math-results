import Research.Backfill.Paper3.Proof.Num.Data

/-!
# Kernel run for Remark 12, `d = 3`

At `γ = 1/10`, `d = 3`: for `m = 1, …, 120` the prefix sums up to `⌊γ d · 2dm⌋` of `P_3^m` and
`P_{H_3}^{⌊m/2⌋} P_3^{m mod 2}` compare as recorded in `codes3` (`0`: `G_n` wins, `2`: it loses,
`1`: tie). Checked by `decide +kernel` (truncation at degree `217`).
-/

set_option autoImplicit false

namespace P3Num

/-- The comparison codes for `d = 3`, `γ = 1/10`, indexed by `m = 0, …, 120`. -/
def codes3 : List ℕ :=
  [1, 1, 0, 0, 0, 0, 2, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 2, 2,
    2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2,
    2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]

/-- One query per `m`: threshold `⌊(1/10) · 3 · 6m⌋` and the expected code. -/
def qR12b (m : ℕ) : List (ℕ × ℕ) :=
  [(1 * 3 * (2 * 3 * m) / 10, nthL codes3 m)]

theorem run_R12b : (runSt K3 H3 217 qR12b 120).ok = true := by
  decide +kernel

end P3Num
