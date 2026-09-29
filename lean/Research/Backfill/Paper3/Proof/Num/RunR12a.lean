import Research.Backfill.Paper3.Proof.Num.Data

/-!
# Kernel run for Remark 12, `d = 2`

At `γ = 1/10`, `d = 2`: for `m = 1, …, 120` the prefix sums up to `⌊γ d · 2dm⌋` of `P_2^m` and
`P_{H_2}^{⌊m/2⌋} P_2^{m mod 2}` compare as recorded in `codes2` (`0`: `G_n` wins, `2`: it loses,
`1`: tie). Checked by `decide +kernel` (truncation at degree `97`).
-/

set_option autoImplicit false

namespace P3Num

/-- The comparison codes for `d = 2`, `γ = 1/10`, indexed by `m = 0, …, 120`. -/
def codes2 : List ℕ :=
  [1, 1, 0, 2, 0, 2, 2, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    2, 2, 2, 0, 0, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]

/-- One query per `m`: threshold `⌊(1/10) · 2 · 4m⌋` and the expected code. -/
def qR12a (m : ℕ) : List (ℕ × ℕ) :=
  [(1 * 2 * (2 * 2 * m) / 10, nthL codes2 m)]

theorem run_R12a : (runSt K2 H2 97 qR12a 120).ok = true := by
  decide +kernel

end P3Num
