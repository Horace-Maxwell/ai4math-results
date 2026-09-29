import Research.Backfill.Paper3.Proof.Num.Data

/-!
# Kernel run for the Theorem D numerics, `d = 4`

Queries (threshold `⌊γ d · 2dm⌋`, expected code; `0`: `G_n` wins, `2`: it loses): `m = 16`
(`n = 128`), `γ = 9/20` (loses); `m = 24` (`n = 192`), `γ = 1/5, 1/4, 1/3, 2/5, 9/20` (wins) and
`γ = 3/20` (loses); `m = 26` (`n = 208`), `γ = 9/20` (loses); every even `m ∈ [40, 74]`
(`n ∈ [320, 592]`, `16 ∣ n`), `γ = 3/20` (wins). Truncation at degree `375`.
-/

set_option autoImplicit false

namespace P3Num

def qTD4 (m : ℕ) : List (ℕ × ℕ) :=
  cond (Nat.beq m 16) [(230, 2)]
    (cond (Nat.beq m 24) [(153, 0), (192, 0), (256, 0), (307, 0), (345, 0), (115, 2)]
      (cond (Nat.beq m 26) [(374, 2)]
        (cond (and (Nat.ble 40 m) (Nat.beq (Nat.mod m 2) 0)) [(3 * 4 * (2 * 4 * m) / 20, 0)] [])))

theorem run_TD4 : (runSt K4 H4 375 qTD4 74).ok = true := by
  decide +kernel

end P3Num
