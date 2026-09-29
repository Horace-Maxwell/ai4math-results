import Research.Backfill.Paper3.Proof.Num.Data

/-!
# Kernel run for the Theorem D numerics, `d = 2`

Queries (threshold `⌊γ d · 2dm⌋`, expected code; `0`: `G_n` wins, `2`: it loses): at `m = 48`
(`n = 192`) for `γ = 1/5, 1/4, 1/3, 2/5, 9/20` (wins) and `γ = 3/20` (loses); at every even
`m ∈ [90, 150]` (`n ∈ [360, 600]`, `8 ∣ n`) for `γ = 3/20` (wins). Truncation at degree `181`.
-/

set_option autoImplicit false

namespace P3Num

def qTD2 (m : ℕ) : List (ℕ × ℕ) :=
  cond (Nat.beq m 48) [(76, 0), (96, 0), (128, 0), (153, 0), (172, 0), (57, 2)]
    (cond (and (Nat.ble 90 m) (Nat.beq (Nat.mod m 2) 0)) [(3 * 2 * (2 * 2 * m) / 20, 0)] [])

theorem run_TD2 : (runSt K2 H2 181 qTD2 150).ok = true := by
  decide +kernel

end P3Num
