import Research.Backfill.Paper3.Proof.Num.Data

/-!
# Kernel run for the Theorem D numerics, `d = 3`

Queries (threshold `⌊γ d · 2dm⌋`, expected code; `0`: `G_n` wins, `2`: it loses): `m = 16`
(`n = 96`), `γ = 9/20` (wins); `m = 24` (`n = 144`), `γ = 9/20` (loses); `m = 32` (`n = 192`),
`γ = 1/5, 1/4, 1/3, 2/5, 9/20` (wins) and `γ = 3/20` (loses); every even `m ∈ [56, 100]`
(`n ∈ [336, 600]`, `12 ∣ n`), `γ = 3/20` (wins). Truncation at degree `271`.
-/

set_option autoImplicit false

namespace P3Num

def qTD3 (m : ℕ) : List (ℕ × ℕ) :=
  cond (Nat.beq m 16) [(129, 0)]
    (cond (Nat.beq m 24) [(194, 2)]
      (cond (Nat.beq m 32) [(115, 0), (144, 0), (192, 0), (230, 0), (259, 0), (86, 2)]
        (cond (and (Nat.ble 56 m) (Nat.beq (Nat.mod m 2) 0)) [(3 * 3 * (2 * 3 * m) / 20, 0)] [])))

theorem run_TD3 : (runSt K3 H3 271 qTD3 100).ok = true := by
  decide +kernel

end P3Num
