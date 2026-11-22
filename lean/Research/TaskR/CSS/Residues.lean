import Research.TaskR.CSS.Challenge

namespace TaskR.CSS.Residues

open TaskR.CSS.Challenge

def score (a b c d k : ℤ) : ℤ :=
  (a + 2*k) % 6 + (b+k) % 6 + (c+k) % 6 + (d+k) % 6

set_option maxRecDepth 30000 in
set_option maxHeartbeats 4000000 in
private theorem box : ∀ (a b c d : Fin 6), ∃ k : Fin 6,
    score a.val b.val c.val d.val k.val ≤ 8 := by decide +kernel

theorem upper (a b c d : ℤ) : ∃ k : ℤ, score a b c d k ≤ 8 := by
  let red (z : ℤ) : Fin 6 := ⟨(z % 6).toNat, by omega⟩
  have hred (z : ℤ) : ((red z).val : ℤ) = z % 6 := by dsimp [red]; omega
  obtain ⟨k,hk⟩ := box (red a) (red b) (red c) (red d)
  use k.val
  simpa only [score, hred, Int.emod_add_emod] using hk

theorem lower (k : ℤ) : 8 ≤ score 1 1 2 4 k := by
  have h : 0 ≤ k%6 ∧ k%6 < 6 := ⟨Int.emod_nonneg _ (by decide), Int.emod_lt_of_pos _ (by decide)⟩
  unfold score
  omega

end TaskR.CSS.Residues
