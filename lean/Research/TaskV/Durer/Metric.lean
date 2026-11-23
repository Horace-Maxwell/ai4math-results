import Research.TaskV.Durer.Challenge
import Mathlib.Tactic.LinearCombination

namespace DurerDV

theorem metric (s : Solid) (u v : ℝ → ℝ)
    (hu : arcValid s s.upper u) (hv : arcValid s s.lower v)
    (k : Chart) (p q : V3) (hp : onChart s k p) (hq : onChart s k q)
    (hf : commonFacet s k p q) :
    sq2 (flat s u v k p) (flat s u v k q) = sq3 (embed s p) (embed s q) := by
  have hbase : 0 ≤ 1-s.c^2 := by
    nlinarith [mul_nonneg (le_of_lt (show 0 < 1+s.c by linarith [s.c_min]))
      (show 0 ≤ 1-s.c by linarith [s.c_max])]
  have hsq := Real.sq_sqrt hbase
  have hgram : sq3 (embed s p) (embed s q) =
      (p.x-q.x)^2 + 2*s.c*(p.x-q.x)*(p.y-q.y) + (p.y-q.y)^2 + (p.z-q.z)^2 := by
    unfold sq3 embed
    dsimp
    linear_combination (p.y-q.y)^2 * hsq
  rw [hgram]
  rcases hp with ⟨⟨px, px', py, py', _, _⟩, hp⟩
  rcases hq with ⟨⟨qx, qx', qy, qy', _, _⟩, hq⟩
  cases k with
  | a | b | c | d =>
    dsimp at hp hq
    simp only [sq2, flat, hp, hq, sub_self]
    ring
  | roof =>
    obtain ⟨i, hip, hiq⟩ := hf
    have hdiff := hu.2.2 i p.x q.x hip hiq
    have h1 := (s.upper.exposed i hip.1 p.x px px').2 hip.2
    have h2 := (s.upper.exposed i hiq.1 q.x qx qx').2 hiq.2
    have hdz : p.z-q.z = s.upper.slope i*(p.x-q.x) := by
      dsimp at hp hq
      linarith only [hp, hq, h1, h2]
    have hk := Real.sq_sqrt (show 0 ≤ 1+s.upper.slope i^2-s.c^2 by
      linarith [sq_nonneg (s.upper.slope i)])
    have hy : s.upper.value 0+u p.x-(s.upper.value 0+u q.x) = u p.x-u q.x := by ring
    simp only [sq2, flat, hy, hdiff, hdz]
    linear_combination (p.x-q.x)^2 * hk
  | floor =>
    obtain ⟨i, hip, hiq⟩ := hf
    have hdiff := hv.2.2 i p.y q.y hip hiq
    have h1 := (s.lower.exposed i hip.1 p.y py py').2 hip.2
    have h2 := (s.lower.exposed i hiq.1 q.y qy qy').2 hiq.2
    have hdz : p.z-q.z = -(s.lower.slope i*(p.y-q.y)) := by
      dsimp at hp hq
      linarith only [hp, hq, h1, h2]
    have hk := Real.sq_sqrt (show 0 ≤ 1+s.lower.slope i^2-s.c^2 by
      linarith [sq_nonneg (s.lower.slope i)])
    have hy : -s.lower.value 0-v p.y-(-s.lower.value 0-v q.y) =
        -(v p.y-v q.y) := by ring
    simp only [sq2, flat, hy, hdiff, hdz]
    linear_combination (p.y-q.y)^2 * hk

end DurerDV
