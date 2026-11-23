import Research.TaskV.Illumination.Challenge
import Mathlib.Analysis.Convex.Combination
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FunProp

namespace PrismIllumination

theorem gapSix {K : Set Space} (_hP : prism ⊆ K) (hQ : K ⊆ cube)
    (hc : IsCompact K) (hd : Disjoint K edge) :
    ∃ r : ℝ, 0 < r ∧ ∀ p ∈ K, r ≤ max (1 - p 0) (1 - p 1) := by
  apply hc.exists_forall_le' (by fun_prop)
  intro p hp
  by_contra! h
  obtain ⟨hx, hy⟩ := max_le_iff.mp h
  have hcube := hQ hp
  exact Set.disjoint_left.mp hd hp ⟨hcube, by linarith [(hcube 0).2],
    by linarith [(hcube 1).2]⟩

private theorem cubeFromCorners {K : Set Space} (hP : prism ⊆ K)
    (hQ : K ⊆ cube) (hv : Convex ℝ K) {l u : Space}
    (hl : l ∈ K) (hu : u ∈ K) (lx : l 0 = 1) (ly : l 1 = 1) (lz : l 2 = 0)
    (ux : u 0 = 1) (uy : u 1 = 1) (uz : u 2 = 1) : K = cube := by
  apply Set.Subset.antisymm hQ
  let vertices := Set.univ.pi (fun _ : Fin 3 => ({0, 1} : Set ℝ))
  have hverts : vertices ⊆ K := by
    intro p hp
    have bits (i : Fin 3) : p i = 0 ∨ p i = 1 := by
      simpa using hp i (Set.mem_univ i)
    have hpQ : p ∈ cube := by
      intro i
      rcases bits i with h | h <;> simp [h]
    by_cases hx : p 0 = 0
    · exact hP ⟨hpQ, by simpa [hx] using (hpQ 1).2⟩
    by_cases hy : p 1 = 0
    · exact hP ⟨hpQ, by simpa [hy] using (hpQ 0).2⟩
    have hx' := (bits 0).resolve_left hx
    have hy' := (bits 1).resolve_left hy
    rcases bits 2 with hz | hz
    · have heq : p = l := by
        funext i
        fin_cases i <;> simp_all
      exact heq ▸ hl
    · have heq : p = u := by
        funext i
        fin_cases i <;> simp_all
      exact heq ▸ hu
  intro p hp
  apply (convexHull_min hverts hv)
  apply mem_convexHull_pi
  intro i _
  rw [convexHull_pair, segment_eq_Icc (zero_le_one : (0 : ℝ) ≤ 1)]
  exact hp i

private def depth (b : Bool) (p : Space) :=
  max (max (1 - p 0) (1 - p 1)) (if b then 1 - p 2 else p 2)

theorem gapSeven {K : Set Space} (hP : prism ⊆ K) (hQ : K ⊆ cube)
    (hc : IsCompact K) (hv : Convex ℝ K) (hne : K ≠ cube) :
    ∃ b : Bool, ∃ r : ℝ, 0 < r ∧ ∀ p ∈ K,
      r ≤ max (max (1 - p 0) (1 - p 1)) (if b then 1 - p 2 else p 2) := by
  have hgood : ∃ b, ∀ p ∈ K, 0 < depth b p := by
    by_contra! h
    obtain ⟨l, hl, hlow⟩ := h false
    obtain ⟨u, hu, hupp⟩ := h true
    simp only [depth, Bool.false_eq_true, ↓reduceIte, max_le_iff] at hlow
    simp only [depth, ↓reduceIte, max_le_iff] at hupp
    obtain ⟨⟨lx, ly⟩, lz⟩ := hlow
    obtain ⟨⟨ux, uy⟩, uz⟩ := hupp
    have hL := hQ hl
    have hU := hQ hu
    apply hne (cubeFromCorners hP hQ hv hl hu ?_ ?_ ?_ ?_ ?_ ?_)
    all_goals linarith [(hL 0).2, (hL 1).2, (hL 2).1, (hU 0).2, (hU 1).2, (hU 2).2]
  obtain ⟨b, hb⟩ := hgood
  refine ⟨b, ?_⟩
  apply hc.exists_forall_le' (f := depth b) _ hb
  cases b <;> unfold depth <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> fun_prop

end PrismIllumination
