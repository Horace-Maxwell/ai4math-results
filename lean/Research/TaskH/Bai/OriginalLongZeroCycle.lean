import Research.TaskH.Bai.LongZeroArithmetic
import Research.TaskH.Bai.TerminalCycleProgression
import Research.TaskH.Bai.SpanningMaximumCut
import Research.TaskH.Gao.OriginalRootedPathAssembly
set_option autoImplicit false
universe u
namespace TaskH.Bai
open SimpleGraph TaskH.Gao
variable {V : Type u}

/-- Explicit conditional transport; the actual final wrapper below supplies E1 internally. -/
theorem long_zero_cycle_from_original_E1 [Fintype V] [Nonempty V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (E1 : RootedPathClaim.{u})
    (k : ℕ) (hk : 4 ≤ k) (hG : G.Connected)
    (hdeg : ∀ v : V, 2 * k - 1 ≤ G.degree v) :
    ∃ (z : V) (p : G.Walk z z), p.IsCycle ∧ k ∣ p.length ∧ k < p.length := by
  classical
  by_cases hke : k % 2 = 0
  · obtain ⟨c, hle, hbi, hcutdeg, hconn⟩ :=
      exists_spanning_bipartite_minimum_degree G k (by omega) hdeg
    obtain ⟨A, d, z, f, hA, hd, hf⟩ := original_terminal_cycle_progression
      (spanningCut G c) E1 k (k - 1) (by omega) (by omega) (by omega) (hconn hG) hcutdeg
    let i0 : Fin (k - 1) := ⟨0, by omega⟩
    let i1 : Fin (k - 1) := ⟨1, by omega⟩
    have he0 := bipartite_closed_walk_even hbi (f i0)
    have he1 := bipartite_closed_walk_even hbi (f i1)
    rw [(hf i0).2] at he0
    rw [(hf i1).2] at he1
    have hAe : A % 2 = 0 := by simpa only [i0, Nat.zero_mul, Nat.add_zero] using he0
    have hde : d = 2 := by
      rcases hd with hd | hd
      · subst d
        simp only [i1, Nat.one_mul] at he1
        omega
      · exact hd
    subst d
    obtain ⟨i, hi, hdiv, hlong⟩ := even_ap_long_zero k A hk hke hA hAe
    let ii : Fin (k - 1) := ⟨i, hi⟩
    refine ⟨z, (f ii).mapLe hle, (hf ii).1.mapLe hle, ?_, ?_⟩
    · rw [Walk.length_mapLe, (hf ii).2]
      exact hdiv
    · rw [Walk.length_mapLe, (hf ii).2]
      exact hlong
  · have hko : k % 2 = 1 := by omega
    obtain ⟨A, d, z, f, hA, hd, hf⟩ := original_terminal_cycle_progression
      G E1 (2 * k - 1) (2 * k - 2) (by omega) (by omega) (by omega) hG hdeg
    obtain ⟨i, hi, hdiv, hlong⟩ := odd_ap_long_zero k A d hk hko hA hd
    let ii : Fin (2 * k - 2) := ⟨i, hi⟩
    refine ⟨z, f ii, (hf ii).1, ?_, ?_⟩
    · rw [(hf ii).2]
      exact hdiv
    · rw [(hf ii).2]
      exact hlong

/-- Original-only endpoint: no E1/maxcut/block/path-family oracle appears as a hypothesis. -/
theorem connected_high_degree_original_long_zero_cycle [Fintype V] [Nonempty V]
    [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (k : ℕ) (hk : 4 ≤ k) (hG : G.Connected)
    (hdeg : ∀ v : V, 2 * k - 1 ≤ G.degree v) :
    ∃ (z : V) (p : G.Walk z z), p.IsCycle ∧ k ∣ p.length ∧ k < p.length := by
  exact long_zero_cycle_from_original_E1 G gao_original_rooted_path_claim k hk hG hdeg

#print axioms long_zero_cycle_from_original_E1
#print axioms connected_high_degree_original_long_zero_cycle
end TaskH.Bai
