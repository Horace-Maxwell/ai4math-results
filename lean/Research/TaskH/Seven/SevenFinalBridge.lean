import Research.TaskH.Seven.SevenOrder45
import Research.TaskH.Seven.SevenK5Free
import Research.TaskH.Seven.SevenMaximumCut
import Research.TaskH.Seven.SevenBP45
import Research.TaskH.Seven.SevenLowerBound

/-! The final original-graph transport once the separately owed minimum
degree13 theorem is available. This internal helper does not assert that
minimum degree13 has already been derived from the original hypotheses. -/

set_option autoImplicit false

universe u

namespace TaskH.Seven

open SimpleGraph _root_.TaskH.Challenge

variable {V : Type u} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem equality_complete_of_min_degree_thirteen (hcrit : IsCriticalPlus 7 G)
    (hc : modCycleCount 7 G = 2880) (hd : ∀ v : V, 13 ≤ G.degree v) :
    IsCompleteOfOrder G 8 := by
  have hdec :
      (inferInstance : DecidableRel G.Adj) =
        (fun a b => Classical.propDecidable (G.Adj a b)) := by
    funext a b
    exact Subsingleton.elim _ _
  cases hdec
  classical
  let : Nonempty V := critical_nonempty hcrit
  by_contra hnot
  have hfree := equality_cliqueFree_five hcrit hc hnot
  have hn45 := equality_card_le_forty_five_of_cliqueFree_five hcrit hc hfree
  obtain ⟨B, hle, hb, hBdegree⟩ := exists_bipartite_subgraph_min_degree_seven G hd
  obtain ⟨a, p, hp, hlen⟩ :=
    BP.bipartite_card_le_forty_five_exists_fourteen hb hn45 hBdegree
  have hpc : (p.mapLe hle).IsCycle := (Walk.isCycle_mapLe hle).mpr hp
  have hlenG : (p.mapLe hle).length = 14 := (Walk.length_mapLe hle p).trans hlen
  have hs : ShortSevenCycles G := equality_shortSevenCycles hcrit hc
  have hseven : (p.mapLe hle).length = 7 :=
    hs (p.mapLe hle) hpc (by rw [hlenG]; decide)
  omega

end TaskH.Seven

#print axioms TaskH.Seven.equality_complete_of_min_degree_thirteen
