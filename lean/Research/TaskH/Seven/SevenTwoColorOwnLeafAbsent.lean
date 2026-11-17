import Research.TaskH.Seven.SevenTwoColorSevenResidual

/-! Actual drop/copy transport: an occurrence of the own leaf on a shortest
seven-edge path occurs at position1. Dropping its actual first edge gives
the forbidden genuine six-edge path, with its colors and avoidance proved. -/

set_option autoImplicit false
universe u
namespace TaskH.Seven
open SimpleGraph Challenge
open scoped Classical
variable {V : Type u} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem DegreeTwelveFrame.shortest_seven_path_own_leaf_absent
    (hcrit : IsCriticalPlus 7 G) (hc : modCycleCount 7 G = 2880)
    (hnot : ¬ IsCompleteOfOrder G 8) {v : V}
    {c : (G.induce {x | x ≠ v}).Coloring (Fin 7)}
    (F : DegreeTwelveFrame G v c) (hF : F.IsPureSplit)
    (hsmall : F.residualPool.card ≤ 7) (i : Fin 5)
    (p : (G.induce {x | x ≠ v}).Walk (F.centerD 0) (F.splitBD i))
    (hp : p.IsPath)
    (hf : Follows p c (Equiv.swap (c (F.centerD 0)) (F.pairIndex i).val))
    (hmin : ∀ q : (G.induce {x | x ≠ v}).Walk (F.centerD 0) (F.splitBD i),
      Follows q c (Equiv.swap (c (F.centerD 0)) (F.pairIndex i).val) → p.length ≤ q.length)
    (hl : p.length = 7) : ∀ n ≤ p.length, p.getVert n ≠ F.splitAD i := by
  intro n hn hpoint
  have hca : c (F.centerD 0) = (F.singletonIndex 0).val := F.center_color 0
  have hpi : c (F.splitAD i) = (F.pairIndex i).val := F.splitA_color i
  have hbeta : (F.pairIndex i).val ≠ c (F.centerD 0) := by
    rw [hca]
    exact F.pairColor_ne_singleton i 0
  have hcolor : c (p.getVert n) = (F.pairIndex i).val := by rw [hpoint, hpi]
  have hedge : (G.induce {x | x ≠ v}).Adj (F.centerD 0) (p.getVert n) := by
    rw [hpoint]
    exact (F.splitAB_adjacencies i (hF i)).1
  have hn1 := twoColor_shortest_neighbor_at_start p c (F.pairIndex i).val hbeta
    hf hmin n hn hcolor hedge
  have hfirst : p.getVert 1 = F.splitAD i := by simpa only [hn1] using hpoint
  let q : (G.induce {x | x ≠ v}).Walk (F.splitAD i) (F.splitBD i) :=
    (p.drop 1).copy hfirst rfl
  have hq : q.IsPath := (Walk.isPath_copy _ _ _).mpr (hp.drop 1)
  have hperm : Equiv.swap (c (F.splitAD i)) (F.singletonIndex 0).val =
      Equiv.swap (c (F.centerD 0)) (F.pairIndex i).val := by
    rw [hpi, hca]
    exact Equiv.swap_comm _ _
  have hqf : Follows q c (Equiv.swap (c (F.splitAD i)) (F.singletonIndex 0).val) := by
    intro d hd
    change d ∈ ((p.drop 1).copy hfirst rfl).darts at hd
    rw [Walk.darts_copy] at hd
    rw [hperm]
    exact twoColor_follows_drop p c _ hf 1 d hd
  have hql : q.length = 6 := by simp [q, Walk.drop_length, hl]
  have hqavoid : ∀ k ≤ q.length, q.getVert k ≠ F.centerD 0 := by
    intro k hk he
    have hpstart : p.getVert (1 + k) = F.centerD 0 := by
      simpa only [q, Walk.getVert_copy, Walk.drop_getVert] using he
    have hn0 := (hp.getVert_eq_start_iff (by omega : 1 + k ≤ p.length)).mp hpstart
    omega
  exact equality_six_path_false_of_residual_card hcrit hc hnot F hF hsmall i q hq hqf hql hqavoid

end TaskH.Seven
#print axioms TaskH.Seven.DegreeTwelveFrame.shortest_seven_path_own_leaf_absent
