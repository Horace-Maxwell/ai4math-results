import Research.TaskH.Seven.SevenTwoColorOwnLeafAbsent

/-! A collection of actual chosen path witnesses. It is constructed from
the original data and an explicit INTERNAL residual upper bound; it is not
an assumption in original CaseSeven or an unexplained path oracle. -/

set_option autoImplicit false
universe u
namespace TaskH.Seven
open SimpleGraph Challenge
open scoped Classical
variable {V : Type u} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]

structure SevenPathSystem {v : V}
    {c : (G.induce {x | x ≠ v}).Coloring (Fin 7)} (F : DegreeTwelveFrame G v c) where
  indices : Finset (Fin 5)
  card_ge_four : 4 ≤ indices.card
  paths : ∀ i : ↥indices, (G.induce {x | x ≠ v}).Walk (F.centerD 0) (F.splitBD i.val)
  path_isPath : ∀ i, (paths i).IsPath
  path_follows : ∀ i, Follows (paths i) c (Equiv.swap (c (F.centerD 0)) (F.pairIndex i.val).val)
  path_minimal : ∀ i, ∀ q : (G.induce {x | x ≠ v}).Walk (F.centerD 0) (F.splitBD i.val),
    Follows q c (Equiv.swap (c (F.centerD 0)) (F.pairIndex i.val).val) → (paths i).length ≤ q.length
  path_length : ∀ i, (paths i).length = 7
  own_leaf_absent : ∀ i, ∀ n ≤ (paths i).length, (paths i).getVert n ≠ F.splitAD i.val

theorem equality_exists_sevenPathSystem
    (hcrit : IsCriticalPlus 7 G) (hc : modCycleCount 7 G = 2880)
    (hnot : ¬ IsCompleteOfOrder G 8) {v : V}
    {c : (G.induce {x | x ≠ v}).Coloring (Fin 7)} (hv : G.degree v = 12)
    (F : DegreeTwelveFrame G v c) (hF : F.IsPureSplit)
    (hsmall : F.residualPool.card ≤ 7) : Nonempty (SevenPathSystem F) := by
  classical
  have hex (i : ↥F.connectedPairSet) := F.connectedPairSet_seven_paths hcrit hc hnot hF i.val i.property
  let p (i : ↥F.connectedPairSet) := Classical.choose (hex i)
  have hp (i : ↥F.connectedPairSet) := Classical.choose_spec (hex i)
  refine ⟨{ indices := F.connectedPairSet
            card_ge_four := F.connectedPairSet_card_ge_four hcrit hc hnot hv hF
            paths := p
            path_isPath := fun i => (hp i).1
            path_follows := fun i => (hp i).2.1
            path_minimal := fun i => (hp i).2.2.1
            path_length := fun i => (hp i).2.2.2
            own_leaf_absent := ?_ }⟩
  intro i
  exact F.shortest_seven_path_own_leaf_absent hcrit hc hnot hF hsmall i.val (p i)
    (hp i).1 (hp i).2.1 (hp i).2.2.1 (hp i).2.2.2

theorem SevenPathSystem.even_color {v : V}
    {c : (G.induce {x | x ≠ v}).Coloring (Fin 7)}
    {F : DegreeTwelveFrame G v c} (P : SevenPathSystem F) (i : ↥P.indices)
    (n : ℕ) (hn : n ≤ 7) (heven : n % 2 = 0) :
    c ((P.paths i).getVert n) = (F.singletonIndex 0).val := by
  have hc := twoColor_color_at (P.paths i) c (F.pairIndex i.val).val
    (P.path_follows i) n (by rw [P.path_length i]; exact hn)
  rw [ite_eq_left heven] at hc
  exact hc.trans (F.center_color 0)

theorem SevenPathSystem.odd_color {v : V}
    {c : (G.induce {x | x ≠ v}).Coloring (Fin 7)}
    {F : DegreeTwelveFrame G v c} (P : SevenPathSystem F) (i : ↥P.indices)
    (n : ℕ) (hn : n ≤ 7) (hodd : n % 2 = 1) :
    c ((P.paths i).getVert n) = (F.pairIndex i.val).val := by
  have hc := twoColor_color_at (P.paths i) c (F.pairIndex i.val).val
    (P.path_follows i) n (by rw [P.path_length i]; exact hn)
  rw [ite_eq_right (by omega : ¬ n % 2 = 0)] at hc
  exact hc

theorem SevenPathSystem.internal_outside {v : V}
    {c : (G.induce {x | x ≠ v}).Coloring (Fin 7)}
    {F : DegreeTwelveFrame G v c} (P : SevenPathSystem F) (i : ↥P.indices)
    (n : ℕ) (hn0 : 0 < n) (hn7 : n < 7) :
    ((P.paths i).getVert n).val ∈ rootOutside G v :=
  F.seven_path_internal_outside_of_own_leaf_absent i.val (P.paths i) (P.path_isPath i)
    (P.path_follows i) (P.path_length i) (P.own_leaf_absent i) n hn0 hn7

theorem SevenPathSystem.middle_residual (hr : RainbowSevenCycles G) {v : V}
    {c : (G.induce {x | x ≠ v}).Coloring (Fin 7)}
    {F : DegreeTwelveFrame G v c} (P : SevenPathSystem F) (hF : F.IsPureSplit) (i : ↥P.indices) :
    ((P.paths i).getVert 3).val ∈ F.residualPool ∧
      ((P.paths i).getVert 4).val ∈ F.residualPool :=
  F.seven_path_middle_residual_of_own_leaf_absent hr hF i.val (P.paths i) (P.path_isPath i)
    (P.path_follows i) (P.path_length i) (P.own_leaf_absent i)

theorem SevenPathSystem.odd_position_injective {v : V}
    {c : (G.induce {x | x ≠ v}).Coloring (Fin 7)}
    {F : DegreeTwelveFrame G v c} (P : SevenPathSystem F)
    (n : ℕ) (hn : n ≤ 7) (hodd : n % 2 = 1) :
    Function.Injective (fun i : ↥P.indices => ((P.paths i).getVert n).val) := by
  intro i j he
  apply Subtype.ext
  apply F.pairColor_injective
  have hh := congrArg c (Subtype.ext he : (P.paths i).getVert n = (P.paths j).getVert n)
  rw [P.odd_color i n hn hodd, P.odd_color j n hn hodd] at hh
  exact hh

end TaskH.Seven
#print axioms TaskH.Seven.SevenPathSystem
#print axioms TaskH.Seven.equality_exists_sevenPathSystem
#print axioms TaskH.Seven.SevenPathSystem.even_color
#print axioms TaskH.Seven.SevenPathSystem.odd_color
#print axioms TaskH.Seven.SevenPathSystem.internal_outside
#print axioms TaskH.Seven.SevenPathSystem.middle_residual
#print axioms TaskH.Seven.SevenPathSystem.odd_position_injective
