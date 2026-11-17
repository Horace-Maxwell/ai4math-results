import Research.TaskH.Seven.SevenCommonRepresentativeColors

/-! Actual oriented representatives of each noncommon two-point fiber.
The orientation is derived from the original first-step coverage. -/

set_option autoImplicit false
universe u
namespace TaskH.Seven
open SimpleGraph _root_.TaskH.Challenge
open scoped Classical
variable {V : Type u} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]

def DegreeTwelveFrame.IsSplitPair {v : V}
    {c : (G.induce {x | x ≠ v}).Coloring (Fin 7)}
    (F : DegreeTwelveFrame G v c) (i : Fin 5) : Prop :=
  (G.Adj (F.center 0).val (F.leaf i 0).val ∧
    ¬ G.Adj (F.center 1).val (F.leaf i 0).val ∧
    G.Adj (F.center 1).val (F.leaf i 1).val ∧
    ¬ G.Adj (F.center 0).val (F.leaf i 1).val) ∨
  (G.Adj (F.center 0).val (F.leaf i 1).val ∧
    ¬ G.Adj (F.center 1).val (F.leaf i 1).val ∧
    G.Adj (F.center 1).val (F.leaf i 0).val ∧
    ¬ G.Adj (F.center 0).val (F.leaf i 0).val)

theorem DegreeTwelveFrame.splitPair_of_not_common
    (hcrit : IsCriticalPlus 7 G) (hc : modCycleCount 7 G = 2880)
    (hnot : ¬ IsCompleteOfOrder G 8) {v : V}
    {c : (G.induce {x | x ≠ v}).Coloring (Fin 7)} (hv : G.degree v = 12)
    (F : DegreeTwelveFrame G v c) (i : Fin 5) (hi : i ∉ F.commonColors) :
    F.IsSplitPair i := by
  have hno : ¬ ∃ e : Fin 2,
      G.Adj (F.center 0).val (F.leaf i e).val ∧
      G.Adj (F.center 1).val (F.leaf i e).val := by
    intro he
    exact hi (Finset.mem_filter.mpr ⟨Finset.mem_univ i, he⟩)
  obtain ⟨e, hae⟩ := F.center_meets_pair hcrit hc hnot hv 0 i
  obtain ⟨d, hbd⟩ := F.center_meets_pair hcrit hc hnot hv 1 i
  have hed : e ≠ d := by
    intro he
    subst d
    exact hno ⟨e, hae, hbd⟩
  have hbe : ¬ G.Adj (F.center 1).val (F.leaf i e).val := fun he => hno ⟨e, hae, he⟩
  have had : ¬ G.Adj (F.center 0).val (F.leaf i d).val := fun he => hno ⟨d, he, hbd⟩
  fin_cases e <;> fin_cases d <;> simp_all [DegreeTwelveFrame.IsSplitPair]

noncomputable def DegreeTwelveFrame.splitA {v : V}
    {c : (G.induce {x | x ≠ v}).Coloring (Fin 7)}
    (F : DegreeTwelveFrame G v c) (i : Fin 5) : G.neighborSet v :=
  if G.Adj (F.center 0).val (F.leaf i 0).val then F.leaf i 0 else F.leaf i 1

noncomputable def DegreeTwelveFrame.splitB {v : V}
    {c : (G.induce {x | x ≠ v}).Coloring (Fin 7)}
    (F : DegreeTwelveFrame G v c) (i : Fin 5) : G.neighborSet v :=
  if G.Adj (F.center 0).val (F.leaf i 0).val then F.leaf i 1 else F.leaf i 0

theorem DegreeTwelveFrame.splitA_color {v : V}
    {c : (G.induce {x | x ≠ v}).Coloring (Fin 7)}
    (F : DegreeTwelveFrame G v c) (i : Fin 5) :
    neighborColor v c (F.splitA i) = (F.pairIndex i).val := by
  unfold DegreeTwelveFrame.splitA
  split_ifs <;> exact F.leaf_color i _

theorem DegreeTwelveFrame.splitB_color {v : V}
    {c : (G.induce {x | x ≠ v}).Coloring (Fin 7)}
    (F : DegreeTwelveFrame G v c) (i : Fin 5) :
    neighborColor v c (F.splitB i) = (F.pairIndex i).val := by
  unfold DegreeTwelveFrame.splitB
  split_ifs <;> exact F.leaf_color i _

theorem DegreeTwelveFrame.splitAB_ne {v : V}
    {c : (G.induce {x | x ≠ v}).Coloring (Fin 7)}
    (F : DegreeTwelveFrame G v c) (i : Fin 5) :
    (F.splitA i).val ≠ (F.splitB i).val := by
  unfold DegreeTwelveFrame.splitA DegreeTwelveFrame.splitB
  split_ifs
  · exact (F.leaf_same_pair_injective i).ne (by decide : (0 : Fin 2) ≠ 1)
  · exact (F.leaf_same_pair_injective i).ne (by decide : (1 : Fin 2) ≠ 0)

theorem DegreeTwelveFrame.splitAB_adjacencies {v : V}
    {c : (G.induce {x | x ≠ v}).Coloring (Fin 7)}
    (F : DegreeTwelveFrame G v c) (i : Fin 5) (hi : F.IsSplitPair i) :
    G.Adj (F.center 0).val (F.splitA i).val ∧
      ¬ G.Adj (F.center 1).val (F.splitA i).val ∧
      G.Adj (F.center 1).val (F.splitB i).val ∧
      ¬ G.Adj (F.center 0).val (F.splitB i).val := by
  rcases hi with h | h <;> simp_all [DegreeTwelveFrame.splitA, DegreeTwelveFrame.splitB]

end TaskH.Seven
#print axioms TaskH.Seven.DegreeTwelveFrame.IsSplitPair
#print axioms TaskH.Seven.DegreeTwelveFrame.splitPair_of_not_common
#print axioms TaskH.Seven.DegreeTwelveFrame.splitA
#print axioms TaskH.Seven.DegreeTwelveFrame.splitB
#print axioms TaskH.Seven.DegreeTwelveFrame.splitA_color
#print axioms TaskH.Seven.DegreeTwelveFrame.splitB_color
#print axioms TaskH.Seven.DegreeTwelveFrame.splitAB_ne
#print axioms TaskH.Seven.DegreeTwelveFrame.splitAB_adjacencies
