import Research.TaskH.Gao.IdentificationDegree

/-! The actual maximal-clique boundary and the sharp finite neighbor budget. -/
set_option autoImplicit false
universe u
namespace TaskH.Gao
open SimpleGraph
variable {V : Type u}

def cliqueBlockBoundary (G : SimpleGraph V) (B K : Set V) (x b : V) : Set V :=
  {p | p ∈ K ∧ p ≠ x ∧ ∃ v ∈ B, v ≠ b ∧ G.Adj v p}

theorem cliqueBlockBoundary_subset (G : SimpleGraph V) (B K : Set V) (x b : V) :
    cliqueBlockBoundary G B K x b ⊆ K := by
  intro p hp
  exact hp.1

theorem root_avoiding_maximal_clique (G : SimpleGraph V) (K : Set V) (x y : V)
    (hK : Maximal (fun L : Set V => G.IsClique L ∧ x ∈ L ∧ y ∉ L) K)
    (hno : ¬G.Adj x y) : Maximal G.IsClique K := by
  refine ⟨hK.1.1, ?_⟩
  intro L hL hKL
  have hxL : x ∈ L := hKL hK.1.2.1
  have hxy : x ≠ y := fun he => hK.1.2.2 (he ▸ hK.1.2.1)
  have hyL : y ∉ L := fun hy => hno (hL hxL hy hxy)
  exact hK.2 ⟨hL, hxL, hyL⟩ hKL

theorem maximal_clique_external_neighbors_lt [Finite V] (G : SimpleGraph V)
    (K : Set V) (hK : Maximal G.IsClique K) (v : V) (hv : v ∉ K) :
    (G.neighborSet v ∩ K).ncard < K.ncard := by
  refine Set.ncard_lt_ncard ?_ (Set.toFinite K)
  rw [Set.ssubset_def]
  refine ⟨Set.inter_subset_right, ?_⟩
  intro hall
  have hins : G.IsClique (insert v K) :=
    (SimpleGraph.isClique_insert_of_notMem hv).mpr
      ⟨hK.1, fun w hw => (hall hw).1⟩
  have hsub : insert v K ⊆ K := hK.2 hins (Set.subset_insert v K)
  exact hv (hsub (Set.mem_insert v K))

theorem disjoint_region_neighbor_partition [Finite V] (G : SimpleGraph V)
    (B K : Set V) (hBK : Disjoint B K) (v : V)
    (hcover : ∀ w, G.Adj v w → w ∈ B ∨ w ∈ K) :
    (G.neighborSet v).ncard =
      (G.neighborSet v ∩ B).ncard + (G.neighborSet v ∩ K).ncard := by
  have heq : G.neighborSet v = (G.neighborSet v ∩ B) ∪ (G.neighborSet v ∩ K) := by
    ext w
    constructor
    · intro hw
      rcases hcover w hw with hB | hK
      · exact Or.inl ⟨hw, hB⟩
      · exact Or.inr ⟨hw, hK⟩
    · rintro (hw | hw) <;> exact hw.1
  have hd : Disjoint (G.neighborSet v ∩ B) (G.neighborSet v ∩ K) := by
    apply Set.disjoint_left.mpr
    intro w hwB hwK
    exact Set.disjoint_left.mp hBK hwB.2 hwK.2
  calc
    (G.neighborSet v).ncard =
        ((G.neighborSet v ∩ B) ∪ (G.neighborSet v ∩ K)).ncard := congrArg Set.ncard heq
    _ = (G.neighborSet v ∩ B).ncard + (G.neighborSet v ∩ K).ncard :=
      Set.ncard_union_eq hd

theorem cliqueBoundary_absent_neighbors_subset (G : SimpleGraph V)
    (B K : Set V) (x b v : V) (hv : v ∈ B) (hvb : v ≠ b)
    (h : ¬∃ w ∈ cliqueBlockBoundary G B K x b, G.Adj v w) :
    G.neighborSet v ∩ K ⊆ {x} := by
  intro w hw
  change w = x
  by_contra hwx
  exact h ⟨w, ⟨hw.2, hwx, ⟨v, hv, hvb, hw.1⟩⟩, hw.1⟩

theorem cliqueBoundary_absent_neighbors_le_one [Finite V] (G : SimpleGraph V)
    (B K : Set V) (x b v : V) (hv : v ∈ B) (hvb : v ≠ b)
    (h : ¬∃ w ∈ cliqueBlockBoundary G B K x b, G.Adj v w) :
    (G.neighborSet v ∩ K).ncard ≤ 1 := by
  have hh := Set.ncard_le_ncard
    (cliqueBoundary_absent_neighbors_subset G B K x b v hv hvb h)
  simpa only [Set.ncard_singleton] using hh

theorem clique_core_strict_order_budget [Finite V] (B K : Set V)
    (hBK : Disjoint B K) (ht : 3 ≤ K.ncard) : B.ncard + 1 < Nat.card V := by
  have hu := Set.ncard_union_eq hBK
  have hb := Set.ncard_le_card (B ∪ K)
  omega

#print axioms cliqueBlockBoundary
#print axioms cliqueBlockBoundary_subset
#print axioms root_avoiding_maximal_clique
#print axioms maximal_clique_external_neighbors_lt
#print axioms disjoint_region_neighbor_partition
#print axioms cliqueBoundary_absent_neighbors_subset
#print axioms cliqueBoundary_absent_neighbors_le_one
#print axioms clique_core_strict_order_budget
end TaskH.Gao
