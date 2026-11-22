import Research.TaskN.Antichain.Challenge

namespace TaskN.Antichain

open SimpleGraph

def bridge {V W : Type*} (G : SimpleGraph V) (H : SimpleGraph W)
    (v : V) (w : W) : SimpleGraph (V ⊕ W) :=
  G.sum H ⊔ SimpleGraph.edge (.inl v) (.inr w)

theorem bridge_tree {V W : Type*} [Fintype V] [Fintype W]
    {G : SimpleGraph V} {H : SimpleGraph W} (v : V) (w : W)
    (hg : G.IsTree) (hh : H.IsTree) : (bridge G H v w).IsTree := by
  classical
  rw [SimpleGraph.isTree_iff_connected_and_card]
  refine ⟨hg.connected.sum_sup_edge hh.connected, ?_⟩
  have hn : ¬ (G.sum H).Adj (Sum.inl v) (Sum.inr w) := by simp
  have hne : (Sum.inl v : V ⊕ W) ≠ Sum.inr w := by simp
  have he := (G.sum H).card_edgeFinset_sup_edge hn hne
  have hs := Fintype.card_congr (SimpleGraph.edgeSetSumEquiv (G := G) (H := H))
  have hG := hg.card_edgeFinset
  have hH := hh.card_edgeFinset
  simp only [Fintype.card_sum] at hs
  simp only [SimpleGraph.edgeFinset, Set.toFinset_card] at he hG hH
  change Nat.card (G.sum H ⊔ SimpleGraph.edge (.inl v) (.inr w)).edgeSet + 1 = Nat.card (V ⊕ W)
  simp only [Nat.card_eq_fintype_card, Fintype.card_sum]
  omega

inductive RT where
  | leaf : RT
  | link : RT → RT → RT

def RT.V : RT → Type
  | .leaf => Unit
  | .link l r => l.V ⊕ r.V

instance RT.instFintype : (t : RT) → Fintype t.V
  | .leaf => inferInstanceAs (Fintype Unit)
  | .link l r => by
    letI := l.instFintype
    letI := r.instFintype
    exact inferInstanceAs (Fintype (l.V ⊕ r.V))

def RT.root : (t : RT) → t.V
  | .leaf => ()
  | .link l _ => .inl l.root

def RT.graph : (t : RT) → SimpleGraph t.V
  | .leaf => ⊥
  | .link l r => bridge l.graph r.graph l.root r.root

theorem RT.tree : (t : RT) → t.graph.IsTree
  | .leaf => by exact (SimpleGraph.IsTree.of_subsingleton (V := Unit))
  | .link l r => bridge_tree _ _ l.tree r.tree

def RT.size : RT → ℕ
  | .leaf => 1
  | .link l r => l.size + r.size

theorem RT.cardV : (t : RT) → Fintype.card t.V = t.size
  | .leaf => by decide
  | .link l r => by change Fintype.card (l.V ⊕ r.V) = l.size + r.size
                    rw [Fintype.card_sum, l.cardV, r.cardV]

open Polynomial

/-- Independence polynomial and its root-excluded part for the binary rooted-tree code. -/
noncomputable def RT.pair : RT → ℝ[X] × ℝ[X]
  | .leaf => (1 + X, 1)
  | .link l r =>
    (l.pair.2 * r.pair.1 + (l.pair.1 - l.pair.2) * r.pair.2, l.pair.2 * r.pair.1)

end TaskN.Antichain
