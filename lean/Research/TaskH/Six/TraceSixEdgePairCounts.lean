import Research.TaskH.Six.TraceSixEdgePairData

/-!
Exact finite-graph count for two oriented edges on four different vertices.
All terms are counts of the actual graph and its actual degrees/edgeFinset.
-/

set_option autoImplicit false

universe u

namespace TaskH.Six

open SimpleGraph

variable {V : Type u} [Fintype V] {G : SimpleGraph V}

theorem traceEdgePairWords_card_eq_oriented_square :
    (traceEdgePairWords G).card = (traceOrientedEdges G).card ^ 2 := by
  classical
  calc
    _ = ((traceOrientedEdges G).product (traceOrientedEdges G)).card := by
      apply Finset.card_bij (fun f _ => ((f 0, f 1), (f 2, f 3)))
      · intro f hf
        have hp := (mem_traceEdgePairWords_iff f).mp hf
        exact Finset.mem_product.mpr
          ⟨(mem_traceOrientedEdges_iff _).mpr hp.1,
            (mem_traceOrientedEdges_iff _).mpr hp.2⟩
      · intro f _ g _ he
        have h0 := congrArg (fun p : (V × V) × (V × V) => p.1.1) he
        have h1 := congrArg (fun p : (V × V) × (V × V) => p.1.2) he
        have h2 := congrArg (fun p : (V × V) × (V × V) => p.2.1) he
        have h3 := congrArg (fun p : (V × V) × (V × V) => p.2.2) he
        funext i
        fin_cases i <;> assumption
      · intro p hp
        obtain ⟨h1, h2⟩ := Finset.mem_product.mp hp
        exact ⟨![p.1.1, p.1.2, p.2.1, p.2.2],
          (mem_traceEdgePairWords_iff _).mpr
            ⟨(mem_traceOrientedEdges_iff _).mp h1,
              (mem_traceOrientedEdges_iff _).mp h2⟩, rfl⟩
    _ = _ := by rw [Finset.product_eq_sprod, Finset.card_product, pow_two]

theorem traceEdgePairDiagonalWords_card_eq_oriented (reverse : Bool) :
    (traceEdgePairDiagonalWords G reverse).card = (traceOrientedEdges G).card := by
  classical
  have hr := trace_edge_pair_filter_reindex_card (G := G) false reverse
    (fun f => f 0 = f 2 ∧ f 1 = f 3)
  have hdiag : traceEdgePairDiagonalWords G reverse =
      (traceEdgePairWords G).filter (fun f =>
        traceEdgePairReindex false reverse f 0 = traceEdgePairReindex false reverse f 2 ∧
          traceEdgePairReindex false reverse f 1 = traceEdgePairReindex false reverse f 3) := by
    ext f
    simp only [mem_traceEdgePairDiagonalWords_iff, Finset.mem_filter,
      mem_traceEdgePairWords_iff, TraceEdgePairDiagonal]
  have hcard : (traceEdgePairDiagonalWords G reverse).card =
      ((traceEdgePairWords G).filter (fun f => f 0 = f 2 ∧ f 1 = f 3)).card := by
    calc
      _ = ((traceEdgePairWords G).filter (fun f =>
          traceEdgePairReindex false reverse f 0 = traceEdgePairReindex false reverse f 2 ∧
            traceEdgePairReindex false reverse f 1 = traceEdgePairReindex false reverse f 3)).card :=
        congrArg Finset.card hdiag
      _ = _ := by
        convert hr using 1 <;> congr 1 <;> ext f <;> simp only [Finset.mem_filter]
  rw [hcard]
  apply Finset.card_bij (fun f _ => (f 0, f 1))
  · intro f hf
    have hp := (mem_traceEdgePairWords_iff f).mp (Finset.mem_filter.mp hf).1
    exact (mem_traceOrientedEdges_iff _).mpr hp.1
  · intro f hf g hg he
    have hf2 := (Finset.mem_filter.mp hf).2
    have hg2 := (Finset.mem_filter.mp hg).2
    have h0 : f 0 = g 0 := congrArg Prod.fst he
    have h1 : f 1 = g 1 := congrArg Prod.snd he
    have h2 : f 2 = g 2 := hf2.1.symm.trans (h0.trans hg2.1)
    have h3 : f 3 = g 3 := hf2.2.symm.trans (h1.trans hg2.2)
    funext i
    fin_cases i <;> assumption
  · intro p hp
    have hab := (mem_traceOrientedEdges_iff p).mp hp
    exact ⟨![p.1, p.2, p.1, p.2], Finset.mem_filter.mpr
      ⟨(mem_traceEdgePairWords_iff _).mpr ⟨hab, hab⟩, rfl, rfl⟩, rfl⟩

theorem traceEdgePairCrossWords_card_eq_base (left right : Bool) :
    (traceEdgePairCrossWords G left right).card =
      (traceEdgePairCrossWords G false false).card := by
  classical
  exact trace_edge_pair_filter_reindex_card left right (fun f => f 0 = f 2)

variable [DecidableRel G.Adj]

open scoped Classical in
theorem trace_edge_pair_cross_base_fiber_card (x : V) :
    ((traceEdgePairCrossWords G false false).filter (fun f => f 0 = x)).card =
      (G.degree x) ^ 2 := by
  classical
  calc
    _ = ((G.neighborFinset x).product (G.neighborFinset x)).card := by
      apply Finset.card_bij (fun f _ => (f 1, f 3))
      · intro f hf
        obtain ⟨hfm, h0⟩ := Finset.mem_filter.mp hf
        obtain ⟨hp, hc⟩ := (mem_traceEdgePairCrossWords_iff false false f).mp hfm
        change f 0 = f 2 at hc
        have h2 : f 2 = x := hc.symm.trans h0
        exact Finset.mem_product.mpr
          ⟨(G.mem_neighborFinset x (f 1)).mpr (by simpa only [h0] using hp.1),
            (G.mem_neighborFinset x (f 3)).mpr (by simpa only [h2] using hp.2)⟩
      · intro f hf g hg he
        obtain ⟨hfm, hf0⟩ := Finset.mem_filter.mp hf
        obtain ⟨hgm, hg0⟩ := Finset.mem_filter.mp hg
        have hf02 := ((mem_traceEdgePairCrossWords_iff false false f).mp hfm).2
        have hg02 := ((mem_traceEdgePairCrossWords_iff false false g).mp hgm).2
        change f 0 = f 2 at hf02
        change g 0 = g 2 at hg02
        have h0 : f 0 = g 0 := hf0.trans hg0.symm
        have h1 : f 1 = g 1 := congrArg Prod.fst he
        have h2 : f 2 = g 2 := hf02.symm.trans (h0.trans hg02)
        have h3 : f 3 = g 3 := congrArg Prod.snd he
        funext i
        fin_cases i <;> assumption
      · intro p hp
        obtain ⟨h1, h2⟩ := Finset.mem_product.mp hp
        have hx1 := (G.mem_neighborFinset x p.1).mp h1
        have hx2 := (G.mem_neighborFinset x p.2).mp h2
        exact ⟨![x, p.1, x, p.2], Finset.mem_filter.mpr
          ⟨(mem_traceEdgePairCrossWords_iff false false _).mpr
            ⟨⟨hx1, hx2⟩, rfl⟩, rfl⟩, rfl⟩
    _ = _ := by
      rw [Finset.product_eq_sprod, Finset.card_product, G.card_neighborFinset_eq_degree, pow_two]

theorem traceEdgePairCrossWords_card (left right : Bool) :
    (traceEdgePairCrossWords G left right).card = ∑ x : V, (G.degree x) ^ 2 := by
  classical
  rw [traceEdgePairCrossWords_card_eq_base]
  calc
    _ = ∑ x : V,
        ((traceEdgePairCrossWords G false false).filter (fun f => f 0 = x)).card :=
      Finset.card_eq_sum_card_fiberwise (fun _ _ => Finset.mem_univ _)
    _ = _ := Finset.sum_congr rfl (fun x _ => trace_edge_pair_cross_base_fiber_card x)

theorem traceOrientedEdges_card :
    (traceOrientedEdges G).card = 2 * G.edgeFinset.card := by
  classical
  calc
    _ = (Finset.univ.filter (fun p : V × V => G.Adj p.1 p.2)).card := by
      congr 1
      ext p
      simp only [mem_traceOrientedEdges_iff, Finset.mem_filter, Finset.mem_univ, true_and]
    _ = _ := G.two_mul_card_edgeFinset.symm

theorem traceEdgePairWords_card :
    (traceEdgePairWords G).card = (2 * G.edgeFinset.card) ^ 2 := by
  rw [traceEdgePairWords_card_eq_oriented_square, traceOrientedEdges_card]

theorem traceEdgePairDiagonalWords_card (reverse : Bool) :
    (traceEdgePairDiagonalWords G reverse).card = 2 * G.edgeFinset.card := by
  rw [traceEdgePairDiagonalWords_card_eq_oriented reverse, traceOrientedEdges_card]

theorem trace_disjoint_edge_words_count_balance :
    (traceDisjointEdgeWords G).card + 4 * (∑ x : V, (G.degree x) ^ 2) =
      4 * G.edgeFinset.card ^ 2 + 4 * G.edgeFinset.card := by
  have hc := trace_edge_pair_card_balance (G := G)
  simp only [traceEdgePairWords_card, traceEdgePairDiagonalWords_card,
    traceEdgePairCrossWords_card] at hc
  nlinarith [hc]

theorem trace_disjoint_edge_words_count_real :
    ((traceDisjointEdgeWords G).card : ℝ) =
      4 * (G.edgeFinset.card : ℝ) ^ 2 + 4 * G.edgeFinset.card -
        4 * (∑ x : V, (G.degree x : ℝ) ^ 2) := by
  have hn := trace_disjoint_edge_words_count_balance (G := G)
  have hr : ((traceDisjointEdgeWords G).card : ℝ) +
      4 * (∑ x : V, (G.degree x : ℝ) ^ 2) =
      4 * (G.edgeFinset.card : ℝ) ^ 2 + 4 * G.edgeFinset.card := by
    exact_mod_cast hn
  linarith

end TaskH.Six

#print axioms TaskH.Six.traceEdgePairWords_card_eq_oriented_square
#print axioms TaskH.Six.traceEdgePairDiagonalWords_card_eq_oriented
#print axioms TaskH.Six.traceEdgePairCrossWords_card_eq_base
#print axioms TaskH.Six.trace_edge_pair_cross_base_fiber_card
#print axioms TaskH.Six.traceEdgePairCrossWords_card
#print axioms TaskH.Six.traceOrientedEdges_card
#print axioms TaskH.Six.traceEdgePairWords_card
#print axioms TaskH.Six.traceEdgePairDiagonalWords_card
#print axioms TaskH.Six.trace_disjoint_edge_words_count_balance
#print axioms TaskH.Six.trace_disjoint_edge_words_count_real
