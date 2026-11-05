import Research.Backfill.Paper7.IntroForestPolynomialParity
import Research.Backfill.Paper7.UnicyclicSchwenkIdentity
import Research.Backfill.Paper7.UnicyclicOffCycleForest

/-! The odd part of the characteristic polynomial of an arbitrary unicyclic
graph with an odd cycle. All deleted graphs are the actual induced graphs;
neither a Sun representation nor any bound on off-cycle branching is assumed. -/
set_option autoImplicit false
noncomputable section
open scoped Classical

namespace Paper7IntroOddForest
open SimpleGraph Polynomial BackfillPaper7.Challenge
open BackfillPaper7.Challenge.Legacy.Algebra Paper7UnicyclicSchwenk

theorem complement_finset_card_add {V : Type} [Fintype V] [DecidableEq V]
    (S : Finset V) : Fintype.card {v : V // v ∉ S} + S.card = Fintype.card V := by
  rw [Fintype.card_subtype_compl (fun v : V => v ∈ S), Fintype.card_coe]
  exact Nat.sub_add_cancel (Finset.card_le_univ S)
#print axioms Paper7IntroOddForest.complement_finset_card_add

theorem delete_pair_card_add {V : Type} [Fintype V] [DecidableEq V]
    (u v : V) (hne : u ≠ v) :
    Fintype.card {z : V // z ∉ ({u, v} : Set V)} + 2 = Fintype.card V := by
  have hcard : Fintype.card {z : V // z ∉ ({u, v} : Set V)} =
      Fintype.card {z : V // z ∉ ({u, v} : Finset V)} := by
    apply Fintype.card_congr
    exact Equiv.subtypeEquivRight (fun z => by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff,
        Finset.mem_insert, Finset.mem_singleton])
  rw [hcard, ← Finset.card_pair hne]
  exact complement_finset_card_add ({u, v} : Finset V)
#print axioms Paper7IntroOddForest.delete_pair_card_add

theorem delete_cycle_card_add {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (b : ℕ) (r : V) (w : G.Walk r r)
    (hw : w.IsCycle) (hlen : w.length = b) :
    Fintype.card {z : V // z ∉ ({z | z ∈ w.support} : Set V)} + b =
      Fintype.card V := by
  have hcard : Fintype.card {z : V // z ∉ ({z | z ∈ w.support} : Set V)} =
      Fintype.card {z : V // z ∉ w.support.toFinset} := by
    apply Fintype.card_congr
    exact Equiv.subtypeEquivRight (fun z => by
      change (z ∉ w.support) ↔ (z ∉ w.support.toFinset)
      exact not_congr List.mem_toFinset.symm)
  have hs : w.support.toFinset.card = b :=
    (Paper7Cycles.cycle_support_card w hw).trans hlen
  rw [hcard, ← hs]
  exact complement_finset_card_add w.support.toFinset
#print axioms Paper7IntroOddForest.delete_cycle_card_add

theorem negOne_pow_mul_self (n : ℕ) : (-1 : ℤ) ^ n * (-1 : ℤ) ^ n = 1 := by
  rw [← mul_pow]
  norm_num
#print axioms Paper7IntroOddForest.negOne_pow_mul_self

theorem odd_deletion_degree_signs (n d f b : ℕ)
    (hd : d + 2 = n) (hf : f + b = n) (hb : Odd b) :
    (-1 : ℤ) ^ n * (-1 : ℤ) ^ n = 1 ∧
      (-1 : ℤ) ^ n * (-1 : ℤ) ^ d = 1 ∧
      (-1 : ℤ) ^ n * (-1 : ℤ) ^ f = -1 := by
  have hdsgn : (-1 : ℤ) ^ n = (-1 : ℤ) ^ d := by
    rw [← hd, pow_add]
    norm_num
  have hfsgn : (-1 : ℤ) ^ n = (-1 : ℤ) ^ f * -1 := by
    rw [← hf, pow_add, hb.neg_one_pow]
  refine ⟨negOne_pow_mul_self n, ?_, ?_⟩
  · rw [hdsgn]
    exact negOne_pow_mul_self d
  · calc
      (-1 : ℤ) ^ n * (-1 : ℤ) ^ f =
          ((-1 : ℤ) ^ f * (-1 : ℤ) ^ f) * -1 := by rw [hfsgn]; ring
      _ = -1 := by rw [negOne_pow_mul_self]; norm_num
#print axioms Paper7IntroOddForest.odd_deletion_degree_signs

theorem unicyclic_delete_cycle_edge_endpoints_isAcyclic
    {V : Type} [DecidableEq V] (G : SimpleGraph V) (b : ℕ)
    (hG : IsUnicyclicWithCycle G b) (r : V) (w : G.Walk r r)
    (hw : w.IsCycle) (hlen : w.length = b) (u v : V) (he : s(u, v) ∈ w.edges) :
    (deleteVertices G ({u, v} : Set V)).IsAcyclic := by
  have hT := cycle_edge_deleted_tree G b hG r w hw hlen u v he
  have hD : (deleteVertices (G.deleteEdges ({s(u, v)} : Set (Sym2 V)))
      ({u, v} : Set V)).IsAcyclic :=
    hT.isAcyclic.induce (({u, v} : Set V)ᶜ)
  rw [deleteVertices_deleteEdge G u v ({u, v} : Set V) (by simp)] at hD
  exact hD
#print axioms Paper7IntroOddForest.unicyclic_delete_cycle_edge_endpoints_isAcyclic

theorem unicyclic_odd_graphPhi_eval {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (b : ℕ)
    (hG : IsUnicyclicWithCycle G b) (hb : Odd b)
    (r : V) (w : G.Walk r r) (hw : w.IsCycle) (hlen : w.length = b) (x : ℤ) :
    (graphPhi G).eval x - (-1 : ℤ) ^ Fintype.card V * (graphPhi G).eval (-x) =
      -4 * (graphPhi (deleteVertices G {z | z ∈ w.support})).eval x := by
  have he : s(r, w.snd) ∈ w.edges := w.mk_start_snd_mem_edges hw.not_nil
  have hadj : G.Adj r w.snd := w.edges_subset_edgeSet he
  let T := G.deleteEdges ({s(r, w.snd)} : Set (Sym2 V))
  let D := deleteVertices G ({r, w.snd} : Set V)
  let F := deleteVertices G {z | z ∈ w.support}
  have hT : T.IsTree := cycle_edge_deleted_tree G b hG r w hw hlen r w.snd he
  have hD : D.IsAcyclic :=
    unicyclic_delete_cycle_edge_endpoints_isAcyclic G b hG r w hw hlen r w.snd he
  have hF : F.IsAcyclic :=
    Paper7UnicyclicStructure.unicyclic_off_cycle_isAcyclic G b hG r w hw hlen
  have hs : graphPhi G = graphPhi T - graphPhi D - 2 * graphPhi F :=
    check_UnicyclicSchwenkIdentity V G b hG r w hw hlen r w.snd he
  have hp := congrArg (fun q : Polynomial ℤ => q.eval x) hs
  have hm := congrArg (fun q : Polynomial ℤ => q.eval (-x)) hs
  simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_ofNat] at hp hm
  have htp := forest_graphPhi_eval_neg T hT.isAcyclic x
  have hdp := forest_graphPhi_eval_neg D hD x
  have hfp := forest_graphPhi_eval_neg F hF x
  rw [htp, hdp, hfp] at hm
  obtain ⟨hnn, hnd, hnf⟩ := odd_deletion_degree_signs (Fintype.card V)
    (Fintype.card {z : V // z ∉ ({r, w.snd} : Set V)})
    (Fintype.card {z : V // z ∉ ({z | z ∈ w.support} : Set V)}) b
    (delete_pair_card_add r w.snd hadj.ne) (delete_cycle_card_add G b r w hw hlen) hb
  calc
    (graphPhi G).eval x - (-1 : ℤ) ^ Fintype.card V * (graphPhi G).eval (-x) =
        (1 - (-1 : ℤ) ^ Fintype.card V * (-1 : ℤ) ^ Fintype.card V) *
            (graphPhi T).eval x -
          (1 - (-1 : ℤ) ^ Fintype.card V *
            (-1 : ℤ) ^ Fintype.card {z : V // z ∉ ({r, w.snd} : Set V)}) *
            (graphPhi D).eval x +
          (2 * ((-1 : ℤ) ^ Fintype.card V *
            (-1 : ℤ) ^ Fintype.card {z : V // z ∉ ({z | z ∈ w.support} : Set V)}) - 2) *
            (graphPhi F).eval x := by rw [hp, hm]; ring
    _ = -4 * (graphPhi F).eval x := by rw [hnn, hnd, hnf]; ring
#print axioms Paper7IntroOddForest.unicyclic_odd_graphPhi_eval

theorem unicyclic_odd_graphPhi_identity {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (b : ℕ)
    (hG : IsUnicyclicWithCycle G b) (hb : Odd b)
    (r : V) (w : G.Walk r r) (hw : w.IsCycle) (hlen : w.length = b) :
    graphPhi G - C ((-1 : ℤ) ^ Fintype.card V) * (graphPhi G).comp (-X) =
      C (-4) * graphPhi (deleteVertices G {z | z ∈ w.support}) := by
  apply Polynomial.funext
  intro x
  simpa only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_comp, Polynomial.eval_neg, Polynomial.eval_X] using
    unicyclic_odd_graphPhi_eval G b hG hb r w hw hlen x
#print axioms Paper7IntroOddForest.unicyclic_odd_graphPhi_identity

theorem unicyclic_odd_exists_forest_identity {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (b : ℕ)
    (hG : IsUnicyclicWithCycle G b) (hb : Odd b) :
    ∃ (r : V) (w : G.Walk r r), w.IsCycle ∧ w.length = b ∧
      (deleteVertices G {z | z ∈ w.support}).IsAcyclic ∧
      Fintype.card {z : V // z ∉ ({z | z ∈ w.support} : Set V)} + b = Fintype.card V ∧
      graphPhi G - C ((-1 : ℤ) ^ Fintype.card V) * (graphPhi G).comp (-X) =
        C (-4) * graphPhi (deleteVertices G {z | z ∈ w.support}) := by
  obtain ⟨s, ⟨r, w, hw, hlen, _hs⟩, _huniq⟩ := hG.2
  exact ⟨r, w, hw, hlen,
    Paper7UnicyclicStructure.unicyclic_off_cycle_isAcyclic G b hG r w hw hlen,
    delete_cycle_card_add G b r w hw hlen,
    unicyclic_odd_graphPhi_identity G b hG hb r w hw hlen⟩
#print axioms Paper7IntroOddForest.unicyclic_odd_exists_forest_identity

end Paper7IntroOddForest
