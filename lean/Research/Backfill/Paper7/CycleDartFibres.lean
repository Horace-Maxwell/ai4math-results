import Research.Backfill.Paper7.CycleBasedTypes

set_option autoImplicit false

noncomputable section

open SimpleGraph Finset
open scoped Classical
open BackfillPaper7.Challenge

namespace Paper7Cycles

variable {V : Type} [Fintype V] [DecidableEq V]

theorem dart_subset_card (H : SimpleGraph V) [DecidableRel H.Adj]
    (S : Finset (Sym2 V)) (hS : ∀ e ∈ S, e ∈ H.edgeSet) :
    Fintype.card {d : H.Dart // d.edge ∈ S} = 2 * S.card := by
  rw [Fintype.card_subtype]
  calc
    (Finset.univ.filter (fun d : H.Dart => d.edge ∈ S)).card =
        ∑ e ∈ S, ((Finset.univ.filter (fun d : H.Dart => d.edge ∈ S)).filter
          (fun d => d.edge = e)).card :=
      Finset.card_eq_sum_card_fiberwise fun d hd => (Finset.mem_filter.mp hd).2
    _ = ∑ e ∈ S, (Finset.univ.filter (fun d : H.Dart => d.edge = e)).card := by
      apply Finset.sum_congr rfl
      intro e he
      congr 1
      ext d
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨fun h => h.2, fun hd => ⟨hd.symm ▸ he, hd⟩⟩
    _ = ∑ _e ∈ S, 2 := by
      apply Finset.sum_congr rfl
      intro e he
      exact H.dart_edge_fiber_card e (hS e he)
    _ = 2 * S.card := by simp [Nat.mul_comm]

#print axioms Paper7Cycles.dart_subset_card

def cycleFibreDart {H : SimpleGraph V} [DecidableRel H.Adj] {g : ℕ}
    (S : Finset (Sym2 V))
    (w : {w : BasedCycle H g // basedCycleEdges w = S}) :
    {d : H.Dart // d.edge ∈ S} :=
  ⟨basedCycleFirstDart w.val, Eq.mp (congrArg (fun T : Finset (Sym2 V) => (basedCycleFirstDart w.val).edge ∈ T)
    w.property) (firstDart_mem_basedCycleEdges w.val)⟩

#print axioms Paper7Cycles.cycleFibreDart

omit [Fintype V] in
theorem cycleFibreDart_injective {H : SimpleGraph V} [DecidableRel H.Adj] {g : ℕ}
    (S : Finset (Sym2 V)) : Function.Injective (cycleFibreDart (H := H) (g := g) S) := by
  intro a b hab
  rcases a with ⟨⟨u, ⟨⟨p, _hpL⟩, hp⟩⟩, hps⟩
  rcases b with ⟨⟨v, ⟨⟨q, _hqL⟩, hq⟩⟩, hqs⟩
  have hd := congrArg Subtype.val hab
  have huv : u = v := congrArg (fun d : H.Dart => d.fst) hd
  subst v
  have hsnd : p.snd = q.snd := congrArg (fun d : H.Dart => d.snd) hd
  have hpq : p = q := cycle_eq_of_edgeFinset_snd hp hq (hps.trans hqs.symm) hsnd
  subst q
  rfl

#print axioms Paper7Cycles.cycleFibreDart_injective

omit [Fintype V] in
theorem cycleFibreDart_surjective {H : SimpleGraph V} [DecidableRel H.Adj] {g : ℕ}
    (S : Finset (Sym2 V)) (hS : S ∈ cycleEdgeSets H g) :
    Function.Surjective (cycleFibreDart (H := H) (g := g) S) := by
  intro d
  obtain ⟨_u, p, hp, hpL, hpS⟩ := hS
  have hd : d.val.edge ∈ p.edges := by
    apply List.mem_toFinset.mp
    rw [hpS]
    exact d.property
  obtain ⟨q, hq, hqL, hqS, hqsnd⟩ := cycle_with_first_dart p hp d.val hd
  refine ⟨⟨⟨d.val.fst, ⟨⟨q, hqL.trans hpL⟩, hq⟩⟩, hqS.trans hpS⟩, ?_⟩
  apply Subtype.ext
  apply SimpleGraph.Dart.ext
  apply Prod.ext
  · rfl
  · exact hqsnd

#print axioms Paper7Cycles.cycleFibreDart_surjective

theorem cycleFibre_card {H : SimpleGraph V} [DecidableRel H.Adj] {g : ℕ}
    (S : Finset (Sym2 V)) (hS : S ∈ cycleEdgeSets H g) :
    Fintype.card {w : BasedCycle H g // basedCycleEdges w = S} = 2 * g := by
  have hScard : S.card = g := by
    obtain ⟨_u, p, hp, hpL, hpS⟩ := hS
    rw [← hpS, List.toFinset_card_of_nodup hp.isTrail.edges_nodup,
      Walk.length_edges, hpL]
  have hSedges : ∀ e ∈ S, e ∈ H.edgeSet := by
    obtain ⟨_u, p, _hp, _hpL, hpS⟩ := hS
    intro e he
    rw [← hpS] at he
    exact p.edges_subset_edgeSet (List.mem_toFinset.mp he)
  calc
    Fintype.card {w : BasedCycle H g // basedCycleEdges w = S} =
        Fintype.card {d : H.Dart // d.edge ∈ S} :=
      Fintype.card_congr (Equiv.ofBijective (cycleFibreDart S)
        ⟨cycleFibreDart_injective S, cycleFibreDart_surjective S hS⟩)
    _ = 2 * S.card := dart_subset_card H S hSedges
    _ = 2 * g := by rw [hScard]

#print axioms Paper7Cycles.cycleFibre_card

end Paper7Cycles
