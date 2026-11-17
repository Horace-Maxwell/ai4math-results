import Research.TaskH.Five.FiveLightEdgeFibers

/-! The actual light-edge degree-sum bound. The five color-class estimates
are derived in one fixed deleted-edge coloring, then summed exactly. -/

universe u

namespace TaskH.Five

open SimpleGraph Challenge

variable {V : Type u} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem light_base_neighbor_fibers {u v : V} (huv : G.Adj u v)
    (c : (G.deleteEdges {s(u, v)}).Coloring (Fin 5)) (he : c u = c v) :
    (lightColorFiber (G.neighborFinset u) c (c u)).card = 1 ∧
    (lightColorFiber (G.neighborFinset v) c (c u)).card = 1 := by
  classical
  have hleft : lightColorFiber (G.neighborFinset u) c (c u) = {v} := by
    ext w
    simp only [lightColorFiber, Finset.mem_filter, G.mem_neighborFinset,
      Finset.mem_singleton]
    constructor
    · rintro ⟨huw, hc⟩
      by_contra hne
      have hd : (G.deleteEdges {s(u, v)}).Adj u w := by
        refine SimpleGraph.deleteEdges_adj.mpr ⟨huw, ?_⟩
        intro hm
        exact hne (Sym2.congr_right.mp (Set.mem_singleton_iff.mp hm))
      exact (c.valid hd) hc.symm
    · rintro rfl
      exact ⟨huv, he.symm⟩
  have hright : lightColorFiber (G.neighborFinset v) c (c u) = {u} := by
    ext w
    simp only [lightColorFiber, Finset.mem_filter, G.mem_neighborFinset,
      Finset.mem_singleton]
    constructor
    · rintro ⟨hvw, hc⟩
      by_contra hne
      have hd : (G.deleteEdges {s(u, v)}).Adj v w := by
        refine SimpleGraph.deleteEdges_adj.mpr ⟨hvw, ?_⟩
        intro hm
        rcases Sym2.eq_iff.mp (Set.mem_singleton_iff.mp hm) with
          ⟨hvu, _⟩ | ⟨_, hwu⟩
        · exact huv.ne hvu.symm
        · exact hne hwu
      exact (c.valid hd) (he.symm.trans hc.symm)
    · rintro rfl
      exact ⟨huv.symm, rfl⟩
  simp only [hleft, hright, Finset.card_singleton, and_self]

theorem light_edge_order_bound_zero
    (hcrit : IsCriticalPlus 5 G) (hs : ShortFiveCycles G)
    (hr : RainbowFiveCycles G) {f : Fin 5 → V} (hf : IsPentagon G f)
    (hlight : IsLightPentagonEdge G f 0) :
    G.degree (f 0) + G.degree (f 1) + 6 ≤ Fintype.card V := by
  classical
  obtain ⟨c⟩ := TaskH.critical_colorable_deletedEdge hcrit hf.2.1
  have he := TaskH.deletedEdge_coloring_endpoints hcrit c
  obtain ⟨b, hb, hmiss, p, hp, hfollow, hmin, hlen, _heven⟩ :=
    critical_exists_missing_color_path_eight hcrit hs hr hf hlight c
  have hno : ∀ w : V, G.Adj (f 0) w → G.Adj (f 1) w → c w ≠ b := by
    intro w hu hv
    obtain ⟨j, rfl⟩ := hlight.1 w hu hv
    exact hmiss j
  let N : Fin 5 → ℕ := fun a => (lightColorFiber Finset.univ c a).card
  let A : Fin 5 → ℕ := fun a => (lightColorFiber (G.neighborFinset (f 0)) c a).card
  let B : Fin 5 → ℕ := fun a => (lightColorFiber (G.neighborFinset (f 1)) c a).card
  let T : Fin 5 → ℕ := fun a =>
    (lightColorFiber (G.neighborFinset (f 0) ∩ G.neighborFinset (f 1)) c a).card
  have hzero : 5 ≤ N (c (f 0)) := light_path_eight_base_class_bound c b p hp hfollow hlen
  have hmissing : A b + B b + 2 ≤ N b :=
    light_path_eight_nonbase_class_bound c b hb he hno p hp hfollow hmin hlen
  have hclass : ∀ a : Fin 5, a ≠ c (f 0) →
      A a + B a + 1 + (if a = b then 1 else 0) ≤ N a + 2 * T a := by
    intro a ha
    by_cases hab : a = b
    · subst a
      simp only [ite_true]
      omega
    · simp only [ite_eq_right hab, Nat.add_zero]
      by_cases ht : T a = 0
      · have hnoa : ∀ w : V, G.Adj (f 0) w → G.Adj (f 1) w → c w ≠ a := by
          intro w hu hv hc
          have hempty : lightColorFiber
              (G.neighborFinset (f 0) ∩ G.neighborFinset (f 1)) c a = ∅ :=
            Finset.card_eq_zero.mp ht
          have hm : w ∈ lightColorFiber
              (G.neighborFinset (f 0) ∩ G.neighborFinset (f 1)) c a := by
            exact Finset.mem_filter.mpr ⟨Finset.mem_inter.mpr
              ⟨(G.mem_neighborFinset (f 0) w).mpr hu,
                (G.mem_neighborFinset (f 1) w).mpr hv⟩, hc⟩
          rw [hempty] at hm
          exact Finset.notMem_empty _ hm
        obtain ⟨q, _hq, hqf, hqmin, hqlen, _hqeven⟩ :=
          critical_exists_long_noncommon_two_color_path hcrit hr hf.2.1 c a ha hnoa
        have hbound : A a + B a + 1 ≤ N a :=
          light_path_six_class_bound c a ha he hnoa q hqf hqmin hqlen
        omega
      · have hbound : A a + B a ≤ N a + T a :=
          light_fiber_union_bound (G.neighborFinset (f 0))
            (G.neighborFinset (f 1)) c a
        omega
  have hsumA : (∑ a : Fin 5, A a) = G.degree (f 0) := by
    change (∑ a : Fin 5, (lightColorFiber (G.neighborFinset (f 0)) c a).card) = _
    rw [light_sum_color_fibers, G.card_neighborFinset_eq_degree]
  have hsumB : (∑ a : Fin 5, B a) = G.degree (f 1) := by
    change (∑ a : Fin 5, (lightColorFiber (G.neighborFinset (f 1)) c a).card) = _
    rw [light_sum_color_fibers, G.card_neighborFinset_eq_degree]
  have hbase := light_base_neighbor_fibers hf.2.1 c he
  have hpartA := Finset.sum_erase_add (s := (Finset.univ : Finset (Fin 5)))
    (f := A) (Finset.mem_univ (c (f 0)))
  have hpartB := Finset.sum_erase_add (s := (Finset.univ : Finset (Fin 5)))
    (f := B) (Finset.mem_univ (c (f 0)))
  have hdegree : G.degree (f 0) + G.degree (f 1) =
      (∑ a ∈ (Finset.univ : Finset (Fin 5)).erase (c (f 0)), (A a + B a)) + 2 := by
    rw [Finset.sum_add_distrib]
    change A (c (f 0)) = 1 ∧ B (c (f 0)) = 1 at hbase
    rw [hbase.1, hsumA] at hpartA
    rw [hbase.2, hsumB] at hpartB
    omega
  have htotal : (∑ a : Fin 5, N a) = Fintype.card V := by
    simp only [N, light_sum_color_fibers, Finset.card_univ]
  have hcommon : (∑ a : Fin 5, T a) ≤ 1 := by
    change (∑ a : Fin 5, (lightColorFiber
      (G.neighborFinset (f 0) ∩ G.neighborFinset (f 1)) c a).card) ≤ 1
    rw [light_sum_color_fibers]
    have hset : G.commonNeighbors (f 0) (f 1) =
        ((G.neighborFinset (f 0) ∩ G.neighborFinset (f 1) : Finset V) : Set V) := by
      ext w
      simp only [G.mem_commonNeighbors, Finset.mem_coe, Finset.mem_inter,
        G.mem_neighborFinset]
    have hc := hlight.2
    change (G.commonNeighbors (f 0) (f 1)).ncard ≤ 1 at hc
    rw [hset, Set.ncard_coe_finset] at hc
    exact hc
  exact light_five_color_budget N A B T (c (f 0)) b hb
    (Fintype.card V) (G.degree (f 0)) (G.degree (f 1))
    hzero hclass hdegree htotal hcommon

def lightRotatePentagon (f : Fin 5 → V) (i : Fin 5) : Fin 5 → V :=
  fun j => f (i + j)

omit [Fintype V] [DecidableRel G.Adj] in
theorem lightRotatePentagon_isPentagon {f : Fin 5 → V} (hf : IsPentagon G f)
    (i : Fin 5) : IsPentagon G (lightRotatePentagon f i) := by
  have hinj : Function.Injective (lightRotatePentagon f i) := by
    intro a b he
    exact add_left_cancel (hf.1 he)
  have hstep : ∀ j : Fin 5, G.Adj (lightRotatePentagon f i j)
      (lightRotatePentagon f i (j + 1)) := by
    intro j
    simpa only [lightRotatePentagon, add_assoc] using pentagon_succ_adj hf (i + j)
  exact ⟨hinj, hstep 0, hstep 1, hstep 2, hstep 3, hstep 4⟩

omit [Fintype V] [DecidableRel G.Adj] in
theorem lightRotatePentagon_isLight {f : Fin 5 → V} (i : Fin 5)
    (hl : IsLightPentagonEdge G f i) :
    IsLightPentagonEdge G (lightRotatePentagon f i) 0 := by
  refine ⟨?_, ?_⟩
  · intro w hu hv
    have hu' : G.Adj (f i) w := by simpa only [lightRotatePentagon, add_zero] using hu
    have hv' : G.Adj (f (i + 1)) w := hv
    obtain ⟨j, hj⟩ := hl.1 w hu' hv'
    have hinj : Function.Injective (fun a : Fin 5 => i + a) := by
      intro a b he
      exact add_left_cancel he
    obtain ⟨k, hk⟩ := Finite.surjective_of_injective hinj j
    change i + k = j at hk
    exact ⟨k, (congrArg f hk).trans hj⟩
  · change (G.commonNeighbors (f (i + 0)) (f (i + (0 + 1)))).ncard ≤ 1
    simpa only [add_zero, zero_add] using hl.2

theorem light_edge_order_bound
    (hcrit : IsCriticalPlus 5 G) (hs : ShortFiveCycles G)
    (hr : RainbowFiveCycles G) (f : Fin 5 → V) (hf : IsPentagon G f)
    (i : Fin 5) (hlight : IsLightPentagonEdge G f i) :
    G.degree (f i) + G.degree (f (i + 1)) + 6 ≤ Fintype.card V := by
  have h := light_edge_order_bound_zero hcrit hs hr
    (lightRotatePentagon_isPentagon hf i) (lightRotatePentagon_isLight i hlight)
  change G.degree (f (i + (0 : Fin 5))) + G.degree (f (i + 1)) + 6 ≤ Fintype.card V at h
  rw [Fin.add_zero] at h
  exact h

theorem pentagon_exists_edge_order_bound
    (hcrit : IsCriticalPlus 5 G) (hs : ShortFiveCycles G)
    (hr : RainbowFiveCycles G) (hn : 7 ≤ Fintype.card V)
    (hgem : ∀ r : Fin 5 → V, ¬ PatternEmbedding G patternGem r)
    (f : Fin 5 → V) (hf : IsPentagon G f) :
    ∃ i : Fin 5, G.Adj (f i) (f (i + 1)) ∧
      G.degree (f i) + G.degree (f (i + 1)) + 6 ≤ Fintype.card V := by
  obtain ⟨i, hi, hlight⟩ := pentagon_has_light_edge hcrit hs hr hn hgem f hf
  exact ⟨i, hi, light_edge_order_bound hcrit hs hr f hf i hlight⟩

end TaskH.Five

#print axioms TaskH.Five.light_base_neighbor_fibers
#print axioms TaskH.Five.light_edge_order_bound_zero
#print axioms TaskH.Five.lightRotatePentagon
#print axioms TaskH.Five.lightRotatePentagon_isPentagon
#print axioms TaskH.Five.lightRotatePentagon_isLight
#print axioms TaskH.Five.light_edge_order_bound
#print axioms TaskH.Five.pentagon_exists_edge_order_bound
