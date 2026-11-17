import Research.TaskH.Seven.SevenBPEighteenTripleClassification

/-! Actual outside neighbors of a three-hook vertex are low. Distinct actual
triple hook sets can share an outside neighbor only when it has no cycle hook. -/
set_option autoImplicit false
universe u
namespace TaskH.Seven.BP
open SimpleGraph
open scoped Classical
variable {V : Type u} {G : SimpleGraph V}

def eighteenTripleCompatibleIndex (q : Fin 2) (i : Fin 9) : Fin 18 :=
  if q=0 then eighteenClassIndex 1 i else eighteenClassIndex 0 (i+1)

theorem eighteenTripleCompatibleIndex_injective :
    Function.Injective (fun p : Fin 2 × Fin 9 => eighteenTripleCompatibleIndex p.1 p.2) := by
  unfold eighteenTripleCompatibleIndex
  decide +kernel

theorem eighteen_three_ear_endpoint_parity (hb : G.IsBipartite)
    (u : Fin 18 → V) (hu : IsCycleEighteen G u) (a b : V) (i j : Fin 18)
    (h0 : G.Adj (u i) b) (hba : G.Adj b a) (hend : G.Adj a (u j)) :
    i.val%2≠j.val%2 := by
  let c : G.Coloring Bool := SimpleGraph.recolorOfEquiv G finTwoEquiv hb.some
  have hne : c (u i)≠c (u j) := by
    have h1 := c.valid h0
    have h2 := c.valid hba
    have h3 := c.valid hend
    cases hi : c (u i) <;> cases hb : c b <;> cases ha : c a <;> cases hj : c (u j) <;> simp_all
  intro hpar
  have hci := cycle_eighteen_color_even_iff u hu c i
  have hcj := cycle_eighteen_color_even_iff u hu c j
  have he : Even i.val ↔ Even j.val := by rw [Nat.even_iff,Nat.even_iff,hpar]
  cases h0 : c (u 0) <;> cases hi : c (u i) <;> cases hj : c (u j) <;> simp_all

theorem eighteen_even_triple_neighbor_subset (hb : G.IsBipartite)
    (h14 : NoFourteenCycle G) (h16 : NoSixteenCycle G)
    (u : Fin 18 → V) (hu : IsCycleEighteen G u) (a b : V)
    (ha : a ∉ Set.range u) (hbout : b ∉ Set.range u) (hba : G.Adj b a) (i : Fin 9)
    (hshape : eighteenOutsideHooks G u b =
      {eighteenClassIndex 0 i,eighteenClassIndex 0 (i+1),eighteenClassIndex 0 (i+5)}) :
    eighteenOutsideHooks G u a ⊆ {eighteenClassIndex 1 i} := by
  have h0 : G.Adj (u (eighteenClassIndex 0 i)) b := by
    have hm : eighteenClassIndex 0 i ∈ eighteenOutsideHooks G u b := by rw [hshape]; simp
    exact (Finset.mem_filter.mp hm).2.symm
  have h1 : G.Adj (u (eighteenClassIndex 0 (i+1))) b := by
    have hm : eighteenClassIndex 0 (i+1) ∈ eighteenOutsideHooks G u b := by rw [hshape]; simp
    exact (Finset.mem_filter.mp hm).2.symm
  have h5 : G.Adj (u (eighteenClassIndex 0 (i+5))) b := by
    have hm : eighteenClassIndex 0 (i+5) ∈ eighteenOutsideHooks G u b := by rw [hshape]; simp
    exact (Finset.mem_filter.mp hm).2.symm
  intro j hj
  have haj := (Finset.mem_filter.mp hj).2
  have hpar := eighteen_three_ear_endpoint_parity hb u hu a b (eighteenClassIndex 0 i) j h0 hba haj
  have tab : ∀ i : Fin 9, ∀ j : Fin 18,
      (eighteenClassIndex 0 i).val%2≠j.val%2 → ∃ k : Fin 9,eighteenClassIndex 1 k=j := by decide +kernel
  obtain ⟨k,hk⟩ := tab i j hpar
  have hki := eighteen_even_triple_forces_unique_odd_hook u hu h14 h16 a b ha hbout hba i k h0 h1 h5
    (by simpa only [hk] using haj)
  apply Finset.mem_singleton.mpr
  rw [← hk,hki]

theorem eighteen_odd_triple_neighbor_subset (hb : G.IsBipartite)
    (h14 : NoFourteenCycle G) (h16 : NoSixteenCycle G)
    (u : Fin 18 → V) (hu : IsCycleEighteen G u) (a b : V)
    (ha : a ∉ Set.range u) (hbout : b ∉ Set.range u) (hba : G.Adj b a) (i : Fin 9)
    (hshape : eighteenOutsideHooks G u b =
      {eighteenClassIndex 1 i,eighteenClassIndex 1 (i+1),eighteenClassIndex 1 (i+5)}) :
    eighteenOutsideHooks G u a ⊆ {eighteenClassIndex 0 (i+1)} := by
  have h0 : G.Adj (u (eighteenClassIndex 1 i)) b := by
    have hm : eighteenClassIndex 1 i ∈ eighteenOutsideHooks G u b := by rw [hshape]; simp
    exact (Finset.mem_filter.mp hm).2.symm
  have h1 : G.Adj (u (eighteenClassIndex 1 (i+1))) b := by
    have hm : eighteenClassIndex 1 (i+1) ∈ eighteenOutsideHooks G u b := by rw [hshape]; simp
    exact (Finset.mem_filter.mp hm).2.symm
  have h5 : G.Adj (u (eighteenClassIndex 1 (i+5))) b := by
    have hm : eighteenClassIndex 1 (i+5) ∈ eighteenOutsideHooks G u b := by rw [hshape]; simp
    exact (Finset.mem_filter.mp hm).2.symm
  intro j hj
  have haj := (Finset.mem_filter.mp hj).2
  have hpar := eighteen_three_ear_endpoint_parity hb u hu a b (eighteenClassIndex 1 i) j h0 hba haj
  have tab : ∀ i : Fin 9, ∀ j : Fin 18,
      (eighteenClassIndex 1 i).val%2≠j.val%2 → ∃ k : Fin 9,eighteenClassIndex 0 k=j := by decide +kernel
  obtain ⟨k,hk⟩ := tab i j hpar
  have hki := eighteen_odd_triple_forces_unique_even_hook u hu h14 h16 b a hbout ha hba.symm k i
    (by simpa only [hk] using haj.symm) h0.symm h1.symm h5.symm
  apply Finset.mem_singleton.mpr
  rw [← hk,hki]

theorem eighteen_triple_neighbor_subset (hb : G.IsBipartite)
    (h14 : NoFourteenCycle G) (h16 : NoSixteenCycle G)
    (u : Fin 18 → V) (hu : IsCycleEighteen G u) (a b : V)
    (ha : a ∉ Set.range u) (hbout : b ∉ Set.range u) (hba : G.Adj b a)
    (q : Fin 2) (i : Fin 9) (hshape : eighteenOutsideHooks G u b =
      {eighteenClassIndex q i,eighteenClassIndex q (i+1),eighteenClassIndex q (i+5)}) :
    eighteenOutsideHooks G u a ⊆ {eighteenTripleCompatibleIndex q i} := by
  have hcases : ∀ r : Fin 2, r = 0 ∨ r = 1 := by decide +kernel
  rcases hcases q with hq | hq
  · subst q
    simpa only [eighteenTripleCompatibleIndex,ite_true] using
      eighteen_even_triple_neighbor_subset hb h14 h16 u hu a b ha hbout hba i hshape
  · subst q
    simpa only [eighteenTripleCompatibleIndex,show ¬((1 : Fin 2)=0) by decide,ite_false] using
      eighteen_odd_triple_neighbor_subset hb h14 h16 u hu a b ha hbout hba i hshape

theorem eighteen_neighbor_of_triple_is_low (hb : G.IsBipartite)
    (h14 : NoFourteenCycle G) (h16 : NoSixteenCycle G)
    (u : Fin 18 → V) (hu : IsCycleEighteen G u) (a b : V)
    (ha : a ∉ Set.range u) (hbout : b ∉ Set.range u) (hba : G.Adj b a)
    (hc : (eighteenOutsideHooks G u b).card=3) : (eighteenOutsideHooks G u a).card≤1 := by
  obtain ⟨q,i,hshape⟩ := eighteen_actual_triple_classification hb h14 h16 u hu b hbout hc
  have hs := eighteen_triple_neighbor_subset hb h14 h16 u hu a b ha hbout hba q i hshape
  have hh := Finset.card_le_card hs
  simpa only [Finset.card_singleton] using hh

theorem eighteen_distinct_triples_common_neighbor_zero (hb : G.IsBipartite)
    (h14 : NoFourteenCycle G) (h16 : NoSixteenCycle G)
    (u : Fin 18 → V) (hu : IsCycleEighteen G u) (a b c : V)
    (ha : a ∉ Set.range u) (hbout : b ∉ Set.range u) (hcout : c ∉ Set.range u)
    (hba : G.Adj b a) (hca : G.Adj c a)
    (hb3 : (eighteenOutsideHooks G u b).card=3) (hc3 : (eighteenOutsideHooks G u c).card=3)
    (hne : eighteenOutsideHooks G u b≠eighteenOutsideHooks G u c) :
    eighteenOutsideHooks G u a=∅ := by
  obtain ⟨q,i,hbshape⟩ := eighteen_actual_triple_classification hb h14 h16 u hu b hbout hb3
  obtain ⟨r,k,hcshape⟩ := eighteen_actual_triple_classification hb h14 h16 u hu c hcout hc3
  have hs1 := eighteen_triple_neighbor_subset hb h14 h16 u hu a b ha hbout hba q i hbshape
  have hs2 := eighteen_triple_neighbor_subset hb h14 h16 u hu a c ha hcout hca r k hcshape
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro j hj
  have he1 := Finset.mem_singleton.mp (hs1 hj)
  have he2 := Finset.mem_singleton.mp (hs2 hj)
  have hp : (q,i)=(r,k) := eighteenTripleCompatibleIndex_injective (he1.symm.trans he2)
  have hqr : q=r := congrArg Prod.fst hp
  have hik : i=k := congrArg Prod.snd hp
  apply hne
  rw [hbshape,hcshape,hqr,hik]

end TaskH.Seven.BP

#print axioms TaskH.Seven.BP.eighteenTripleCompatibleIndex
#print axioms TaskH.Seven.BP.eighteenTripleCompatibleIndex_injective
#print axioms TaskH.Seven.BP.eighteen_three_ear_endpoint_parity
#print axioms TaskH.Seven.BP.eighteen_even_triple_neighbor_subset
#print axioms TaskH.Seven.BP.eighteen_odd_triple_neighbor_subset
#print axioms TaskH.Seven.BP.eighteen_triple_neighbor_subset
#print axioms TaskH.Seven.BP.eighteen_neighbor_of_triple_is_low
#print axioms TaskH.Seven.BP.eighteen_distinct_triples_common_neighbor_zero
