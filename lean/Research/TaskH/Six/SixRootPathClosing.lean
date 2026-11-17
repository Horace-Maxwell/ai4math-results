import Research.TaskH.Six.SixRootPaths

/-!
A root/endpoint degree-sum surplus closes each actual simple four-edge
path by an unused common neighbor. Genuine edge-set orientation uniqueness
then bounds each resulting cycle fiber by two.
-/

set_option autoImplicit false

universe u

namespace TaskH.Six

open SimpleGraph _root_.TaskH.Challenge
open scoped Classical

variable {V : Type u} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem four_common_neighbors_of_degree_sum (v z : V) (δ : ℕ)
    (hz : δ ≤ G.degree z) (hsum : Fintype.card V + 4 ≤ G.degree v + δ) :
    4 ≤ ((G.neighborFinset v) ∩ (G.neighborFinset z)).card := by
  classical
  have he := Finset.card_union_add_card_inter (G.neighborFinset v) (G.neighborFinset z)
  have hu := Finset.card_le_univ ((G.neighborFinset v) ∪ (G.neighborFinset z))
  rw [G.card_neighborFinset_eq_degree, G.card_neighborFinset_eq_degree] at he
  omega

noncomputable def rootClosingHexagon (v : V) (f : Fin 5 → V) (z : V) : Fin 6 → V :=
  ![v, f 1, f 2, f 3, f 4, z]

omit [Fintype V] [DecidableRel G.Adj] in
theorem rootClosingHexagon_isHexagon (v : V) (f : Fin 5 → V)
    (hf : IsRootFourPath G v f) (z : V)
    (hzv : G.Adj v z) (hzend : G.Adj (f 4) z)
    (hz : ∀ i : Fin 5, z ≠ f i) : IsHexagon G (rootClosingHexagon v f z) := by
  have h0 := hf.1
  have hfi := hf.2.1
  have h01 : G.Adj v (f 1) := by simpa only [h0] using hf.2.2.1
  have hsnoc : rootClosingHexagon v f z = Fin.snoc f z := by
    funext i
    fin_cases i <;> simp [rootClosingHexagon, Fin.snoc, h0] <;> rfl
  refine ⟨?_, h01, hf.2.2.2.1, hf.2.2.2.2.1, hf.2.2.2.2.2, hzend, hzv.symm⟩
  rw [hsnoc]
  apply Fin.snoc_injective_of_injective hfi
  rintro ⟨i, hi⟩
  exact hz i hi.symm

theorem root_four_path_has_closing_cycle (δ : ℕ)
    (hmin : ∀ x : V, δ ≤ G.degree x) (v : V)
    (hsum : Fintype.card V + 4 ≤ G.degree v + δ)
    (f : Fin 5 → V) (hf : IsRootFourPath G v f) :
    ∃ p : G.Walk v v, p.IsCycle ∧ p.length = 6 ∧
      ∀ i : Fin 5, p.getVert i.val = f i := by
  classical
  let C := (G.neighborFinset v) ∩ (G.neighborFinset (f 4))
  have hC : 4 ≤ C.card := four_common_neighbors_of_degree_sum v (f 4) δ (hmin _) hsum
  let I : Finset V := {f 1, f 2, f 3}
  have hI : I.card ≤ 3 := by
    have h1 := Finset.card_insert_le (f 1) ({f 2, f 3} : Finset V)
    have h2 := Finset.card_insert_le (f 2) ({f 3} : Finset V)
    simp only [Finset.card_singleton] at h2
    change ({f 1, f 2, f 3} : Finset V).card ≤ 3
    omega
  have hlt : I.card < C.card := by omega
  obtain ⟨z, hzC, hzI⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
  have hzv : G.Adj v z := (G.mem_neighborFinset v z).mp (Finset.mem_inter.mp hzC).1
  have hzend : G.Adj (f 4) z :=
    (G.mem_neighborFinset (f 4) z).mp (Finset.mem_inter.mp hzC).2
  have hz : ∀ i : Fin 5, z ≠ f i := by
    intro i
    fin_cases i
    · change z ≠ f 0
      rw [hf.1]
      exact hzv.ne.symm
    · intro he
      exact hzI (Finset.mem_insert.mpr (Or.inl he))
    · intro he
      exact hzI (Finset.mem_insert.mpr
        (Or.inr (Finset.mem_insert.mpr (Or.inl he))))
    · intro he
      exact hzI (Finset.mem_insert.mpr
        (Or.inr (Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr he)))))
    · exact hzend.ne.symm
  let g := rootClosingHexagon v f z
  have hg : IsHexagon G g := rootClosingHexagon_isHexagon v f hf z hzv hzend hz
  let p : G.Walk v v := hexagonWalk G g hg.2.1 hg.2.2.1 hg.2.2.2.1
    hg.2.2.2.2.1 hg.2.2.2.2.2.1 hg.2.2.2.2.2.2
  refine ⟨p, hexagonWalk_isCycle G g hg.1 hg.2.1 hg.2.2.1 hg.2.2.2.1
    hg.2.2.2.2.1 hg.2.2.2.2.2.1 hg.2.2.2.2.2.2, rfl, ?_⟩
  intro i
  fin_cases i
  · exact hf.1.symm
  · rfl
  · rfl
  · rfl
  · rfl

/-- Relation between an actual rooted path and an actual genuine six-cycle. -/
def RootFourCycleRel (v : V) (f : Fin 5 → V) (s : Finset (Sym2 V)) : Prop :=
  ∃ p : G.Walk v v, p.IsCycle ∧ p.length = 6 ∧ p.edgeSet = (s : Set (Sym2 V)) ∧
    ∀ i : Fin 5, p.getVert i.val = f i

theorem rootFourCycleRel_fiber_le_two (v : V) (s : Finset (Sym2 V)) :
    ((rootFourPaths G v).filter (fun f => RootFourCycleRel (G := G) v f s)).card ≤ 2 := by
  classical
  let A := (rootFourPaths G v).filter (fun f => RootFourCycleRel (G := G) v f s)
  change A.card ≤ 2
  by_cases hn : A.Nonempty
  · obtain ⟨f, hf⟩ := hn
    obtain ⟨p, hp, _hlen, hps, _hpf⟩ := (Finset.mem_filter.mp hf).2
    let a : Fin 5 → V := fun i => p.getVert i.val
    let b : Fin 5 → V := fun i => p.reverse.getVert i.val
    have hsub : A ⊆ {a, b} := by
      intro g hg
      obtain ⟨q, hq, _hqlen, hqs, hqg⟩ := (Finset.mem_filter.mp hg).2
      obtain hdir | hdir := CycleOrientation.cycle_eq_or_reverse hp hq (hps.trans hqs.symm)
      · apply Finset.mem_insert.mpr
        left
        funext i
        exact (hqg i).symm.trans (congrArg (fun r : G.Walk v v => r.getVert i.val) hdir)
      · apply Finset.mem_insert.mpr
        right
        apply Finset.mem_singleton.mpr
        funext i
        exact (hqg i).symm.trans (congrArg (fun r : G.Walk v v => r.getVert i.val) hdir)
    have hh := Finset.card_le_card hsub
    have hp := Finset.card_insert_le a ({b} : Finset (Fin 5 → V))
    simp only [Finset.card_singleton] at hp
    omega
  · rw [Finset.not_nonempty_iff_eq_empty.mp hn]
    simp

theorem rootFourPaths_card_le_two_cycleDegree (δ : ℕ)
    (hmin : ∀ x : V, δ ≤ G.degree x) (v : V)
    (hsum : Fintype.card V + 4 ≤ G.degree v + δ) :
    (rootFourPaths G v).card ≤ 2 * cycleDegree G v := by
  classical
  let A := rootFourPaths G v
  let C := throughFinset G v
  let R : (Fin 5 → V) → Finset (Sym2 V) → Prop := RootFourCycleRel (G := G) v
  have hrow : ∀ f ∈ A, 1 ≤ (C.filter (R f)).card := by
    intro f hf
    obtain ⟨p, hp, hlen, hpf⟩ := root_four_path_has_closing_cycle δ hmin v hsum f
      (mem_rootFourPaths_spec v f hf)
    have hm : p.edges.toFinset ∈ C.filter (R f) := by
      apply Finset.mem_filter.mpr
      constructor
      · apply (mem_throughFinset p.edges.toFinset v).mpr
        refine ⟨(Basics.cycle_edges_mem_modCycleEdgeSets_iff hp).mpr ?_, ?_⟩
        · simpa only [hlen] using dvd_refl 6
        · exact (cycleContains_edges_toFinset_iff p hp.not_nil v).mpr p.start_mem_support
      · exact ⟨p, hp, hlen, p.coe_edges_toFinset.symm, hpf⟩
    have hpos := Finset.card_pos.mpr ⟨p.edges.toFinset, hm⟩
    omega
  have hcol : ∀ s ∈ C, (A.filter (fun f => R f s)).card ≤ 2 := by
    intro s _hs
    exact rootFourCycleRel_fiber_le_two v s
  calc
    (rootFourPaths G v).card = ∑ _f ∈ A, 1 := by simp [A]
    _ ≤ ∑ f ∈ A, (C.filter (R f)).card := Finset.sum_le_sum hrow
    _ = ∑ s ∈ C, (A.filter (fun f => R f s)).card :=
      FiniteBudget.relation_double_count A C R
    _ ≤ ∑ _s ∈ C, 2 := Finset.sum_le_sum hcol
    _ = 2 * cycleDegree G v := by simp [C, cycleDegree, Nat.mul_comm]

end TaskH.Six

#print axioms TaskH.Six.four_common_neighbors_of_degree_sum
#print axioms TaskH.Six.rootClosingHexagon
#print axioms TaskH.Six.rootClosingHexagon_isHexagon
#print axioms TaskH.Six.root_four_path_has_closing_cycle
#print axioms TaskH.Six.RootFourCycleRel
#print axioms TaskH.Six.rootFourCycleRel_fiber_le_two
#print axioms TaskH.Six.rootFourPaths_card_le_two_cycleDegree
