import Research.TaskH.Gao.CaseThreeCoreChoice
import Research.TaskH.Gao.CliqueCoreDegree

/-! The exact common-clique/three-anchor loss budget in the original Case3. -/
set_option autoImplicit false
universe u
namespace TaskH.Gao
open SimpleGraph
variable {V : Type u}

theorem case3_anchor_neighbors_at_most_one_of_root_adjacent [Finite V]
    (G : SimpleGraph V) (x p q v : V) (hi : G.IsIndepSet (G.neighborSet x))
    (exp : G.Adj x p) (exq : G.Adj x q) (exv : G.Adj x v) :
    (G.neighborSet v ∩ ({x, p, q} : Set V)).ncard ≤ 1 := by
  have hsub : G.neighborSet v ∩ ({x, p, q} : Set V) ⊆ {x} := by
    rintro z ⟨evz, hz⟩
    rcases hz with hzx | hzp | hzq
    · exact hzx
    · have evp : G.Adj v p := Eq.mp (congrArg (fun z : V => G.Adj v z) hzp) evz
      exact False.elim ((case3_common_neighbor_avoids_root G x p v hi exp evp.symm) exv)
    · have evq : G.Adj v q := Eq.mp (congrArg (fun z : V => G.Adj v z) hzq) evz
      exact False.elim ((case3_common_neighbor_avoids_root G x q v hi exq evq.symm) exv)
  simpa only [Set.ncard_singleton] using Set.ncard_le_ncard hsub

theorem case3_anchor_neighbors_at_most_two [Finite V]
    (G : SimpleGraph V) (x p q v : V) (hi : G.IsIndepSet (G.neighborSet x))
    (exp : G.Adj x p) (exq : G.Adj x q) (hpq : p ≠ q) :
    (G.neighborSet v ∩ ({x, p, q} : Set V)).ncard ≤ 2 := by
  by_cases exv : G.Adj x v
  · have hh := case3_anchor_neighbors_at_most_one_of_root_adjacent G x p q v hi exp exq exv
    omega
  · have hsub : G.neighborSet v ∩ ({x, p, q} : Set V) ⊆ {p, q} := by
      rintro z ⟨evz, hz⟩
      rcases hz with hzx | hzp | hzq
      · have evx : G.Adj v x := Eq.mp (congrArg (fun z : V => G.Adj v z) hzx) evz
        exact False.elim (exv evx.symm)
      · exact Or.inl hzp
      · exact Or.inr hzq
    have hh := Set.ncard_le_ncard hsub
    rw [Set.ncard_pair hpq] at hh
    exact hh

theorem case3_anchor_neighbors_at_most_one_of_not_both [Finite V]
    (G : SimpleGraph V) (x p q v : V) (hi : G.IsIndepSet (G.neighborSet x))
    (exp : G.Adj x p) (exq : G.Adj x q)
    (hboth : ¬(G.Adj v p ∧ G.Adj v q)) :
    (G.neighborSet v ∩ ({x, p, q} : Set V)).ncard ≤ 1 := by
  by_cases exv : G.Adj x v
  · exact case3_anchor_neighbors_at_most_one_of_root_adjacent G x p q v hi exp exq exv
  · by_cases evp : G.Adj v p
    · have hsub : G.neighborSet v ∩ ({x, p, q} : Set V) ⊆ {p} := by
        rintro z ⟨evz, hz⟩
        rcases hz with hzx | hzp | hzq
        · have evx : G.Adj v x := Eq.mp (congrArg (fun z : V => G.Adj v z) hzx) evz
          exact False.elim (exv evx.symm)
        · exact hzp
        · have evq : G.Adj v q := Eq.mp (congrArg (fun z : V => G.Adj v z) hzq) evz
          exact False.elim (hboth ⟨evp, evq⟩)
      simpa only [Set.ncard_singleton] using Set.ncard_le_ncard hsub
    · have hsub : G.neighborSet v ∩ ({x, p, q} : Set V) ⊆ {q} := by
        rintro z ⟨evz, hz⟩
        rcases hz with hzx | hzp | hzq
        · have evx : G.Adj v x := Eq.mp (congrArg (fun z : V => G.Adj v z) hzx) evz
          exact False.elim (exv evx.symm)
        · exact False.elim (evp (Eq.mp (congrArg (fun z : V => G.Adj v z) hzp) evz))
        · exact hzq
      simpa only [Set.ncard_singleton] using Set.ncard_le_ncard hsub

theorem case3_actual_core_loss_budget [Finite V] (G : SimpleGraph V)
    (x y p q : V) (K : Set V)
    (hK : Maximal (fun L : Set V => G.IsClique L ∧ L ⊆ case3CoreDomain G x y p q) K)
    (ht : 2 ≤ K.ncard) (hi : G.IsIndepSet (G.neighborSet x))
    (exp : G.Adj x p) (exq : G.Adj x q) (hpq : p ≠ q)
    (v : V) (hvx : v ≠ x) (hvy : v ≠ y) (hvp : v ≠ p) (hvq : v ≠ q)
    (hvK : v ∉ K) :
    (G.neighborSet v ∩ (K ∪ ({x, p, q} : Set V))).ncard ≤
      K.ncard + collapsedNeighborCount G K v := by
  classical
  have hdis : Disjoint K ({x, p, q} : Set V) := by
    apply Set.disjoint_left.mpr
    intro z hz hzA
    have hu := hK.1.2 hz
    rcases hzA with hzx | hzp | hzq
    · exact hu.1 hzx
    · exact hu.2.2.1 hzp
    · exact hu.2.2.2.1 hzq
  have heq : G.neighborSet v ∩ (K ∪ ({x, p, q} : Set V)) =
      (G.neighborSet v ∩ K) ∪ (G.neighborSet v ∩ ({x, p, q} : Set V)) := by
    ext z
    constructor
    · rintro ⟨ez, hz | hz⟩
      · exact Or.inl ⟨ez, hz⟩
      · exact Or.inr ⟨ez, hz⟩
    · rintro (hz | hz)
      · exact ⟨hz.1, Or.inl hz.2⟩
      · exact ⟨hz.1, Or.inr hz.2⟩
  have hd : Disjoint (G.neighborSet v ∩ K) (G.neighborSet v ∩ ({x, p, q} : Set V)) := by
    apply Set.disjoint_left.mpr
    intro z hzK hzA
    exact Set.disjoint_left.mp hdis hzK.2 hzA.2
  rw [heq, Set.ncard_union_eq hd]
  have hKcard : (G.neighborSet v ∩ K).ncard ≤ K.ncard :=
    Set.ncard_le_ncard Set.inter_subset_right
  have hAcard := case3_anchor_neighbors_at_most_two G x p q v hi exp exq hpq
  by_cases htouch : ∃ z ∈ K, G.Adj v z
  · have hb : collapsedNeighborCount G K v = 1 := by
      unfold collapsedNeighborCount
      exact ite_eq_left htouch
    rw [hb]
    by_cases hboth : G.Adj v p ∧ G.Adj v q
    · have hvU : v ∈ case3CoreDomain G x y p q :=
        ⟨hvx, hvy, hvp, hvq, hboth.1.symm, hboth.2.symm⟩
      have hstrict := case3_core_external_neighbors_lt G x y p q K hK v hvU hvK
      omega
    · have hsmall := case3_anchor_neighbors_at_most_one_of_not_both G x p q v hi exp exq hboth
      omega
  · have hb : collapsedNeighborCount G K v = 0 := by
      unfold collapsedNeighborCount
      exact ite_eq_right htouch
    have hem : G.neighborSet v ∩ K = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      rintro z ⟨evz, hzK⟩
      exact htouch ⟨z, hzK, evz⟩
    rw [hem, Set.ncard_empty, hb]
    omega

theorem case3_block_K_quotient_degree [Finite V] (G : SimpleGraph V)
    (x y p q : V) (K B : Set V) (b : V) (k : ℕ)
    (hK : Maximal (fun L : Set V => G.IsClique L ∧ L ⊆ case3CoreDomain G x y p q) K)
    (ht : 2 ≤ K.ncard) (htk : K.ncard ≤ k)
    (hi : G.IsIndepSet (G.neighborSet x))
    (exp : G.Adj x p) (exq : G.Adj x q) (hpq : p ≠ q)
    (hBC : Disjoint B (K ∪ ({x, p, q} : Set V)))
    (hBy : y ∈ B → y = b)
    (hcover : ∀ v ∈ B, v ≠ b → ∀ z, G.Adj v z → z ∈ B ∨ z ∈ K ∪ ({x, p, q} : Set V))
    (hd : TaskH.Fan.NonrootDegreeAtLeast G x y (k + 1))
    (v : B) (hvb : v.1 ≠ b) :
    k - K.ncard + 1 ≤
      ((regionIdentificationGraph G B (cliqueBlockBoundary G B K x b)).neighborSet
        (some (regionRetainedVertex B (cliqueBlockBoundary G B K x b)
          (cliqueBlock_boundary_disjoint G B K x b
            (Set.disjoint_left.mpr (fun _ hv hK' => Set.disjoint_left.mp hBC hv (Or.inl hK')))) v))).ncard := by
  classical
  let S := cliqueBlockBoundary G B K x b
  have hBK : Disjoint B K :=
    Set.disjoint_left.mpr (fun _ hv hK' => Set.disjoint_left.mp hBC hv (Or.inl hK'))
  have hBS : Disjoint B S := cliqueBlock_boundary_disjoint G B K x b hBK
  have hvx : v.1 ≠ x := by
    intro he
    exact Set.disjoint_left.mp hBC v.2 (Or.inr (Or.inl he))
  have hvp : v.1 ≠ p := by
    intro he
    exact Set.disjoint_left.mp hBC v.2 (Or.inr (Or.inr (Or.inl he)))
  have hvq : v.1 ≠ q := by
    intro he
    exact Set.disjoint_left.mp hBC v.2 (Or.inr (Or.inr (Or.inr he)))
  have hvy : v.1 ≠ y := by
    intro he
    have hyB : y ∈ B := Eq.mp (congrArg (fun z : V => z ∈ B) he) v.2
    exact hvb (he.trans (hBy hyB))
  have hvK : v.1 ∉ K := fun hv => Set.disjoint_left.mp hBK v.2 hv
  have hcap := case3_actual_core_loss_budget G x y p q K hK ht hi exp exq hpq
    v.1 hvx hvy hvp hvq hvK
  have hpart := disjoint_region_neighbor_partition G B (K ∪ ({x, p, q} : Set V)) hBC
    v.1 (hcover v.1 v.2 hvb)
  have hquot := regionIdentification_neighbor_ncard G B S hBS v
  have hbits : collapsedNeighborCount G S v.1 = collapsedNeighborCount G K v.1 := by
    have hiff : (∃ z ∈ S, G.Adj v.1 z) ↔ ∃ z ∈ K, G.Adj v.1 z := by
      constructor
      · rintro ⟨z, hz, evz⟩
        exact ⟨z, hz.1, evz⟩
      · rintro ⟨z, hzK, evz⟩
        have hzx : z ≠ x := (hK.1.2 hzK).1
        exact ⟨z, ⟨hzK, hzx, v.1, v.2, hvb, evz⟩, evz⟩
    unfold collapsedNeighborCount
    rw [hiff]
  rw [hbits] at hquot
  have hOrig := hd v.1 hvx hvy
  change k - K.ncard + 1 ≤
    ((regionIdentificationGraph G B S).neighborSet (some (regionRetainedVertex B S hBS v))).ncard
  omega

#print axioms case3_anchor_neighbors_at_most_one_of_root_adjacent
#print axioms case3_anchor_neighbors_at_most_two
#print axioms case3_anchor_neighbors_at_most_one_of_not_both
#print axioms case3_actual_core_loss_budget
#print axioms case3_block_K_quotient_degree
end TaskH.Gao
