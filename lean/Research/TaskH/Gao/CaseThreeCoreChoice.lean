import Research.TaskH.Gao.CliqueBoundaryBudget

/-! Actual finite maximal common-neighbor clique; not the full original Case3. -/
set_option autoImplicit false
universe u
namespace TaskH.Gao
open SimpleGraph
variable {V : Type u}

def case3CoreDomain (G : SimpleGraph V) (x y p q : V) : Set V :=
  {z | z ≠ x ∧ z ≠ y ∧ z ≠ p ∧ z ≠ q ∧ G.Adj p z ∧ G.Adj q z}

theorem case3CoreDomain_swap (G : SimpleGraph V) (x y p q : V) :
    case3CoreDomain G x y q p = case3CoreDomain G x y p q := by
  ext z
  constructor
  · rintro ⟨hzx, hzy, hzq, hzp, eqz, epz⟩
    exact ⟨hzx, hzy, hzp, hzq, epz, eqz⟩
  · rintro ⟨hzx, hzy, hzp, hzq, epz, eqz⟩
    exact ⟨hzx, hzy, hzq, hzp, eqz, epz⟩

theorem case3_actual_core_exists [Finite V] (G : SimpleGraph V) (x y p q a v : V)
    (ha : a ∈ case3CoreDomain G x y p q)
    (hv : v ∈ case3CoreDomain G x y p q) (hav : G.Adj a v) :
    ∃ K : Set V,
      Maximal (fun L : Set V => G.IsClique L ∧ L ⊆ case3CoreDomain G x y p q) K ∧
      a ∈ K ∧ v ∈ K ∧ 2 ≤ K.ncard := by
  classical
  let : Fintype V := Fintype.ofFinite _
  have hseed : G.IsClique ({a, v} : Set V) ∧
      ({a, v} : Set V) ⊆ case3CoreDomain G x y p q := by
    refine ⟨SimpleGraph.isClique_pair.mpr (fun _ => hav), ?_⟩
    intro z hz
    rcases Set.mem_insert_iff.mp hz with he | he
    · exact Eq.mpr (congrArg (fun z : V => z ∈ case3CoreDomain G x y p q) he) ha
    · have he' : z = v := he
      exact Eq.mpr (congrArg (fun z : V => z ∈ case3CoreDomain G x y p q) he') hv
  obtain ⟨K, hseedK, hmax⟩ := Finite.exists_le_maximal (α := Set V)
    (p := fun L : Set V => G.IsClique L ∧ L ⊆ case3CoreDomain G x y p q)
    (a := ({a, v} : Set V)) hseed
  have hc := Set.ncard_le_ncard hseedK
  rw [Set.ncard_pair hav.ne] at hc
  exact ⟨K, hmax, hseedK (Set.mem_insert a {v}),
    hseedK (Set.mem_insert_of_mem a (Set.mem_singleton v)), hc⟩

theorem case3_core_external_neighbors_lt [Finite V] (G : SimpleGraph V)
    (x y p q : V) (K : Set V)
    (hK : Maximal (fun L : Set V => G.IsClique L ∧ L ⊆ case3CoreDomain G x y p q) K)
    (v : V) (hv : v ∈ case3CoreDomain G x y p q) (hvK : v ∉ K) :
    (G.neighborSet v ∩ K).ncard < K.ncard := by
  refine Set.ncard_lt_ncard ?_ (Set.toFinite K)
  rw [Set.ssubset_def]
  refine ⟨Set.inter_subset_right, ?_⟩
  intro hall
  have hcl : G.IsClique (insert v K) :=
    (SimpleGraph.isClique_insert_of_notMem hvK).mpr
      ⟨hK.1.1, fun z hz => (hall hz).1⟩
  have hsub : insert v K ⊆ case3CoreDomain G x y p q := by
    intro z hz
    rcases Set.mem_insert_iff.mp hz with he | he
    · exact Eq.mpr (congrArg (fun z : V => z ∈ case3CoreDomain G x y p q) he) hv
    · exact hK.1.2 he
  have hback : insert v K ⊆ K := hK.2 ⟨hcl, hsub⟩ (Set.subset_insert v K)
  exact hvK (hback (Set.mem_insert v K))

theorem case3_common_neighbor_avoids_root (G : SimpleGraph V) (x p v : V)
    (hi : G.IsIndepSet (G.neighborSet x)) (exp : G.Adj x p) (epv : G.Adj p v) :
    ¬G.Adj x v := by
  intro exv
  exact hi exp exv epv.ne epv

#print axioms case3CoreDomain
#print axioms case3CoreDomain_swap
#print axioms case3_actual_core_exists
#print axioms case3_core_external_neighbors_lt
#print axioms case3_common_neighbor_avoids_root
end TaskH.Gao
