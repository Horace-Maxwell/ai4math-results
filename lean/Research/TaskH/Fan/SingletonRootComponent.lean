import Research.TaskH.Fan.Challenge

/-! Full neighbor data from an actual singleton root-deleted component. -/
set_option autoImplicit false
universe u
namespace TaskH.Fan
open SimpleGraph
variable {V : Type u}

theorem singleton_deleted_component_neighbors (G : SimpleGraph V) (z y : V)
    (hyz : y ≠ z)
    (hc : ((G.induce {v : V | v ≠ z}).connectedComponentMk ⟨y, hyz⟩).supp.ncard = 1) :
    ∀ w : V, G.Adj y w → w = z := by
  classical
  let C := (G.induce {v : V | v ≠ z}).connectedComponentMk ⟨y, hyz⟩
  obtain ⟨a, ha⟩ := Set.ncard_eq_one.mp hc
  have hyC : (⟨y, hyz⟩ : {v : V // v ≠ z}) ∈ C.supp := rfl
  have hya : (⟨y, hyz⟩ : {v : V // v ≠ z}) = a := by
    exact Set.mem_singleton_iff.mp (ha ▸ hyC)
  intro w e
  by_contra hw
  have hwC : (⟨w, hw⟩ : {v : V // v ≠ z}) ∈ C.supp :=
    C.mem_supp_of_adj_mem_supp hyC e
  have hwa : (⟨w, hw⟩ : {v : V // v ≠ z}) = a :=
    Set.mem_singleton_iff.mp (ha ▸ hwC)
  have hwy : w = y := congrArg Subtype.val (hwa.trans hya.symm)
  exact e.ne hwy.symm

theorem singleton_deleted_component_neighborSet (G : SimpleGraph V) (z y : V)
    (hyz : y ≠ z) (hG : G.Connected)
    (hc : ((G.induce {v : V | v ≠ z}).connectedComponentMk ⟨y, hyz⟩).supp.ncard = 1) :
    G.neighborSet y = {z} := by
  have hn := singleton_deleted_component_neighbors G z y hyz hc
  obtain ⟨p⟩ := hG y z
  have ep := p.adj_snd (p.not_nil_of_ne hyz)
  have hpz : p.snd = z := hn _ ep
  have eyz : G.Adj y z := hpz ▸ ep
  ext w
  constructor
  · intro ew
    exact Set.mem_singleton_iff.mpr (hn w ew)
  · intro hw
    exact (Set.mem_singleton_iff.mp hw).symm ▸ eyz

theorem singleton_deleted_component_neighbor_ncard (G : SimpleGraph V) (z y : V)
    (hyz : y ≠ z) (hG : G.Connected)
    (hc : ((G.induce {v : V | v ≠ z}).connectedComponentMk ⟨y, hyz⟩).supp.ncard = 1) :
    (G.neighborSet y).ncard = 1 := by
  rw [singleton_deleted_component_neighborSet G z y hyz hG hc, Set.ncard_singleton]

theorem reachable_eq_of_isolated (G : SimpleGraph V) (r w : V)
    (hr : ∀ v : V, ¬G.Adj r v) (h : G.Reachable r w) : r = w := by
  obtain ⟨p⟩ := h
  cases p with
  | nil => rfl
  | cons e p => exact False.elim (hr _ e)

#print axioms singleton_deleted_component_neighbors
#print axioms singleton_deleted_component_neighborSet
#print axioms singleton_deleted_component_neighbor_ncard
#print axioms reachable_eq_of_isolated
end TaskH.Fan
