import Research.TaskH.Fan.Identification

/-! Exact retained-vertex degree under arbitrary one-set identification. -/
set_option autoImplicit false
universe u
namespace TaskH.Gao
open SimpleGraph TaskH.Fan
variable {V : Type u}

noncomputable def collapsedNeighborCount (G : SimpleGraph V) (S : Set V) (v : V) : ℕ := by
  classical
  exact if ∃ w ∈ S, G.Adj v w then 1 else 0

theorem identification_retained_neighbors_ncard (G : SimpleGraph V) (S : Set V)
    (v : {a : V // a ∉ S}) :
    (Option.some '' {w : {a : V // a ∉ S} | G.Adj v.1 w.1}).ncard =
      (G.neighborSet v.1 \ S).ncard := by
  rw [Set.ncard_image_of_injective _ (Option.some_injective _)]
  apply Set.ncard_congr (fun w _ => w.1)
  · intro w hw
    exact ⟨hw, w.2⟩
  · intro a b _ha _hb he
    exact Subtype.ext he
  · intro w hw
    exact ⟨⟨w, hw.2⟩, hw.1, rfl⟩

theorem identification_neighbors_with_boundary (G : SimpleGraph V) (S : Set V)
    (v : {a : V // a ∉ S}) (h : ∃ w ∈ S, G.Adj v.1 w) :
    (identificationGraph G S).neighborSet (some v) =
      insert none (Option.some '' {w : {a : V // a ∉ S} | G.Adj v.1 w.1}) := by
  ext w
  cases w <;> simp [identificationGraph, identificationAdj, h]

theorem identification_neighbors_without_boundary (G : SimpleGraph V) (S : Set V)
    (v : {a : V // a ∉ S}) (h : ¬∃ w ∈ S, G.Adj v.1 w) :
    (identificationGraph G S).neighborSet (some v) =
      Option.some '' {w : {a : V // a ∉ S} | G.Adj v.1 w.1} := by
  ext w
  cases w <;> simp [identificationGraph, identificationAdj, h]

theorem identification_neighbor_ncard_partition [Finite V] (G : SimpleGraph V)
    (S : Set V) (v : {a : V // a ∉ S}) :
    ((identificationGraph G S).neighborSet (some v)).ncard =
      (G.neighborSet v.1 \ S).ncard + collapsedNeighborCount G S v.1 := by
  classical
  have hn : (none : IdentificationVertex S) ∉
      Option.some '' {w : {a : V // a ∉ S} | G.Adj v.1 w.1} := by
    rintro ⟨w, _hw, he⟩
    cases he
  by_cases h : ∃ w ∈ S, G.Adj v.1 w
  · rw [identification_neighbors_with_boundary G S v h,
      Set.ncard_insert_of_notMem hn, identification_retained_neighbors_ncard]
    simp [collapsedNeighborCount, h]
  · rw [identification_neighbors_without_boundary G S v h,
      identification_retained_neighbors_ncard]
    simp [collapsedNeighborCount, h]

theorem identification_degree_balance [Finite V] (G : SimpleGraph V)
    (S : Set V) (v : {a : V // a ∉ S}) :
    ((identificationGraph G S).neighborSet (some v)).ncard +
        (G.neighborSet v.1 ∩ S).ncard =
      (G.neighborSet v.1).ncard + collapsedNeighborCount G S v.1 := by
  have hsplit := Set.ncard_inter_add_ncard_sdiff_eq_ncard (G.neighborSet v.1) S
  have hquot := identification_neighbor_ncard_partition G S v
  omega

theorem collapsedNeighborCount_le_inter [Finite V] (G : SimpleGraph V)
    (S : Set V) (v : V) : collapsedNeighborCount G S v ≤ (G.neighborSet v ∩ S).ncard := by
  classical
  by_cases h : ∃ w ∈ S, G.Adj v w
  · have hp : 0 < (G.neighborSet v ∩ S).ncard :=
      (Set.ncard_pos (Set.toFinite _)).mpr (by
        obtain ⟨w, hwS, hvw⟩ := h
        exact ⟨w, hvw, hwS⟩)
    have hc : collapsedNeighborCount G S v = 1 := by
      unfold collapsedNeighborCount
      exact ite_eq_left h
    omega
  · simp [collapsedNeighborCount, h]

theorem identification_exact_degree_loss [Finite V] (G : SimpleGraph V)
    (S : Set V) (v : {a : V // a ∉ S}) :
    (G.neighborSet v.1).ncard -
        ((identificationGraph G S).neighborSet (some v)).ncard =
      (G.neighborSet v.1 ∩ S).ncard - collapsedNeighborCount G S v.1 := by
  have hb := identification_degree_balance G S v
  have hi := collapsedNeighborCount_le_inter G S v.1
  omega

#print axioms collapsedNeighborCount
#print axioms identification_retained_neighbors_ncard
#print axioms identification_neighbors_with_boundary
#print axioms identification_neighbors_without_boundary
#print axioms identification_neighbor_ncard_partition
#print axioms identification_degree_balance
#print axioms collapsedNeighborCount_le_inter
#print axioms identification_exact_degree_loss
end TaskH.Gao
