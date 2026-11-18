import Research.TaskH.Fan.ComponentRootBlock
import Research.TaskH.Fan.Identification

/-! The actual root-deleted component containing the retained endpoint, with its actual block. -/
set_option autoImplicit false
universe u
namespace TaskH.Fan
open SimpleGraph
variable {V : Type u}

def identificationYComponent (G : SimpleGraph V) (S : Set V) (y : {v : V // v ∉ S}) :
    ((identificationGraph G S).induce {v : IdentificationVertex S | v ≠ none}).ConnectedComponent :=
  ((identificationGraph G S).induce {v : IdentificationVertex S | v ≠ none}).connectedComponentMk
    ⟨some y, by intro he; cases he⟩

def identificationYBlockSet (G : SimpleGraph V) (S : Set V) (y : {v : V // v ∉ S}) :
    Set (IdentificationVertex S) :=
  componentRootSet (identificationGraph G S) none (identificationYComponent G S y)

theorem identificationYBlock_root_mem (G : SimpleGraph V) (S : Set V) (y : {v : V // v ∉ S}) :
    none ∈ identificationYBlockSet G S y := Or.inl rfl

theorem identificationYBlock_endpoint_mem (G : SimpleGraph V) (S : Set V) (y : {v : V // v ∉ S}) :
    some y ∈ identificationYBlockSet G S y := by
  apply Or.inr
  refine ⟨?_, ?_⟩
  · intro he
    cases he
  · rfl

theorem twoConnected_mono [Fintype V] (A B : SimpleGraph V) (hAB : A ≤ B)
    (hA : TwoConnected A) : TwoConnected B := by
  refine ⟨hA.1, Connected.mono hAB hA.2.1, ?_⟩
  intro z
  have hd : A.induce {v | v ≠ z} ≤ B.induce {v | v ≠ z} := fun _ _ e => hAB e
  exact Connected.mono hd (hA.2.2 z)

theorem identificationYBlock_rooted (G : SimpleGraph V) (S : Set V)
    (y : {v : V // v ∉ S}) [Fintype (IdentificationVertex S)]
    [Fintype (identificationYBlockSet G S y)]
    (hT : 2 ≤ (identificationYComponent G S y).supp.ncard)
    (hK : (identificationGraph G S).Connected)
    (hd : ∀ w : IdentificationVertex S, w ≠ none →
      ((identificationGraph G S).induce {v | v ≠ w}).Connected) :
    RootedTwoConnected ((identificationGraph G S).induce (identificationYBlockSet G S y))
      (⟨none, identificationYBlock_root_mem G S y⟩ : identificationYBlockSet G S y)
      (⟨some y, identificationYBlock_endpoint_mem G S y⟩ : identificationYBlockSet G S y) := by
  let _ : Fintype (componentRootSet (identificationGraph G S) none (identificationYComponent G S y)) :=
    ‹Fintype (identificationYBlockSet G S y)›
  have hB := componentRoot_twoConnected (identificationGraph G S) none
    (identificationYComponent G S y) hT hK hd
  have hne : (⟨none, identificationYBlock_root_mem G S y⟩ : identificationYBlockSet G S y) ≠
      ⟨some y, identificationYBlock_endpoint_mem G S y⟩ := by
    intro he
    have hh : (none : IdentificationVertex S) = some y := congrArg Subtype.val he
    cases hh
  exact ⟨hne, twoConnected_mono _ _ le_sup_left hB⟩

theorem identificationYBlock_degree (G : SimpleGraph V) (S : Set V) (y : {v : V // v ∉ S})
    (hd : NonrootDegreeAtLeast (identificationGraph G S) none (some y) 3) :
    NonrootDegreeAtLeast ((identificationGraph G S).induce (identificationYBlockSet G S y))
      (⟨none, identificationYBlock_root_mem G S y⟩ : identificationYBlockSet G S y)
      (⟨some y, identificationYBlock_endpoint_mem G S y⟩ : identificationYBlockSet G S y) 3 := by
  intro t htn hty
  have htn' : t.1 ≠ none := fun he => htn (Subtype.ext he)
  have hty' : t.1 ≠ some y := fun he => hty (Subtype.ext he)
  have heq := rootedSet_neighbor_ncard (identificationGraph G S) (identificationYBlockSet G S y)
    none (componentRootSet_closed (identificationGraph G S) none (identificationYComponent G S y)) t htn'
  rw [← heq]
  exact hd t.1 htn' hty'

#print axioms identificationYComponent
#print axioms identificationYBlockSet
#print axioms identificationYBlock_root_mem
#print axioms identificationYBlock_endpoint_mem
#print axioms twoConnected_mono
#print axioms identificationYBlock_rooted
#print axioms identificationYBlock_degree
end TaskH.Fan
