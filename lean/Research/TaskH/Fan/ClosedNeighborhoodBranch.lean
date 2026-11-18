import Research.TaskH.Fan.ClosedNeighborhoodQuotient
import Research.TaskH.Fan.IdentificationYComponent
import Research.TaskH.Fan.ClosedNeighborhoodLift

/-! The actual chosen component of K-none is used, never supplied as an original premise. -/
set_option autoImplicit false
universe u
namespace TaskH.Fan
open SimpleGraph
variable {V : Type u}

theorem closedNeighborhood_large_component_branch [Fintype V] (G : SimpleGraph V)
    (x y : V) (hG : TwoConnected G) (hxy : x ≠ y) (hno : ¬G.Adj x y)
    (hfour : ¬rootFourCycleAvoiding G x y) (hdeg : NonrootDegreeAtLeast G x y 3)
    (hT : 2 ≤ (identificationYComponent G (closedRootNeighborhood G x)
      ⟨y, closedRootNeighborhood_other_root_out G x y hxy hno⟩).supp.ncard)
    (ih : ∀ (W : Type u) [Fintype W] (J : SimpleGraph W) (s t : W),
      Fintype.card W < Fintype.card V → RootedTwoConnected J s t →
        NonrootDegreeAtLeast J s t 3 → HasTwoPaths J s t) : HasTwoPaths G x y := by
  classical
  let S := closedRootNeighborhood G x
  let oy : {v : V // v ∉ S} := ⟨y, closedRootNeighborhood_other_root_out G x y hxy hno⟩
  let K := identificationGraph G S
  let B := identificationYBlockSet G S oy
  let : Fintype {v : V // v ∉ S} := Fintype.ofFinite _
  let : Fintype B := Fintype.ofFinite _
  let zr : B := ⟨none, identificationYBlock_root_mem G S oy⟩
  let yr : B := ⟨some oy, identificationYBlock_endpoint_mem G S oy⟩
  have hK := closedNeighborhood_quotient_connected G hG x
  have hdK := closedNeighborhood_quotient_delete_retained G hG x
  have hroot := identificationYBlock_rooted G S oy hT hK hdK
  have hdegree := identificationYBlock_degree G S oy
    (closedNeighborhood_quotient_degree G x y hxy hno hfour hdeg)
  have hle : Fintype.card B ≤ Fintype.card (IdentificationVertex S) :=
    Fintype.card_subtype_le (fun v => v ∈ B)
  have hltK := closedNeighborhood_quotient_card G hG x y hxy
  have hlt : Fintype.card B < Fintype.card V := lt_of_le_of_lt hle hltK
  obtain ⟨p, q, hpq⟩ := ih B (K.induce B) zr yr hlt hroot hdegree
  let f : K.induce B →g K := (SimpleGraph.Embedding.induce B).toHom
  have hq : HasTwoPaths K none (some oy) :=
    ⟨p.map f, q.map f, twoPathWitness_map f Subtype.val_injective p q hpq⟩
  exact closedNeighborhood_two_path_lift G x oy hq

theorem counterexample_closed_component_small [Fintype V] (G : SimpleGraph V)
    (x y : V) (hG : TwoConnected G) (hxy : x ≠ y) (hno : ¬G.Adj x y)
    (hfour : ¬rootFourCycleAvoiding G x y) (hdeg : NonrootDegreeAtLeast G x y 3)
    (hbad : ¬HasTwoPaths G x y)
    (ih : ∀ (W : Type u) [Fintype W] (J : SimpleGraph W) (s t : W),
      Fintype.card W < Fintype.card V → RootedTwoConnected J s t →
        NonrootDegreeAtLeast J s t 3 → HasTwoPaths J s t) :
    (identificationYComponent G (closedRootNeighborhood G x)
      ⟨y, closedRootNeighborhood_other_root_out G x y hxy hno⟩).supp.ncard < 2 := by
  classical
  by_contra hs
  have hT : 2 ≤ (identificationYComponent G (closedRootNeighborhood G x)
      ⟨y, closedRootNeighborhood_other_root_out G x y hxy hno⟩).supp.ncard := by omega
  exact hbad (closedNeighborhood_large_component_branch G x y hG hxy hno hfour hdeg hT ih)

theorem counterexample_closed_component_card_one [Fintype V] (G : SimpleGraph V)
    (x y : V) (hG : TwoConnected G) (hxy : x ≠ y) (hno : ¬G.Adj x y)
    (hfour : ¬rootFourCycleAvoiding G x y) (hdeg : NonrootDegreeAtLeast G x y 3)
    (hbad : ¬HasTwoPaths G x y)
    (ih : ∀ (W : Type u) [Fintype W] (J : SimpleGraph W) (s t : W),
      Fintype.card W < Fintype.card V → RootedTwoConnected J s t →
        NonrootDegreeAtLeast J s t 3 → HasTwoPaths J s t) :
    (identificationYComponent G (closedRootNeighborhood G x)
      ⟨y, closedRootNeighborhood_other_root_out G x y hxy hno⟩).supp.ncard = 1 := by
  classical
  let S := closedRootNeighborhood G x
  let oy : {v : V // v ∉ S} := ⟨y, closedRootNeighborhood_other_root_out G x y hxy hno⟩
  let C := identificationYComponent G S oy
  have hnonempty : C.supp.Nonempty := ⟨⟨some oy, by intro he; cases he⟩, rfl⟩
  have hpos : 0 < C.supp.ncard := (Set.ncard_pos (s := C.supp)).mpr hnonempty
  have hsmall : C.supp.ncard < 2 :=
    counterexample_closed_component_small G x y hG hxy hno hfour hdeg hbad ih
  change C.supp.ncard = 1
  omega

#print axioms closedNeighborhood_large_component_branch
#print axioms counterexample_closed_component_small
#print axioms counterexample_closed_component_card_one
end TaskH.Fan
