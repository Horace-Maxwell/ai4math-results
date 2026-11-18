import Research.TaskH.Gao.GraphIsoTwoConnected
import Research.TaskH.Gao.CliqueCoreDegree
import Research.TaskH.Gao.OneRootExtension

/-! The actual exterior of G[B union S]/S is the real induced graph on B. -/
set_option autoImplicit false
universe u
namespace TaskH.Gao
open SimpleGraph TaskH.Fan
variable {V : Type u}

def regionExteriorGraphIso (G : SimpleGraph V) (B S : Set V) (hBS : Disjoint B S) :
    (G.induce (B ∪ S)).induce {w : (B ∪ S : Set V) | w.1 ∉ S} ≃g G.induce B where
  toEquiv := regionOutsideEquiv B S hBS
  map_rel_iff' := by
    intro a b
    rfl

theorem regionExterior_twoConnected (G : SimpleGraph V) (B S : Set V)
    (hBS : Disjoint B S) [iB : Fintype B]
    [iO : Fintype {w : (B ∪ S : Set V) // w.1 ∉ S}]
    (hB : @TwoConnected B iB (G.induce B)) :
    @TwoConnected {w : (B ∪ S : Set V) // w.1 ∉ S} iO
      ((G.induce (B ∪ S)).induce {w : (B ∪ S : Set V) | w.1 ∉ S}) := by
  exact twoConnected_of_graphIso
    (V := B) (W := {w : (B ∪ S : Set V) // w.1 ∉ S}) (iV := iB) (iW := iO)
    (G.induce B) ((G.induce (B ∪ S)).induce {w : (B ∪ S : Set V) | w.1 ∉ S})
    (regionExteriorGraphIso G B S hBS).symm hB

local instance regionIdentificationFintype (B S : Set V)
    [iO : Fintype {w : (B ∪ S : Set V) // w.1 ∉ S}] :
    Fintype (IdentificationVertex {z : (B ∪ S : Set V) | z.1 ∈ S}) := by
  change Fintype (Option {w : (B ∪ S : Set V) // w.1 ∉ S})
  infer_instance

theorem regionIdentification_rooted_from_real_spoke (G : SimpleGraph V)
    (B S : Set V) (hBS : Disjoint B S) [iB : Fintype B]
    [iO : Fintype {w : (B ∪ S : Set V) // w.1 ∉ S}]
    (b w : B) (hB : @TwoConnected B iB (G.induce B))
    (hspoke : ∃ s ∈ S, G.Adj s w.1) (hwb : w ≠ b) :
    RootedTwoConnected
      (V := IdentificationVertex {z : (B ∪ S : Set V) | z.1 ∈ S})
      (regionIdentificationGraph G B S) none (some (regionRetainedVertex B S hBS b)) := by
  have hO := regionExterior_twoConnected G B S hBS (iB := iB) (iO := iO) hB
  have hreal : (regionIdentificationGraph G B S).Adj
      none (some (regionRetainedVertex B S hBS w)) := by
    obtain ⟨s, hs, hsw⟩ := hspoke
    change ∃ z ∈ ({z : (B ∪ S : Set V) | z.1 ∈ S} : Set (B ∪ S : Set V)),
      (G.induce (B ∪ S)).Adj z (regionRetainedVertex B S hBS w).1
    exact ⟨⟨s, Or.inr hs⟩, hs, hsw⟩
  have htags : regionRetainedVertex B S hBS w ≠ regionRetainedVertex B S hBS b := by
    intro he
    apply hwb
    apply Subtype.ext
    exact congrArg (fun z : {z : (B ∪ S : Set V) // z.1 ∉ S} => z.1.1) he
  exact @one_root_extension_rooted {z : (B ∪ S : Set V) // z.1 ∉ S} iO
    ((G.induce (B ∪ S)).induce {z : (B ∪ S : Set V) | z.1 ∉ S})
    (regionIdentificationGraph G B S)
    (regionRetainedVertex B S hBS b) (regionRetainedVertex B S hBS w)
    hO (fun _ _ => Iff.rfl) hreal htags

#print axioms regionExteriorGraphIso
#print axioms regionExterior_twoConnected
#print axioms regionIdentificationFintype
#print axioms regionIdentification_rooted_from_real_spoke
end TaskH.Gao
