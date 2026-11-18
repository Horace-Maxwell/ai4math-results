import Research.TaskH.Fan.AdjEqConnectivity
import Research.TaskH.Fan.Identification

/-!
Actual identification preserves connectivity, also after deleting any retained
vertex. The map sends an original edge to an edge or equality; it is never
called a graph homomorphism. The collapsed set need only be nonempty.
-/
set_option autoImplicit false
universe u
namespace TaskH.Fan
open SimpleGraph
variable {V : Type u}

theorem identification_map_adj_or_eq (G : SimpleGraph V) (S : Set V)
    {a b : V} (h : G.Adj a b) :
    identificationMap S a = identificationMap S b ∨
      (identificationGraph G S).Adj (identificationMap S a) (identificationMap S b) := by
  classical
  by_cases ha : a ∈ S
  · by_cases hb : b ∈ S
    · left
      simp only [identificationMap, dite_eq_left ha, dite_eq_left hb]
    · right
      simpa only [identificationMap, dite_eq_left ha, dite_eq_right hb,
        identificationGraph, identificationAdj] using
          (show ∃ s ∈ S, G.Adj s b from ⟨a, ha, h⟩)
  · by_cases hb : b ∈ S
    · right
      simpa only [identificationMap, dite_eq_right ha, dite_eq_left hb,
        identificationGraph, identificationAdj] using
          (show ∃ s ∈ S, G.Adj a s from ⟨b, hb, h⟩)
    · right
      simpa only [identificationMap, dite_eq_right ha, dite_eq_right hb,
        identificationGraph, identificationAdj] using h

theorem identification_map_surjective (S : Set V) (hS : S.Nonempty) :
    Function.Surjective (identificationMap S) := by
  classical
  intro b
  cases b with
  | none =>
    obtain ⟨a, ha⟩ := hS
    exact ⟨a, by simp only [identificationMap, dite_eq_left ha]⟩
  | some b =>
    exact ⟨b.1, by simp only [identificationMap, dite_eq_right b.2]⟩

theorem identification_connected (G : SimpleGraph V) (S : Set V)
    (hS : S.Nonempty) (hG : G.Connected) :
    (identificationGraph G S).Connected := by
  exact connected_of_surjective_adj_or_eq (identificationMap S)
    (identification_map_surjective S hS) (identification_map_adj_or_eq G S) hG

theorem identification_map_ne_some_of_ne (S : Set V) (r : V) (hr : r ∉ S)
    {a : V} (ha : a ≠ r) : identificationMap S a ≠ some ⟨r, hr⟩ := by
  classical
  by_cases haS : a ∈ S
  · intro he
    have hh : (none : IdentificationVertex S) = some ⟨r, hr⟩ := by
      simpa only [identificationMap, dite_eq_left haS] using he
    cases hh
  · intro he
    have hsub : (⟨a, haS⟩ : {v : V // v ∉ S}) = ⟨r, hr⟩ := by
      simpa only [identificationMap, dite_eq_right haS, Option.some.injEq] using he
    exact ha (congrArg Subtype.val hsub)

noncomputable def identificationDeleteMap (S : Set V) (r : V) (hr : r ∉ S) :
    {a : V // a ≠ r} → {b : IdentificationVertex S // b ≠ some ⟨r, hr⟩} :=
  fun a => ⟨identificationMap S a.1, identification_map_ne_some_of_ne S r hr a.2⟩

theorem identification_delete_map_surjective (S : Set V) (hS : S.Nonempty)
    (r : V) (hr : r ∉ S) : Function.Surjective (identificationDeleteMap S r hr) := by
  intro b
  obtain ⟨a, ha⟩ := identification_map_surjective S hS b.1
  have har : a ≠ r := by
    intro he
    subst a
    have hb : b.1 = some ⟨r, hr⟩ := by
      rw [← ha]
      classical
      simp only [identificationMap, dite_eq_right hr]
    exact b.2 hb
  exact ⟨⟨a, har⟩, Subtype.ext ha⟩

theorem identification_delete_map_adj_or_eq (G : SimpleGraph V) (S : Set V)
    (r : V) (hr : r ∉ S) {a b : {v : V // v ≠ r}}
    (h : (G.induce {v | v ≠ r}).Adj a b) :
    identificationDeleteMap S r hr a = identificationDeleteMap S r hr b ∨
      ((identificationGraph G S).induce {v : IdentificationVertex S | v ≠ some ⟨r, hr⟩}).Adj
        (identificationDeleteMap S r hr a) (identificationDeleteMap S r hr b) := by
  rcases identification_map_adj_or_eq G S h with he | he
  · exact Or.inl (Subtype.ext he)
  · exact Or.inr he

theorem identification_delete_retained_connected (G : SimpleGraph V) (S : Set V)
    (hS : S.Nonempty) (r : V) (hr : r ∉ S)
    (hG : (G.induce {v | v ≠ r}).Connected) :
    ((identificationGraph G S).induce {v : IdentificationVertex S | v ≠ some ⟨r, hr⟩}).Connected := by
  exact connected_of_surjective_adj_or_eq (identificationDeleteMap S r hr)
    (identification_delete_map_surjective S hS r hr)
    (identification_delete_map_adj_or_eq G S r hr) hG

#print axioms identification_map_adj_or_eq
#print axioms identification_map_surjective
#print axioms identification_connected
#print axioms identification_map_ne_some_of_ne
#print axioms identificationDeleteMap
#print axioms identification_delete_map_surjective
#print axioms identification_delete_map_adj_or_eq
#print axioms identification_delete_retained_connected
end TaskH.Fan
