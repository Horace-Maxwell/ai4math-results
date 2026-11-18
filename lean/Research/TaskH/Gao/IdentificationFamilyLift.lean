import Research.TaskH.Gao.FamilyOperations
import Research.TaskH.Fan.IdentificationPathLift

/-! Simultaneous actual lifts have independently chosen boundary endpoints. -/
set_option autoImplicit false
universe u
namespace TaskH.Gao
open SimpleGraph TaskH.Fan
variable {V : Type u}

def EndpointPathFamily (G : SimpleGraph V) (k a d : ℕ)
    (s t : Fin k → V) (p : ∀ i, G.Walk (s i) (t i)) : Prop :=
  2 ≤ a ∧ (d = 1 ∨ d = 2) ∧ ∀ i, (p i).IsPath ∧ (p i).length = a + i.val * d

theorem identification_family_lift (G : SimpleGraph V) (S : Set V)
    (v : {w : V // w ∉ S}) (k a d : ℕ)
    (p : Fin k → (identificationGraph G S).Walk none (some v))
    (hp : AdmissiblePathFamily (identificationGraph G S) none (some v) k a d p) :
    ∃ s : Fin k → V, ∃ q : ∀ i, G.Walk (s i) v.1,
      (∀ i, s i ∈ S) ∧ EndpointPathFamily G k a d s (fun _ => v.1) q ∧
      (∀ i, (q i).length = (p i).length) ∧
      ∀ i w, w ∈ (q i).support → w = s i ∨ w ∉ S := by
  classical
  have h : ∀ i : Fin k, ∃ s ∈ S, ∃ q : G.Walk s v.1,
      q.IsPath ∧ q.length = (p i).length ∧
        ∀ w ∈ q.support, w = s ∨ w ∉ S := by
    intro i
    exact identification_path_lift G S v (p i) (hp.2.2 i).1
  choose s hs q hq hlen hsupp using h
  refine ⟨s, q, hs, ⟨hp.1, hp.2.1, ?_⟩, hlen, hsupp⟩
  intro i
  exact ⟨hq i, (hlen i).trans (hp.2.2 i).2⟩

theorem identification_family_lift_to_root (G : SimpleGraph V) (S : Set V)
    (u : {w : V // w ∉ S}) (k a d : ℕ)
    (p : Fin k → (identificationGraph G S).Walk (some u) none)
    (hp : AdmissiblePathFamily (identificationGraph G S) (some u) none k a d p) :
    ∃ t : Fin k → V, ∃ q : ∀ i, G.Walk u.1 (t i),
      (∀ i, t i ∈ S) ∧ EndpointPathFamily G k a d (fun _ => u.1) t q ∧
      (∀ i, (q i).length = (p i).length) ∧
      ∀ i w, w ∈ (q i).support → w = t i ∨ w ∉ S := by
  classical
  have h : ∀ i : Fin k, ∃ t ∈ S, ∃ q : G.Walk u.1 t,
      q.IsPath ∧ q.length = (p i).length ∧
        ∀ w ∈ q.support, w = t ∨ w ∉ S := by
    intro i
    exact identification_path_lift_to_root G S u (p i) (hp.2.2 i).1
  choose t ht q hq hlen hsupp using h
  refine ⟨t, q, ht, ⟨hp.1, hp.2.1, ?_⟩, hlen, hsupp⟩
  intro i
  exact ⟨hq i, (hlen i).trans (hp.2.2 i).2⟩

theorem identification_induced_family_lift (G : SimpleGraph V) (T S : Set V)
    (v : {w : T // w.1 ∉ S}) (k a d : ℕ)
    (p : Fin k → (identificationGraph (G.induce T) {w : T | w.1 ∈ S}).Walk none (some v))
    (hp : AdmissiblePathFamily (identificationGraph (G.induce T) {w : T | w.1 ∈ S})
      none (some v) k a d p) :
    ∃ s : Fin k → V, ∃ q : ∀ i, G.Walk (s i) v.1.1,
      (∀ i, s i ∈ S) ∧ EndpointPathFamily G k a d s (fun _ => v.1.1) q ∧
      (∀ i, (q i).length = (p i).length) ∧
      ∀ i w, w ∈ (q i).support → w ∈ T ∧ (w = s i ∨ w ∉ S) := by
  obtain ⟨s, q, hs, hfam, hlen, hsupp⟩ :=
    identification_family_lift (G.induce T) {w : T | w.1 ∈ S} v k a d p hp
  let f : G.induce T →g G := (SimpleGraph.Embedding.induce T).toHom
  refine ⟨(fun i => (s i).1), (fun i => (q i).map f), hs, ?_, ?_, ?_⟩
  · refine ⟨hfam.1, hfam.2.1, ?_⟩
    intro i
    refine ⟨(Walk.isPath_map_iff_of_injective (f := f) Subtype.val_injective).mpr
      (hfam.2.2 i).1, ?_⟩
    exact (Walk.length_map (p := q i) (f := f)).trans (hfam.2.2 i).2
  · intro i
    exact (Walk.length_map (p := q i) (f := f)).trans (hlen i)
  · intro i w hw
    have hw' : w ∈ ((q i).map f).support := hw
    rw [Walk.support_map] at hw'
    rcases List.mem_map.mp hw' with ⟨z, hz, he⟩
    change z.1 = w at he
    refine ⟨he ▸ z.2, ?_⟩
    rcases hsupp i z hz with hzS | hzS
    · exact Or.inl (he.symm.trans (congrArg Subtype.val hzS))
    · change z.1 ∉ S at hzS
      exact Or.inr (he ▸ hzS)

#print axioms EndpointPathFamily
#print axioms identification_family_lift
#print axioms identification_family_lift_to_root
#print axioms identification_induced_family_lift
end TaskH.Gao
