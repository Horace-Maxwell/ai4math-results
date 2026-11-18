import Research.TaskH.Gao.SingletonG1Quotient
import Research.TaskH.Gao.IdentificationDegree

/-! Exact full-domain degree balance gives ell+1, retaining the original nonroot degree. -/
set_option autoImplicit false
universe u
namespace TaskH.Gao
open SimpleGraph TaskH.Fan
variable {V : Type u}

theorem singleton_g1_collapse_ncard (G : SimpleGraph V) (K : Set V)
    (C : (G.induce Kᶜ).ConnectedComponent) (v : V) :
    (boundaryCollapse G (singletonG1Vertices G K C) v).ncard =
      (singletonG1Boundary G K C \ {v}).ncard := by
  apply Set.ncard_congr (fun w _ => w.1)
  · intro w hw
    have hb := hw.1
    rw [singleton_g1_full_boundary G K C] at hb
    exact ⟨hb, hw.2⟩
  · intro a b _ha _hb he
    exact Subtype.ext he
  · intro a ha
    have hb : a ∈ equalBranchBoundary G (singletonG1Vertices G K C) := by
      rw [singleton_g1_full_boundary G K C]
      exact ha.1
    exact ⟨⟨a, Or.inr hb⟩, ⟨hb, ha.2⟩, rfl⟩

theorem singleton_g1_nonroot_degree [Fintype V] (G : SimpleGraph V) (K : Set V)
    (C : (G.induce Kᶜ).ConnectedComponent) (x y v : V) (k : ℕ)
    (hG : TwoConnected G) (hx : x ∈ K) (hy : y ∉ K)
    (hK : 3 ≤ K.ncard) (htk : K.ncard ≤ k)
    (hother : C ≠ (G.induce Kᶜ).connectedComponentMk ⟨y, hy⟩)
    (hv : v ∈ singletonG1Boundary G K C)
    (hxD : ¬∃ d : C.supp, G.Adj x d.1.1)
    (hdeg : NonrootDegreeAtLeast G x y (k + 1)) :
    NonrootDegreeAtLeast (boundaryQuotient G (singletonG1Vertices G K C) v) none
      (some (boundaryRetainedRoot G (singletonG1Vertices G K C) v
        (by rw [singleton_g1_full_boundary G K C]; exact hv))) (k - K.ncard + 4) := by
  classical
  let R := singletonG1Vertices G K C
  have hvB : v ∈ equalBranchBoundary G R := by
    rw [singleton_g1_full_boundary G K C]
    exact hv
  have hs := (singleton_g1_native_boundary_budget G K C x v hG hx
    (by omega : 2 ≤ K.ncard) hv hxD).2.2
  rw [← singleton_g1_collapse_ncard G K C v] at hs
  change (boundaryCollapse G R v).ncard + 2 ≤ K.ncard at hs
  intro q hqn hqv
  cases q with
  | none => exact False.elim (hqn rfl)
  | some a =>
    have hav : a.1.1 ≠ v := by
      intro he
      have he' : a = boundaryRetainedRoot G R v hvB := Subtype.ext (Subtype.ext he)
      exact hqv (congrArg Option.some he')
    have haR : a.1.1 ∈ R := by
      rcases a.1.2 with ha | ha
      · exact ha
      · exact False.elim (a.2 ⟨ha, hav⟩)
    obtain ⟨haK, haC⟩ := haR
    let dr : C.supp := ⟨⟨a.1.1, haK⟩, haC⟩
    have hax : a.1.1 ≠ x := fun he => haK
      (Eq.mpr (congrArg (fun z : V => z ∈ K) he) hx)
    have hay : a.1.1 ≠ y := singleton_g1_point_ne_y G K y hy C hother dr
    have hd := hdeg a.1.1 hax hay
    have hf : ((G.induce (boundaryDomain G R)).neighborSet a.1).ncard =
        (G.neighborSet a.1.1).ncard :=
      (equalBranchRegion_neighbor_ncard G R ⟨a.1.1, haK, haC⟩).symm
    have hb := identification_degree_balance (G.induce (boundaryDomain G R))
      (boundaryCollapse G R v) a
    rw [hf] at hb
    have hi : (((G.induce (boundaryDomain G R)).neighborSet a.1) ∩
        boundaryCollapse G R v).ncard ≤ (boundaryCollapse G R v).ncard :=
      Set.ncard_le_ncard Set.inter_subset_right
    change k - K.ncard + 4 ≤
      ((identificationGraph (G.induce (boundaryDomain G R)) (boundaryCollapse G R v)).neighborSet
        (some a)).ncard
    by_cases he : ∃ w ∈ boundaryCollapse G R v, (G.induce (boundaryDomain G R)).Adj a.1 w
    · have hbit : collapsedNeighborCount (G.induce (boundaryDomain G R))
          (boundaryCollapse G R v) a.1 = 1 := by
        exact ite_eq_left he
      rw [hbit] at hb
      omega
    · have hz : ((G.induce (boundaryDomain G R)).neighborSet a.1 ∩ boundaryCollapse G R v) = ∅ := by
        ext w
        constructor
        · rintro ⟨ew, hw⟩
          exact False.elim (he ⟨w, hw, ew⟩)
        · intro hw
          cases hw
      have hzcard : ((G.induce (boundaryDomain G R)).neighborSet a.1 ∩
          boundaryCollapse G R v).ncard = 0 := by rw [hz, Set.ncard_empty]
      have hbit : collapsedNeighborCount (G.induce (boundaryDomain G R))
          (boundaryCollapse G R v) a.1 = 0 := by
        exact ite_eq_right he
      rw [hzcard, hbit] at hb
      omega

#print axioms singleton_g1_collapse_ncard
#print axioms singleton_g1_nonroot_degree
end TaskH.Gao
