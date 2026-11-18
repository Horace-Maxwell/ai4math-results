import Research.TaskH.Fan.EqualNeighborhoodExterior

/-! The complete external boundary is derived from the actual deleted-neighborhood component. -/
set_option autoImplicit false
universe u
namespace TaskH.Fan
open SimpleGraph
variable {V : Type u}

def equalBranchBoundary (G : SimpleGraph V) (D : Set V) : Set V :=
  {s | s ∉ D ∧ ∃ d ∈ D, G.Adj d s}

theorem equalBranch_crossing_edge (G : SimpleGraph V) (D : Set V) (hG : G.Connected)
    (p q : V) (hp : p ∈ D) (hq : q ∉ D) :
    ∃ d ∈ D, ∃ s ∉ D, G.Adj d s := by
  classical
  by_contra hn
  have hclosed : ∀ d ∈ D, ∀ s, G.Adj d s → s ∈ D := by
    intro d hd s e
    by_contra hs
    exact hn ⟨d, hd, s, hs, e⟩
  have hwalk : ∀ {v w : V}, G.Walk v w → v ∈ D → w ∈ D := by
    intro v w p
    induction p with
    | nil => exact fun h => h
    | cons e p ih =>
      intro hv
      exact ih (hclosed _ hv _ e)
  obtain ⟨p⟩ := hG p q
  exact hq (hwalk p hp)

theorem equalBranchBoundary_subset (G : SimpleGraph V) (x w : V)
    (hw : w ∉ G.neighborSet x) :
    equalBranchBoundary G (equalNeighborhoodRegion G x w hw) ⊆ G.neighborSet x := by
  rintro s ⟨hs, d, hd, e⟩
  exact equalNeighborhoodRegion_boundary G x w hw d hd s hs e

theorem equalBranchBoundary_two [Fintype V] (G : SimpleGraph V) (x y w : V)
    (hG : TwoConnected G) (hno : ¬G.Adj x y)
    (heq : G.neighborSet y = G.neighborSet x)
    (hw : w ∉ G.neighborSet x) (hwx : w ≠ x) (hwy : w ≠ y) :
    ∃ s ∈ equalBranchBoundary G (equalNeighborhoodRegion G x w hw),
      ∃ t ∈ equalBranchBoundary G (equalNeighborhoodRegion G x w hw), s ≠ t := by
  let D := equalNeighborhoodRegion G x w hw
  have hwD : w ∈ D := equalNeighborhoodRegion_root G x w hw
  have hxD : x ∉ D := (equalNeighborhoodRegion_avoids_roots G x y w hno heq hw hwx hwy).1
  obtain ⟨d, hd, s, hs, e⟩ := equalBranch_crossing_edge G D hG.2.1 w x hwD hxD
  have hsB : s ∈ equalBranchBoundary G D := ⟨hs, d, hd, e⟩
  have hsN : G.Adj x s := equalBranchBoundary_subset G x w hw hsB
  have hws : w ≠ s := fun he => hs (he ▸ hwD)
  let wr : {v : V // v ≠ s} := ⟨w, hws⟩
  let xr : {v : V // v ≠ s} := ⟨x, hsN.ne⟩
  obtain ⟨d', hd', t, ht, e'⟩ := equalBranch_crossing_edge
    (G.induce {v : V | v ≠ s}) {v | v.1 ∈ D} (hG.2.2 s) wr xr hwD hxD
  have htB : t.1 ∈ equalBranchBoundary G D := ⟨ht, d'.1, hd', e'⟩
  exact ⟨s, hsB, t.1, htB, t.2.symm⟩

theorem equalBranchBoundary_ncard [Fintype V] (G : SimpleGraph V) (x y w : V)
    (hG : TwoConnected G) (hno : ¬G.Adj x y)
    (heq : G.neighborSet y = G.neighborSet x)
    (hw : w ∉ G.neighborSet x) (hwx : w ≠ x) (hwy : w ≠ y) :
    2 ≤ (equalBranchBoundary G (equalNeighborhoodRegion G x w hw)).ncard := by
  obtain ⟨s, hs, t, ht, hst⟩ := equalBranchBoundary_two G x y w hG hno heq hw hwx hwy
  have hsub : ({s, t} : Set V) ⊆ equalBranchBoundary G (equalNeighborhoodRegion G x w hw) := by
    intro v hv
    rcases Set.mem_insert_iff.mp hv with hv | hv
    · exact hv.symm ▸ hs
    · exact (Set.mem_singleton_iff.mp hv).symm ▸ ht
  have hle := Set.ncard_le_ncard hsub
  rw [Set.ncard_pair hst] at hle
  exact hle

theorem equalBranchRegion_neighbors_full (G : SimpleGraph V) (D : Set V)
    (d : V) (hd : d ∈ D) :
    ∀ s : V, G.Adj d s → s ∈ D ∪ equalBranchBoundary G D := by
  classical
  intro s e
  by_cases hs : s ∈ D
  · exact Or.inl hs
  · exact Or.inr ⟨hs, d, hd, e⟩

theorem equalBranchRegion_neighbor_ncard (G : SimpleGraph V) (D : Set V)
    (d : D) :
    (G.neighborSet d.1).ncard =
      ((G.induce (D ∪ equalBranchBoundary G D)).neighborSet
        (⟨d.1, Or.inl d.2⟩ : (D ∪ equalBranchBoundary G D : Set V))).ncard := by
  apply Set.ncard_congr (fun s hs =>
    (⟨s, equalBranchRegion_neighbors_full G D d.1 d.2 s hs⟩ : (D ∪ equalBranchBoundary G D : Set V)))
  · intro s hs
    exact hs
  · intro s t hs ht he
    exact congrArg Subtype.val he
  · intro s hs
    exact ⟨s.1, hs, Subtype.ext rfl⟩

theorem equalBranchBoundary_neighbor_unique (G : SimpleGraph V) (x y w : V)
    (hxy : x ≠ y) (hno : ¬G.Adj x y) (hfour : ¬rootFourCycleAvoiding G x y)
    (heq : G.neighborSet y = G.neighborSet x)
    (hw : w ∉ G.neighborSet x) (hwx : w ≠ x) (hwy : w ≠ y)
    (d : V) (hd : d ∈ equalNeighborhoodRegion G x w hw)
    {s t : V}
    (hs : s ∈ equalBranchBoundary G (equalNeighborhoodRegion G x w hw))
    (ht : t ∈ equalBranchBoundary G (equalNeighborhoodRegion G x w hw))
    (es : G.Adj d s) (et : G.Adj d t) : s = t := by
  have havoid := equalNeighborhoodRegion_avoids_roots G x y w hno heq hw hwx hwy
  have hdx : d ≠ x := fun he => havoid.1 (he ▸ hd)
  have hdy : d ≠ y := fun he => havoid.2 (he ▸ hd)
  exact noFour_neighbor_unique G x y hxy hno hfour d hdx hdy
    (equalBranchBoundary_subset G x w hw hs) (equalBranchBoundary_subset G x w hw ht) es et

def equalBranchDomain (G : SimpleGraph V) (x w : V) (hw : w ∉ G.neighborSet x) : Set V :=
  equalNeighborhoodRegion G x w hw ∪ equalBranchBoundary G (equalNeighborhoodRegion G x w hw)

def equalBranchCollapsed (G : SimpleGraph V) (x w : V) (hw : w ∉ G.neighborSet x) (u : V) :
    Set (equalBranchDomain G x w hw) :=
  {v | v.1 ∈ equalBranchBoundary G (equalNeighborhoodRegion G x w hw) ∧ v.1 ≠ u}

def equalBranchGraph (G : SimpleGraph V) (x w : V) (hw : w ∉ G.neighborSet x) (u : V) :
    SimpleGraph (IdentificationVertex (equalBranchCollapsed G x w hw u)) :=
  identificationGraph (G.induce (equalBranchDomain G x w hw)) (equalBranchCollapsed G x w hw u)

theorem equalBranchCollapsed_nonempty [Fintype V] (G : SimpleGraph V) (x y w u : V)
    (hG : TwoConnected G) (hno : ¬G.Adj x y)
    (heq : G.neighborSet y = G.neighborSet x)
    (hw : w ∉ G.neighborSet x) (hwx : w ≠ x) (hwy : w ≠ y) :
    (equalBranchCollapsed G x w hw u).Nonempty := by
  obtain ⟨s, hs, t, ht, hst⟩ := equalBranchBoundary_two G x y w hG hno heq hw hwx hwy
  by_cases hsu : s = u
  · have htu : t ≠ u := fun he => hst (hsu.trans he.symm)
    exact ⟨⟨t, Or.inr ht⟩, ht, htu⟩
  · exact ⟨⟨s, Or.inr hs⟩, hs, hsu⟩

theorem equalBranchDomain_avoids_roots (G : SimpleGraph V) (x y w : V)
    (hno : ¬G.Adj x y) (heq : G.neighborSet y = G.neighborSet x)
    (hw : w ∉ G.neighborSet x) (hwx : w ≠ x) (hwy : w ≠ y) :
    x ∉ equalBranchDomain G x w hw ∧ y ∉ equalBranchDomain G x w hw := by
  have ha := equalNeighborhoodRegion_avoids_roots G x y w hno heq hw hwx hwy
  constructor
  · rintro (hd | hs)
    · exact ha.1 hd
    · exact G.irrefl (equalBranchBoundary_subset G x w hw hs)
  · rintro (hd | hs)
    · exact ha.2 hd
    · exact hno (equalBranchBoundary_subset G x w hw hs)

theorem equalBranchGraph_card [Fintype V] (G : SimpleGraph V) (x y w u : V)
    (hG : TwoConnected G) (hno : ¬G.Adj x y)
    (heq : G.neighborSet y = G.neighborSet x)
    (hw : w ∉ G.neighborSet x) (hwx : w ≠ x) (hwy : w ≠ y)
    [Fintype (equalBranchDomain G x w hw)]
    [Fintype (IdentificationVertex (equalBranchCollapsed G x w hw u))] :
    Fintype.card (IdentificationVertex (equalBranchCollapsed G x w hw u)) < Fintype.card V := by
  have hcollapse := equalBranchCollapsed_nonempty G x y w u hG hno heq hw hwx hwy
  have hle := Fintype.card_le_of_surjective (identificationMap (equalBranchCollapsed G x w hw u))
    (identification_map_surjective _ hcollapse)
  have hxD := (equalNeighborhoodRegion_avoids_roots G x y w hno heq hw hwx hwy).1
  have hxP : x ∉ equalBranchDomain G x w hw := by
    rintro (hx | hx)
    · exact hxD hx
    · exact G.irrefl (equalBranchBoundary_subset G x w hw hx)
  have hlt := Fintype.card_subtype_lt (p := fun v => v ∈ equalBranchDomain G x w hw)
    (x := x) hxP
  exact lt_of_le_of_lt hle hlt

theorem equalBranchGraph_nonroot_degree (G : SimpleGraph V) (x y w u : V)
    (hxy : x ≠ y) (hno : ¬G.Adj x y) (hfour : ¬rootFourCycleAvoiding G x y)
    (heq : G.neighborSet y = G.neighborSet x)
    (hw : w ∉ G.neighborSet x) (hwx : w ≠ x) (hwy : w ≠ y)
    (hu : u ∈ equalBranchBoundary G (equalNeighborhoodRegion G x w hw))
    (hdeg : NonrootDegreeAtLeast G x y 3) :
    NonrootDegreeAtLeast (equalBranchGraph G x w hw u) none
      (some ⟨(⟨u, Or.inr hu⟩ : equalBranchDomain G x w hw),
        by rintro ⟨_, hne⟩; exact hne rfl⟩) 3 := by
  intro t htn htu
  cases t with
  | none => exact False.elim (htn rfl)
  | some a =>
    have hd : a.1.1 ∈ equalNeighborhoodRegion G x w hw := by
      rcases a.1.2 with hd | hs
      · exact hd
      · by_cases hau : a.1.1 = u
        · have haeq : a = ⟨(⟨u, Or.inr hu⟩ : equalBranchDomain G x w hw),
              by rintro ⟨_, hne⟩; exact hne rfl⟩ := Subtype.ext (Subtype.ext hau)
          exact False.elim (htu (congrArg Option.some haeq))
        · exact False.elim (a.2 ⟨hs, hau⟩)
    have havoid := equalNeighborhoodRegion_avoids_roots G x y w hno heq hw hwx hwy
    have hdx : a.1.1 ≠ x := by
      intro he
      exact havoid.1 (Eq.mp
        (congrArg (fun z : V => z ∈ equalNeighborhoodRegion G x w hw) he) hd)
    have hdy : a.1.1 ≠ y := by
      intro he
      exact havoid.2 (Eq.mp
        (congrArg (fun z : V => z ∈ equalNeighborhoodRegion G x w hw) he) hd)
    have huni : ∀ b c : equalBranchDomain G x w hw,
        b ∈ equalBranchCollapsed G x w hw u → c ∈ equalBranchCollapsed G x w hw u →
        (G.induce (equalBranchDomain G x w hw)).Adj a.1 b →
        (G.induce (equalBranchDomain G x w hw)).Adj a.1 c → b = c := by
      intro b c hb hc eb ec
      exact Subtype.ext (equalBranchBoundary_neighbor_unique G x y w hxy hno hfour heq
        hw hwx hwy a.1.1 hd hb.1 hc.1 eb ec)
    have hi := identification_neighbor_ncard (G.induce (equalBranchDomain G x w hw))
      (equalBranchCollapsed G x w hw u) a huni
    have hf := equalBranchRegion_neighbor_ncard G (equalNeighborhoodRegion G x w hw) ⟨a.1.1, hd⟩
    change 3 ≤ ((identificationGraph (G.induce (equalBranchDomain G x w hw))
      (equalBranchCollapsed G x w hw u)).neighborSet (some a)).ncard
    have hf' : (G.neighborSet a.1.1).ncard =
        ((G.induce (equalBranchDomain G x w hw)).neighborSet a.1).ncard := hf
    rw [← hi, ← hf']
    exact hdeg a.1.1 hdx hdy

#print axioms equalBranchBoundary
#print axioms equalBranch_crossing_edge
#print axioms equalBranchBoundary_subset
#print axioms equalBranchBoundary_two
#print axioms equalBranchBoundary_ncard
#print axioms equalBranchRegion_neighbors_full
#print axioms equalBranchRegion_neighbor_ncard
#print axioms equalBranchBoundary_neighbor_unique
#print axioms equalBranchDomain
#print axioms equalBranchCollapsed
#print axioms equalBranchGraph
#print axioms equalBranchCollapsed_nonempty
#print axioms equalBranchDomain_avoids_roots
#print axioms equalBranchGraph_card
#print axioms equalBranchGraph_nonroot_degree
end TaskH.Fan
