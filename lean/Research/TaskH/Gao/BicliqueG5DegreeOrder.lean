import Research.TaskH.Gao.BicliqueG5ActualQuotient

/-! Degree is counted in the actual region quotient. A lost A neighbor either
is retained u or creates the collapsed tag; no such neighbor is silently lost. -/
set_option autoImplicit false
universe u
namespace TaskH.Gao
open SimpleGraph TaskH.Fan
variable {V : Type u}

theorem g5_component_neighbor_cover (G : SimpleGraph V) (A B : Set V) (y : V)
    (C : (G.induce (bicliqueSingletonCore A B y)ᶜ).ConnectedComponent)
    (hNy : G.neighborSet y = A) (d : C.supp) :
    ∀ z, G.Adj d.1.1 z → z ∈ singletonG1Vertices G (bicliqueSingletonCore A B y) C ∨
      z ∈ A ∪ B := by
  intro z edz
  by_cases hzQ : z ∈ A ∪ B
  · exact Or.inr hzQ
  · have hzy : z ≠ y := by
      intro he
      have edy : G.Adj y d.1.1 := (he ▸ edz).symm
      have hdA : d.1.1 ∈ A := hNy ▸ edy
      exact d.1.2 (Or.inl (Or.inl hdA))
    have hzK : z ∉ bicliqueSingletonCore A B y := by
      rintro (hz | hz)
      · exact hzQ hz
      · exact hzy hz
    exact Or.inl ⟨hzK, C.mem_supp_of_adj_mem_supp d.2 edz⟩

theorem g5_actual_point_degree [Fintype V] (G : SimpleGraph V) (A B : Set V)
    (x y u : V) (s k : ℕ)
    (C : (G.induce (bicliqueSingletonCore A B y)ᶜ).ConnectedComponent)
    (hx : x ∈ B) (hNy : G.neighborSet y = A) (hsk : s ≤ k)
    (hcap : ∀ d : C.supp, (G.neighborSet d.1.1 ∩ (A ∪ B)).ncard ≤ s + 1)
    (hcapB : ∀ d : C.supp, (G.neighborSet d.1.1 ∩ B).ncard ≤ s)
    (hd : NonrootDegreeAtLeast G x y (k + 1)) (d : C.supp) :
    k - s + 1 ≤
      ((regionIdentificationGraph G (g5Retained G A B y u C) (g5Collapse G A B y u C)).neighborSet
        (some (g5Point G A B y u C d))).ncard := by
  classical
  let N := g5Retained G A B y u C
  let S := g5Collapse G A B y u C
  change k - s + 1 ≤ ((regionIdentificationGraph G N S).neighborSet
    (some (g5Point G A B y u C d))).ncard
  have hdN : d.1.1 ∈ N := Or.inl ⟨d.1.2, d.2⟩
  have hdx : d.1.1 ≠ x := fun he =>
    d.1.2 (Or.inl (Or.inr (he.symm ▸ hx)))
  have hdy : d.1.1 ≠ y := fun he => d.1.2 (Or.inr he)
  have hdegree := hd d.1.1 hdx hdy
  have hbalance := Set.ncard_inter_add_ncard_sdiff_eq_ncard (G.neighborSet d.1.1) N
  have hq := regionIdentification_neighbor_ncard G N S
    (g5_retained_collapse_disjoint G A B y u C) ⟨d.1.1, hdN⟩
  have hlost : G.neighborSet d.1.1 \ N ⊆ G.neighborSet d.1.1 ∩ (A ∪ B) := by
    intro z hz
    refine ⟨hz.1, ?_⟩
    rcases g5_component_neighbor_cover G A B y C hNy d z hz.1 with hzR | hzQ
    · exact False.elim (hz.2 (Or.inl hzR))
    · exact hzQ
  have hbound := (Set.ncard_le_ncard hlost).trans (hcap d)
  by_cases he : ∃ a ∈ S, G.Adj d.1.1 a
  · have hbit : collapsedNeighborCount G S d.1.1 = 1 := by
      simp only [collapsedNeighborCount, ite_eq_left he]
    rw [hbit] at hq
    change ((regionIdentificationGraph G N S).neighborSet
      (some (g5Point G A B y u C d))).ncard =
        (G.neighborSet d.1.1 ∩ N).ncard + 1 at hq
    omega
  · have hbit : collapsedNeighborCount G S d.1.1 = 0 := by
      simp only [collapsedNeighborCount, ite_eq_right he]
    have hsubB : G.neighborSet d.1.1 \ N ⊆ G.neighborSet d.1.1 ∩ B := by
      intro z hz
      refine ⟨hz.1, ?_⟩
      rcases (hlost hz).2 with hzA | hzB
      · have hzu : z ≠ u := fun hzu => hz.2 (Or.inr hzu)
        exact False.elim (he ⟨z, ⟨hzA, hzu, d, hz.1⟩, hz.1⟩)
      · exact hzB
    have hb := (Set.ncard_le_ncard hsubB).trans (hcapB d)
    rw [hbit] at hq
    change ((regionIdentificationGraph G N S).neighborSet
      (some (g5Point G A B y u C d))).ncard =
        (G.neighborSet d.1.1 ∩ N).ncard + 0 at hq
    omega

theorem g5_actual_nonroot_degree [Fintype V] (G : SimpleGraph V) (A B : Set V)
    (x y u : V) (s k : ℕ)
    (C : (G.induce (bicliqueSingletonCore A B y)ᶜ).ConnectedComponent)
    (hx : x ∈ B) (hNy : G.neighborSet y = A) (hsk : s ≤ k)
    (hcap : ∀ d : C.supp, (G.neighborSet d.1.1 ∩ (A ∪ B)).ncard ≤ s + 1)
    (hcapB : ∀ d : C.supp, (G.neighborSet d.1.1 ∩ B).ncard ≤ s)
    (hd : NonrootDegreeAtLeast G x y (k + 1)) :
    NonrootDegreeAtLeast
      (regionIdentificationGraph G (g5Retained G A B y u C) (g5Collapse G A B y u C))
      (some (g5Root G A B y u C)) none (k - s + 1) := by
  intro q hqU hqT
  cases q with
  | none => exact False.elim (hqT rfl)
  | some q =>
    have hqN : q.1.1 ∈ g5Retained G A B y u C :=
      q.1.2.elim id (fun h => False.elim (q.2 h))
    rcases hqN with hqR | hqu
    · let d : C.supp := ⟨⟨q.1.1, hqR.1⟩, hqR.2⟩
      have he : g5Point G A B y u C d = q := Subtype.ext (Subtype.ext rfl)
      have hdegree := g5_actual_point_degree G A B x y u s k C hx hNy hsk hcap hcapB hd d
      rw [he] at hdegree
      exact hdegree
    · have he : q = g5Root G A B y u C := Subtype.ext (Subtype.ext hqu)
      exact False.elim (hqU (congrArg Option.some he))

theorem g5_actual_strict_order [Fintype V] (G : SimpleGraph V) (A B : Set V)
    (y u : V) (s : ℕ)
    (C : (G.induce (bicliqueSingletonCore A B y)ᶜ).ConnectedComponent)
    (hAB : Disjoint A B) (hu : u ∈ A) (hy : y ∉ A ∪ B)
    (hs : 1 ≤ s) (hB : B.ncard = s + 1) :
    Nat.card (IdentificationVertex
      {w : (g5Retained G A B y u C ∪ g5Collapse G A B y u C : Set V) |
        w.1 ∈ g5Collapse G A B y u C}) < Nat.card V := by
  let N := g5Retained G A B y u C
  let S := g5Collapse G A B y u C
  have hdis : Disjoint N (B ∪ {y}) := by
    apply Set.disjoint_left.mpr
    intro z hz hzB
    rcases hz with hzR | hzu
    · exact hzR.1 (hzB.elim (fun h => Or.inl (Or.inr h)) Or.inr)
    · rcases hzB with hzB | hzy
      · exact Set.disjoint_left.mp hAB (hzu.symm ▸ hu) hzB
      · exact hy (Or.inl ((hzu.symm.trans hzy) ▸ hu))
  have hyB : y ∉ B := fun h => hy (Or.inr h)
  have hc : 3 ≤ (B ∪ {y}).ncard := by
    rw [Set.union_singleton, Set.ncard_insert_of_notMem hyB, hB]
    omega
  have hn := clique_core_strict_order_budget N (B ∪ {y}) hdis hc
  rw [regionIdentification_card N S (g5_retained_collapse_disjoint G A B y u C)]
  exact hn

#print axioms g5_component_neighbor_cover
#print axioms g5_actual_point_degree
#print axioms g5_actual_nonroot_degree
#print axioms g5_actual_strict_order
end TaskH.Gao
