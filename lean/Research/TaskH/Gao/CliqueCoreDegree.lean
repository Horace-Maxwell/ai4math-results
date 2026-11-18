import Research.TaskH.Gao.CliqueBoundaryBudget

/-! Actual induced-region identification, sharp clique loss and strict order. -/
set_option autoImplicit false
universe u
namespace TaskH.Gao
open SimpleGraph TaskH.Fan
variable {V : Type u}

def regionIdentificationGraph (G : SimpleGraph V) (B S : Set V) :
    SimpleGraph (IdentificationVertex {w : (B ∪ S : Set V) | w.1 ∈ S}) :=
  identificationGraph (G.induce (B ∪ S)) {w : (B ∪ S : Set V) | w.1 ∈ S}

def regionRetainedVertex (B S : Set V) (hBS : Disjoint B S) (v : B) :
    {w : (B ∪ S : Set V) // w.1 ∉ S} :=
  ⟨⟨v.1, Or.inl v.2⟩, fun hs => Set.disjoint_left.mp hBS v.2 hs⟩

def regionOutsideEquiv (B S : Set V) (hBS : Disjoint B S) :
    {w : (B ∪ S : Set V) // w.1 ∉ S} ≃ B where
  toFun w := ⟨w.1.1, by
    rcases w.1.2 with hB | hS
    · exact hB
    · exact False.elim (w.2 hS)⟩
  invFun := regionRetainedVertex B S hBS
  left_inv w := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  right_inv v := by
    apply Subtype.ext
    rfl

theorem regionIdentification_card [Finite V]
    (B S : Set V) (hBS : Disjoint B S) :
    Nat.card (IdentificationVertex {w : (B ∪ S : Set V) | w.1 ∈ S}) = B.ncard + 1 := by
  classical
  let : Fintype {w : (B ∪ S : Set V) // w.1 ∉ S} := Fintype.ofFinite _
  have hopt : Nat.card (Option {w : (B ∪ S : Set V) // w.1 ∉ S}) =
      Nat.card {w : (B ∪ S : Set V) // w.1 ∉ S} + 1 := by
    simpa only [Fintype.card_eq_nat_card] using
      (Fintype.card_option (α := {w : (B ∪ S : Set V) // w.1 ∉ S}))
  change Nat.card (Option {w : (B ∪ S : Set V) // w.1 ∉ S}) = B.ncard + 1
  rw [hopt, Nat.card_congr (regionOutsideEquiv B S hBS), Nat.card_coe_set_eq]

theorem regionIdentification_neighbor_ncard [Finite V] (G : SimpleGraph V)
    (B S : Set V) (hBS : Disjoint B S) (v : B) :
    ((regionIdentificationGraph G B S).neighborSet
        (some (regionRetainedVertex B S hBS v))).ncard =
      (G.neighborSet v.1 ∩ B).ncard + collapsedNeighborCount G S v.1 := by
  have hext : (((G.induce (B ∪ S)).neighborSet
      (regionRetainedVertex B S hBS v).1) \ {w : (B ∪ S : Set V) | w.1 ∈ S}).ncard =
        (G.neighborSet v.1 ∩ B).ncard := by
    apply Set.ncard_congr (fun w _ => w.1)
    · intro w hw
      refine ⟨hw.1, ?_⟩
      rcases w.2 with hB | hS
      · exact hB
      · exact False.elim (hw.2 hS)
    · intro a b _ha _hb he
      exact Subtype.ext he
    · intro w hw
      refine ⟨⟨w, Or.inl hw.2⟩, ⟨hw.1, ?_⟩, rfl⟩
      exact fun hS => Set.disjoint_left.mp hBS hw.2 hS
  have he : (∃ w ∈ ({w : (B ∪ S : Set V) | w.1 ∈ S} : Set (B ∪ S : Set V)),
      (G.induce (B ∪ S)).Adj (regionRetainedVertex B S hBS v).1 w) ↔
        ∃ w ∈ S, G.Adj v.1 w := by
    constructor
    · rintro ⟨w, hw, he⟩
      exact ⟨w.1, hw, he⟩
    · rintro ⟨w, hw, he⟩
      exact ⟨⟨w, Or.inr hw⟩, hw, he⟩
  have hbit : collapsedNeighborCount (G.induce (B ∪ S))
      {w : (B ∪ S : Set V) | w.1 ∈ S} (regionRetainedVertex B S hBS v).1 =
        collapsedNeighborCount G S v.1 := by
    classical
    simp only [collapsedNeighborCount, he]
  have hq := identification_neighbor_ncard_partition (G.induce (B ∪ S))
    {w : (B ∪ S : Set V) | w.1 ∈ S} (regionRetainedVertex B S hBS v)
  rw [hext, hbit] at hq
  exact hq

theorem cliqueBlock_boundary_disjoint (G : SimpleGraph V) (B K : Set V)
    (x b : V) (hBK : Disjoint B K) : Disjoint B (cliqueBlockBoundary G B K x b) := by
  apply Set.disjoint_left.mpr
  intro w hwB hwS
  exact Set.disjoint_left.mp hBK hwB hwS.1

theorem cliqueBlock_quotient_degree [Finite V] (G : SimpleGraph V)
    (B K : Set V) (x b : V) (k : ℕ) (hBK : Disjoint B K)
    (hK : Maximal G.IsClique K) (ht : 3 ≤ K.ncard) (htk : K.ncard ≤ k)
    (v : B) (hvb : v.1 ≠ b)
    (hcover : ∀ w, G.Adj v.1 w → w ∈ B ∨ w ∈ K)
    (hdeg : k + 1 ≤ (G.neighborSet v.1).ncard) :
    k - K.ncard + 3 ≤
      ((regionIdentificationGraph G B (cliqueBlockBoundary G B K x b)).neighborSet
        (some (regionRetainedVertex B (cliqueBlockBoundary G B K x b)
          (cliqueBlock_boundary_disjoint G B K x b hBK) v))).ncard := by
  classical
  have hvK : v.1 ∉ K := fun hv => Set.disjoint_left.mp hBK v.2 hv
  have hlt := maximal_clique_external_neighbors_lt G K hK v.1 hvK
  have hp := disjoint_region_neighbor_partition G B K hBK v.1 hcover
  have hq := regionIdentification_neighbor_ncard G B (cliqueBlockBoundary G B K x b)
    (cliqueBlock_boundary_disjoint G B K x b hBK) v
  by_cases he : ∃ w ∈ cliqueBlockBoundary G B K x b, G.Adj v.1 w
  · have hb : collapsedNeighborCount G (cliqueBlockBoundary G B K x b) v.1 = 1 := by
      simp [collapsedNeighborCount, he]
    rw [hb] at hq
    omega
  · have hb : collapsedNeighborCount G (cliqueBlockBoundary G B K x b) v.1 = 0 := by
      simp [collapsedNeighborCount, he]
    have hk := cliqueBoundary_absent_neighbors_le_one G B K x b v.1 v.2 hvb he
    rw [hb] at hq
    omega

theorem cliqueBlock_quotient_from_original_degree [Finite V] (G : SimpleGraph V)
    (B K : Set V) (x y b : V) (k : ℕ) (hBK : Disjoint B K)
    (hK : Maximal G.IsClique K) (hx : x ∈ K) (hBy : y ∈ B → y = b)
    (ht : 3 ≤ K.ncard) (htk : K.ncard ≤ k)
    (hdeg : NonrootDegreeAtLeast G x y (k + 1))
    (hcover : ∀ v ∈ B, v ≠ b → ∀ w, G.Adj v w → w ∈ B ∨ w ∈ K)
    (v : B) (hvb : v.1 ≠ b) :
    k - K.ncard + 3 ≤
      ((regionIdentificationGraph G B (cliqueBlockBoundary G B K x b)).neighborSet
        (some (regionRetainedVertex B (cliqueBlockBoundary G B K x b)
          (cliqueBlock_boundary_disjoint G B K x b hBK) v))).ncard := by
  have hvx : v.1 ≠ x := fun he => Set.disjoint_left.mp hBK v.2 (he.symm ▸ hx)
  have hvy : v.1 ≠ y := fun he => hvb (he.trans (hBy (he ▸ v.2)))
  exact cliqueBlock_quotient_degree G B K x b k hBK hK ht htk v hvb
    (hcover v.1 v.2 hvb) (hdeg v.1 hvx hvy)

theorem cliqueBlock_quotient_nonroot_degree [Finite V] (G : SimpleGraph V)
    (B K : Set V) (x y b : V) (k : ℕ) (hBK : Disjoint B K)
    (hK : Maximal G.IsClique K) (hx : x ∈ K) (hb : b ∈ B) (hBy : y ∈ B → y = b)
    (ht : 3 ≤ K.ncard) (htk : K.ncard ≤ k)
    (hdeg : NonrootDegreeAtLeast G x y (k + 1))
    (hcover : ∀ v ∈ B, v ≠ b → ∀ w, G.Adj v w → w ∈ B ∨ w ∈ K) :
    NonrootDegreeAtLeast (regionIdentificationGraph G B (cliqueBlockBoundary G B K x b))
      none (some (regionRetainedVertex B (cliqueBlockBoundary G B K x b)
        (cliqueBlock_boundary_disjoint G B K x b hBK) ⟨b, hb⟩)) (k - K.ncard + 3) := by
  intro z hzn hzb
  cases z with
  | none => exact False.elim (hzn rfl)
  | some w =>
    let v : B := regionOutsideEquiv B (cliqueBlockBoundary G B K x b)
      (cliqueBlock_boundary_disjoint G B K x b hBK) w
    have hw : regionRetainedVertex B (cliqueBlockBoundary G B K x b)
        (cliqueBlock_boundary_disjoint G B K x b hBK) v = w := by
      apply Subtype.ext
      apply Subtype.ext
      rfl
    have hvb : v.1 ≠ b := by
      intro he
      have heV : v = (⟨b, hb⟩ : B) := Subtype.ext he
      have heW : w = regionRetainedVertex B (cliqueBlockBoundary G B K x b)
          (cliqueBlock_boundary_disjoint G B K x b hBK) ⟨b, hb⟩ :=
        hw.symm.trans (congrArg
          (regionRetainedVertex B (cliqueBlockBoundary G B K x b)
            (cliqueBlock_boundary_disjoint G B K x b hBK)) heV)
      exact hzb (congrArg Option.some heW)
    have hd := cliqueBlock_quotient_from_original_degree G B K x y b k
      hBK hK hx hBy ht htk hdeg hcover v hvb
    rw [hw] at hd
    exact hd

theorem cliqueBlock_quotient_strict_order [Finite V] (G : SimpleGraph V)
    (B K : Set V) (x b : V) (hBK : Disjoint B K) (ht : 3 ≤ K.ncard) :
    Nat.card (IdentificationVertex
      {w : (B ∪ cliqueBlockBoundary G B K x b : Set V) | w.1 ∈ cliqueBlockBoundary G B K x b}) <
        Nat.card V := by
  rw [regionIdentification_card B (cliqueBlockBoundary G B K x b)
    (cliqueBlock_boundary_disjoint G B K x b hBK)]
  exact clique_core_strict_order_budget B K hBK ht

#print axioms regionIdentificationGraph
#print axioms regionRetainedVertex
#print axioms regionOutsideEquiv
#print axioms regionIdentification_card
#print axioms regionIdentification_neighbor_ncard
#print axioms cliqueBlock_boundary_disjoint
#print axioms cliqueBlock_quotient_degree
#print axioms cliqueBlock_quotient_from_original_degree
#print axioms cliqueBlock_quotient_nonroot_degree
#print axioms cliqueBlock_quotient_strict_order
end TaskH.Gao
