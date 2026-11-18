import Research.TaskH.Gao.G6ActualComponents

/-! Exact real-neighbor accounting and a strict order bound for the four tags.
No reduced-graph degree bound or smaller-order conclusion is assumed. -/
set_option autoImplicit false
universe u
namespace TaskH.Gao
open SimpleGraph
variable {V : Type u}

theorem g6_retained_neighbors_ncard (G : SimpleGraph V) (H : Set V) (u w : V)
    (hu : u ∉ H) (hw : w ∉ H) (huw : u ≠ w) (p : G6Retained H) :
    (Option.some '' {q : G6Retained H | G.Adj (g6Value H u w p) (g6Value H u w q)}).ncard =
      (G.neighborSet (g6Value H u w p) ∩ g6RetainedSet H u w).ncard := by
  rw [Set.ncard_image_of_injective _ (Option.some_injective _)]
  apply Set.ncard_congr (fun q _ => g6Value H u w q)
  · intro q hq
    exact ⟨hq, (g6Value_range H u w).le ⟨q, rfl⟩⟩
  · intro a b _ha _hb he
    exact g6Value_injective H u w hu hw huw he
  · intro z hz
    obtain ⟨q, hq⟩ := (g6Value_range H u w).symm ▸ hz.2
    have hvalue : g6Value H u w q = z := hq
    refine ⟨q, ?_, hq⟩
    change G.Adj (g6Value H u w p) (g6Value H u w q)
    exact Eq.mpr
      (congrArg (fun v : V => G.Adj (g6Value H u w p) v) hvalue) hz.1

theorem g6_neighbor_ncard_partition [Finite V] (G : SimpleGraph V) (H A : Set V)
    (u w : V) (hu : u ∉ H) (hw : w ∉ H) (huw : u ≠ w) (p : G6Retained H) :
    ((g6Graph G H A u w).neighborSet (some p)).ncard =
      (G.neighborSet (g6Value H u w p) ∩ g6RetainedSet H u w).ncard +
        collapsedNeighborCount G (g6Boundary G H A u) (g6Value H u w p) := by
  classical
  let R : Set (G6Retained H) := {q | G.Adj (g6Value H u w p) (g6Value H u w q)}
  have hn : (none : G6Vertex H) ∉ Option.some '' R := by
    rintro ⟨q, _hq, he⟩
    cases he
  by_cases h : ∃ a ∈ g6Boundary G H A u, G.Adj (g6Value H u w p) a
  · have he : (g6Graph G H A u w).neighborSet (some p) = insert none (Option.some '' R) := by
      ext q
      cases q <;> simp [g6Graph, g6Adj, R, h]
    rw [he, Set.ncard_insert_of_notMem hn,
      g6_retained_neighbors_ncard G H u w hu hw huw p]
    simp [collapsedNeighborCount, h]
  · have he : (g6Graph G H A u w).neighborSet (some p) = Option.some '' R := by
      ext q
      cases q <;> simp [g6Graph, g6Adj, R, h]
    rw [he, g6_retained_neighbors_ncard G H u w hu hw huw p]
    simp [collapsedNeighborCount, h]

theorem g6_degree_balance [Finite V] (G : SimpleGraph V) (H A : Set V)
    (u w : V) (hu : u ∉ H) (hw : w ∉ H) (huw : u ≠ w) (p : G6Retained H) :
    ((g6Graph G H A u w).neighborSet (some p)).ncard +
        (G.neighborSet (g6Value H u w p) \ g6RetainedSet H u w).ncard =
      (G.neighborSet (g6Value H u w p)).ncard +
        collapsedNeighborCount G (g6Boundary G H A u) (g6Value H u w p) := by
  have hq := g6_neighbor_ncard_partition G H A u w hu hw huw p
  have hs := Set.ncard_inter_add_ncard_sdiff_eq_ncard
    (G.neighborSet (g6Value H u w p)) (g6RetainedSet H u w)
  omega

theorem g6_exact_degree_loss [Finite V] (G : SimpleGraph V) (H A : Set V)
    (u w : V) (hu : u ∉ H) (hw : w ∉ H) (huw : u ≠ w)
    (hST : Disjoint (g6Boundary G H A u) (g6RetainedSet H u w)) (p : G6Retained H) :
    (G.neighborSet (g6Value H u w p)).ncard -
        ((g6Graph G H A u w).neighborSet (some p)).ncard =
      (G.neighborSet (g6Value H u w p) \ g6RetainedSet H u w).ncard -
        collapsedNeighborCount G (g6Boundary G H A u) (g6Value H u w p) := by
  have hb := g6_degree_balance G H A u w hu hw huw p
  have hc := collapsedNeighborCount_le_inter G (g6Boundary G H A u) (g6Value H u w p)
  have hm : (G.neighborSet (g6Value H u w p) ∩ g6Boundary G H A u).ncard ≤
      (G.neighborSet (g6Value H u w p) \ g6RetainedSet H u w).ncard := by
    apply Set.ncard_mono
    intro v hv
    exact ⟨hv.1, Set.disjoint_left.mp hST hv.2⟩
  omega

theorem g6_w_deleted_neighbors (G : SimpleGraph V) (H A : Set V) (u w : V)
    (hHA : Disjoint H A) (hwA : w ∉ A)
    (hcover : G.neighborSet w ⊆ H ∪ A) (hcross : ∀ a ∈ A, G.Adj a w) :
    G.neighborSet w \ g6RetainedSet H u w = A \ ({u} : Set V) := by
  ext v
  constructor
  · rintro ⟨e, hvT⟩
    rcases hcover e with hvH | hvA
    · exact False.elim (hvT (Or.inl hvH))
    · exact ⟨hvA, fun hvu => hvT (Or.inr (Or.inl hvu))⟩
  · rintro ⟨hvA, hvu⟩
    refine ⟨(hcross v hvA).symm, ?_⟩
    rintro (hvH | hvT)
    · exact Set.disjoint_left.mp hHA hvH hvA
    · rcases hvT with hvu' | hvw
      · exact hvu hvu'
      · exact hwA (hvw ▸ hvA)

theorem g6_w_exact_loss [Finite V] (G : SimpleGraph V) (H A : Set V)
    (u w : V) (s : ℕ) (huA : u ∈ A) (hHA : Disjoint H A)
    (hwH : w ∉ H) (hwA : w ∉ A) (hcard : A.ncard = s + 1)
    (hS : (g6Boundary G H A u).Nonempty)
    (hcover : G.neighborSet w ⊆ H ∪ A) (hcross : ∀ a ∈ A, G.Adj a w) :
    (G.neighborSet w).ncard -
      ((g6Graph G H A u w).neighborSet (some (Sum.inr true))).ncard = s - 1 := by
  have huH : u ∉ H := fun huH => Set.disjoint_left.mp hHA huH huA
  have huw : u ≠ w := fun he => hwA (he ▸ huA)
  have hl := g6_exact_degree_loss G H A u w huH hwH huw
    (g6Boundary_disjoint_retained G H A u w hHA hwA) (Sum.inr true)
  have hd := g6_w_deleted_neighbors G H A u w hHA hwA hcover hcross
  have hs := Set.ncard_sdiff_singleton_add_one huA
  have hc : collapsedNeighborCount G (g6Boundary G H A u) w = 1 := by
    obtain ⟨a, ha⟩ := hS
    simp only [collapsedNeighborCount, ite_eq_left (show ∃ a ∈ g6Boundary G H A u,
      G.Adj w a from ⟨a, ha, (hcross a ha.1).symm⟩)]
  change (G.neighborSet w).ncard -
    ((g6Graph G H A u w).neighborSet (some (Sum.inr true))).ncard =
      (G.neighborSet w \ g6RetainedSet H u w).ncard -
        collapsedNeighborCount G (g6Boundary G H A u) w at hl
  rw [hd, hc] at hl
  omega

theorem g6_w_degree_bound [Finite V] (G : SimpleGraph V) (H A : Set V)
    (u w : V) (s k : ℕ) (huA : u ∈ A) (hHA : Disjoint H A)
    (hwH : w ∉ H) (hwA : w ∉ A) (hcard : A.ncard = s + 1)
    (hS : (g6Boundary G H A u).Nonempty)
    (hcover : G.neighborSet w ⊆ H ∪ A) (hcross : ∀ a ∈ A, G.Adj a w)
    (hsk : s + 2 ≤ k) (hdegree : k + 1 ≤ (G.neighborSet w).ncard) :
    k - s + 2 ≤ ((g6Graph G H A u w).neighborSet (some (Sum.inr true))).ncard := by
  have huH : u ∉ H := fun huH => Set.disjoint_left.mp hHA huH huA
  have huw : u ≠ w := fun he => hwA (he ▸ huA)
  have hb := g6_degree_balance G H A u w huH hwH huw (Sum.inr true)
  have hd := g6_w_deleted_neighbors G H A u w hHA hwA hcover hcross
  have hs := Set.ncard_sdiff_singleton_add_one huA
  have hc : collapsedNeighborCount G (g6Boundary G H A u) w = 1 := by
    obtain ⟨a, ha⟩ := hS
    simp only [collapsedNeighborCount, ite_eq_left (show ∃ a ∈ g6Boundary G H A u,
      G.Adj w a from ⟨a, ha, (hcross a ha.1).symm⟩)]
  change ((g6Graph G H A u w).neighborSet (some (Sum.inr true))).ncard +
      (G.neighborSet w \ g6RetainedSet H u w).ncard =
        (G.neighborSet w).ncard + collapsedNeighborCount G (g6Boundary G H A u) w at hb
  rw [hd, hc] at hb
  omega

theorem g6_h_A_only_loss_bound [Finite V] (G : SimpleGraph V) (H A : Set V)
    (u w : V) (s : ℕ) (huA : u ∈ A) (hHA : Disjoint H A)
    (hwH : w ∉ H) (hwA : w ∉ A) (hcard : A.ncard = s + 1)
    (h : H) (hcover : G.neighborSet h.1 ⊆ H ∪ A) :
    (G.neighborSet h.1).ncard -
      ((g6Graph G H A u w).neighborSet (some (Sum.inl h))).ncard ≤ s - 1 := by
  classical
  have huH : u ∉ H := fun huH => Set.disjoint_left.mp hHA huH huA
  have huw : u ≠ w := fun he => hwA (he ▸ huA)
  have hl := g6_exact_degree_loss G H A u w huH hwH huw
    (g6Boundary_disjoint_retained G H A u w hHA hwA) (Sum.inl h)
  have hsub : G.neighborSet h.1 \ g6RetainedSet H u w ⊆ A \ ({u} : Set V) := by
    rintro a ⟨e, haT⟩
    rcases hcover e with haH | haA
    · exact False.elim (haT (Or.inl haH))
    · exact ⟨haA, fun hau => haT (Or.inr (Or.inl hau))⟩
  have hbound := Set.ncard_mono hsub
  have hcard' := Set.ncard_sdiff_singleton_add_one huA
  by_cases he : ∃ a ∈ g6Boundary G H A u, G.Adj h.1 a
  · have hc : collapsedNeighborCount G (g6Boundary G H A u) h.1 = 1 := by
      simp only [collapsedNeighborCount, ite_eq_left he]
    change (G.neighborSet h.1).ncard -
      ((g6Graph G H A u w).neighborSet (some (Sum.inl h))).ncard =
        (G.neighborSet h.1 \ g6RetainedSet H u w).ncard -
          collapsedNeighborCount G (g6Boundary G H A u) h.1 at hl
    rw [hc] at hl
    omega
  · have hzero : G.neighborSet h.1 \ g6RetainedSet H u w = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      rintro a ha
      have haA := hsub ha
      exact he ⟨a, ⟨haA.1, haA.2, h.1, h.2, ha.1.symm⟩, ha.1⟩
    have hz : (G.neighborSet h.1 \ g6RetainedSet H u w).ncard = 0 := by rw [hzero]; simp
    change (G.neighborSet h.1).ncard -
      ((g6Graph G H A u w).neighborSet (some (Sum.inl h))).ncard =
        (G.neighborSet h.1 \ g6RetainedSet H u w).ncard -
          collapsedNeighborCount G (g6Boundary G H A u) h.1 at hl
    omega

theorem g6_h_B_only_loss_bound [Finite V] (G : SimpleGraph V) (H A D : Set V)
    (u w : V) (s : ℕ) (huA : u ∈ A) (hHA : Disjoint H A)
    (hwH : w ∉ H) (hwA : w ∉ A) (hwD : w ∈ D) (hcard : D.ncard = s)
    (h : H) (hcover : G.neighborSet h.1 ⊆ H ∪ D) :
    (G.neighborSet h.1).ncard -
      ((g6Graph G H A u w).neighborSet (some (Sum.inl h))).ncard ≤ s - 1 := by
  have huH : u ∉ H := fun huH => Set.disjoint_left.mp hHA huH huA
  have huw : u ≠ w := fun he => hwA (he ▸ huA)
  have hl := g6_exact_degree_loss G H A u w huH hwH huw
    (g6Boundary_disjoint_retained G H A u w hHA hwA) (Sum.inl h)
  have hsub : G.neighborSet h.1 \ g6RetainedSet H u w ⊆ D \ ({w} : Set V) := by
    rintro a ⟨e, haT⟩
    rcases hcover e with haH | haD
    · exact False.elim (haT (Or.inl haH))
    · exact ⟨haD, fun haw => haT (Or.inr (Or.inr haw))⟩
  have hb := Set.ncard_mono hsub
  have hs := Set.ncard_sdiff_singleton_add_one hwD
  change (G.neighborSet h.1).ncard -
    ((g6Graph G H A u w).neighborSet (some (Sum.inl h))).ncard =
      (G.neighborSet h.1 \ g6RetainedSet H u w).ncard -
        collapsedNeighborCount G (g6Boundary G H A u) h.1 at hl
  omega

theorem g6_h_mixed_unique_A_loss_bound [Finite V] (G : SimpleGraph V) (H A D : Set V)
    (u w : V) (s : ℕ) (huA : u ∈ A) (hHA : Disjoint H A)
    (hwH : w ∉ H) (hwA : w ∉ A) (hwD : w ∈ D) (hcard : D.ncard = s)
    (h : H) (hcover : G.neighborSet h.1 ⊆ H ∪ (A ∪ D))
    (hunique : ∀ a ∈ A, ∀ b ∈ A, G.Adj h.1 a → G.Adj h.1 b → a = b) :
    (G.neighborSet h.1).ncard -
      ((g6Graph G H A u w).neighborSet (some (Sum.inl h))).ncard ≤ s - 1 := by
  classical
  have huH : u ∉ H := fun huH => Set.disjoint_left.mp hHA huH huA
  have huw : u ≠ w := fun he => hwA (he ▸ huA)
  have hl := g6_exact_degree_loss G H A u w huH hwH huw
    (g6Boundary_disjoint_retained G H A u w hHA hwA) (Sum.inl h)
  have hs := Set.ncard_sdiff_singleton_add_one hwD
  by_cases he : ∃ a ∈ g6Boundary G H A u, G.Adj h.1 a
  · obtain ⟨a, haS, eha⟩ := he
    have he' : ∃ a ∈ g6Boundary G H A u, G.Adj h.1 a := ⟨a, haS, eha⟩
    have hc : collapsedNeighborCount G (g6Boundary G H A u) h.1 = 1 := by
      simp only [collapsedNeighborCount, ite_eq_left he']
    have hsub : G.neighborSet h.1 \ g6RetainedSet H u w ⊆ insert a (D \ ({w} : Set V)) := by
      rintro z ⟨ehz, hzT⟩
      rcases hcover ehz with hzH | hzA | hzD
      · exact False.elim (hzT (Or.inl hzH))
      · exact Or.inl (hunique z hzA a haS.1 ehz eha)
      · exact Or.inr ⟨hzD, fun hzw => hzT (Or.inr (Or.inr hzw))⟩
    have hb := Set.ncard_mono hsub
    have hi := Set.ncard_insert_le a (D \ ({w} : Set V))
    change (G.neighborSet h.1).ncard -
      ((g6Graph G H A u w).neighborSet (some (Sum.inl h))).ncard =
        (G.neighborSet h.1 \ g6RetainedSet H u w).ncard -
          collapsedNeighborCount G (g6Boundary G H A u) h.1 at hl
    rw [hc] at hl
    omega
  · have hsub : G.neighborSet h.1 \ g6RetainedSet H u w ⊆ D \ ({w} : Set V) := by
      rintro z ⟨ehz, hzT⟩
      rcases hcover ehz with hzH | hzA | hzD
      · exact False.elim (hzT (Or.inl hzH))
      · have hzu : z ≠ u := fun hzu => hzT (Or.inr (Or.inl hzu))
        exact False.elim (he ⟨z, ⟨hzA, hzu, h.1, h.2, ehz.symm⟩, ehz⟩)
      · exact ⟨hzD, fun hzw => hzT (Or.inr (Or.inr hzw))⟩
    have hb := Set.ncard_mono hsub
    change (G.neighborSet h.1).ncard -
      ((g6Graph G H A u w).neighborSet (some (Sum.inl h))).ncard =
        (G.neighborSet h.1 \ g6RetainedSet H u w).ncard -
          collapsedNeighborCount G (g6Boundary G H A u) h.1 at hl
    omega

theorem g6_strict_original_order [Finite V] (H A : Set V) (w : V)
    (hHA : Disjoint H A) (hwH : w ∉ H) (hwA : w ∉ A) (hA : 3 ≤ A.ncard) :
    Nat.card (G6Vertex H) < Nat.card V := by
  classical
  let iH : Fintype H := Fintype.ofFinite H
  have ho : Nat.card (G6Vertex H) = H.ncard + 3 := by
    simpa only [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq] using (@g6_order V H iH)
  have hw : w ∉ H ∪ A := fun hv => hv.elim hwH hwA
  have hi := Set.ncard_insert_of_notMem hw
  have hu := Set.ncard_union_eq hHA
  have hb := Set.ncard_le_card (insert w (H ∪ A))
  omega

#print axioms g6_retained_neighbors_ncard
#print axioms g6_neighbor_ncard_partition
#print axioms g6_degree_balance
#print axioms g6_exact_degree_loss
#print axioms g6_w_deleted_neighbors
#print axioms g6_w_exact_loss
#print axioms g6_w_degree_bound
#print axioms g6_h_A_only_loss_bound
#print axioms g6_h_B_only_loss_bound
#print axioms g6_h_mixed_unique_A_loss_bound
#print axioms g6_strict_original_order
end TaskH.Gao
