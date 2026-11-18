import Research.TaskH.Gao.RealRootRegion
import Research.TaskH.Gao.CliqueBoundaryBudget

/-! S=empty retains the REAL x and every original interior neighbor. -/
set_option autoImplicit false
universe u
namespace TaskH.Gao
open SimpleGraph TaskH.Fan
variable {V : Type u}

theorem clique_empty_boundary_cover (G : SimpleGraph V) (B K : Set V) (x b : V)
    (hS : cliqueBlockBoundary G B K x b = ∅)
    (hcover : ∀ v ∈ B, v ≠ b → ∀ z, G.Adj v z → z ∈ B ∨ z ∈ K) :
    ∀ v ∈ B, v ≠ b → ∀ z, G.Adj v z → z ∈ B ∨ z = x := by
  intro v hv hvb z e
  rcases hcover v hv hvb z e with hzB | hzK
  · exact Or.inl hzB
  · by_cases hzx : z = x
    · exact Or.inr hzx
    · have hzS : z ∈ cliqueBlockBoundary G B K x b := ⟨hzK, hzx, v, hv, hvb, e⟩
      have hzE : z ∈ (∅ : Set V) :=
        Eq.mp (congrArg (fun S : Set V => z ∈ S) hS) hzS
      exact False.elim hzE

theorem real_x_spoke_from_actual_delete [iV : Fintype V] (G : SimpleGraph V)
    (B K : Set V) (x b : V) (hG : @TwoConnected V iV G)
    (hBK : Disjoint B K) (ht : 3 ≤ K.ncard)
    (hI : ∃ v ∈ B, v ≠ b) (hb : b ∈ B)
    (hcover : ∀ v ∈ B, v ≠ b → ∀ z, G.Adj v z → z ∈ B ∨ z = x) :
    ∃ w ∈ B, w ≠ b ∧ G.Adj x w := by
  classical
  obtain ⟨z, hzK, hzx⟩ := Set.exists_ne_of_one_lt_ncard (by omega : 1 < K.ncard) x
  have hzB : z ∉ B := fun hz => Set.disjoint_left.mp hBK hz hzK
  have hzb : z ≠ b := fun he => hzB (he.symm ▸ hb)
  by_contra hn
  have hclosed : ∀ a d : {v : V // v ≠ b}, a.1 ∈ B →
      (G.induce {v | v ≠ b}).Adj a d → d.1 ∈ B := by
    intro a d ha e
    rcases hcover a.1 ha a.2 d.1 e with hd | hd
    · exact hd
    · exact False.elim (hn ⟨a.1, ha, a.2, hd ▸ e.symm⟩)
  have hwalk : ∀ {a d : {v : V // v ≠ b}},
      (G.induce {v | v ≠ b}).Walk a d → a.1 ∈ B → d.1 ∈ B := by
    intro a d p
    induction p with
    | nil => exact fun ha => ha
    | cons e _ ih => exact fun ha => ih (hclosed _ _ ha e)
  obtain ⟨v, hv, hvb⟩ := hI
  obtain ⟨p⟩ := (hG.2.2 b) ⟨v, hvb⟩ ⟨z, hzb⟩
  exact hzB (hwalk p hv)

theorem twoConnected_block_has_other {B : Set V} [iB : Fintype B]
    (G : SimpleGraph V) (b : B) (hB : @TwoConnected B iB (G.induce B)) :
    ∃ w : B, w ≠ b := by
  obtain ⟨a, d, _e, had, _hae, _hde⟩ :=
    Fintype.two_lt_card_iff.mp (show 2 < Fintype.card B by have hc := hB.1; omega)
  by_cases hab : a = b
  · exact ⟨d, fun hdb => had (hab.trans hdb.symm)⟩
  · exact ⟨a, hab⟩

theorem clique_empty_real_rooted [iV : Fintype V] (G : SimpleGraph V)
    (B K : Set V) (x : V) [iB : Fintype B] [iT : Fintype (B ∪ {x} : Set V)]
    (b : B) (hG : @TwoConnected V iV G) (hB : @TwoConnected B iB (G.induce B))
    (hBK : Disjoint B K) (hx : x ∈ K) (ht : 3 ≤ K.ncard)
    (hS : cliqueBlockBoundary G B K x b.1 = ∅)
    (hcover : ∀ v ∈ B, v ≠ b.1 → ∀ z, G.Adj v z → z ∈ B ∨ z ∈ K) :
    RootedTwoConnected (realRootGraph G B x) (realRootPoint B x) (realRootBlockPoint B x b) := by
  obtain ⟨w, hwb⟩ := twoConnected_block_has_other G b hB
  have hI : ∃ v ∈ B, v ≠ b.1 := ⟨w.1, w.2, fun he => hwb (Subtype.ext he)⟩
  obtain ⟨v, hv, hvb, e⟩ := real_x_spoke_from_actual_delete G B K x b.1 hG hBK ht hI b.2
    (clique_empty_boundary_cover G B K x b.1 hS hcover)
  have hxB : x ∉ B := fun hxB => Set.disjoint_left.mp hBK hxB hx
  exact realRoot_rooted_from_actual_spoke G B x hxB b ⟨v, hv⟩ hB e
    (fun he => hvb (congrArg Subtype.val he))

theorem realRoot_neighbor_ncard (G : SimpleGraph V) (B : Set V) (x : V) (v : B)
    (hcover : ∀ z, G.Adj v.1 z → z ∈ B ∨ z = x) :
    (G.neighborSet v.1).ncard =
      ((realRootGraph G B x).neighborSet (realRootBlockPoint B x v)).ncard := by
  apply Set.ncard_congr (fun z hz => (⟨z, hcover z hz⟩ : (B ∪ {x} : Set V)))
  · intro z hz
    exact hz
  · intro a d _ha _hd he
    exact congrArg Subtype.val he
  · intro z hz
    exact ⟨z.1, hz, Subtype.ext rfl⟩

theorem clique_empty_real_nonroot_degree (G : SimpleGraph V) (B K : Set V)
    (x y : V) (b : B) (k : ℕ) (hBK : Disjoint B K) (hx : x ∈ K)
    (hBy : y ∈ B → y = b.1) (hdeg : NonrootDegreeAtLeast G x y (k + 1))
    (hS : cliqueBlockBoundary G B K x b.1 = ∅)
    (hcover : ∀ v ∈ B, v ≠ b.1 → ∀ z, G.Adj v z → z ∈ B ∨ z ∈ K) :
    NonrootDegreeAtLeast (realRootGraph G B x) (realRootPoint B x)
      (realRootBlockPoint B x b) (k + 1) := by
  intro z hzx hzb
  have hzB : z.1 ∈ B := by
    rcases z.2 with hz | hz
    · exact hz
    · exact False.elim (hzx (Subtype.ext hz))
  let v : B := ⟨z.1, hzB⟩
  have hvb : v.1 ≠ b.1 := fun he => hzb (Subtype.ext he)
  have hvx : v.1 ≠ x := fun he => Set.disjoint_left.mp hBK v.2 (he.symm ▸ hx)
  have hvy : v.1 ≠ y := fun he => hvb (he.trans (hBy (he ▸ v.2)))
  have hn := realRoot_neighbor_ncard G B x v
    (clique_empty_boundary_cover G B K x b.1 hS hcover v.1 v.2 hvb)
  have he : realRootBlockPoint B x v = z := Subtype.ext rfl
  rw [he] at hn
  rw [← hn]
  exact hdeg v.1 hvx hvy

theorem clique_empty_real_strict_order [Finite V] (B K : Set V) (x : V)
    (hBK : Disjoint B K) (ht : 3 ≤ K.ncard) :
    Nat.card (B ∪ {x} : Set V) < Nat.card V := by
  obtain ⟨z, hzK, hzx⟩ := Set.exists_ne_of_one_lt_ncard (by omega : 1 < K.ncard) x
  have hzT : z ∉ B ∪ ({x} : Set V) := by
    rintro (hz | hz)
    · exact Set.disjoint_left.mp hBK hz hzK
    · exact hzx hz
  have hne : B ∪ ({x} : Set V) ≠ Set.univ := by
    intro he
    exact hzT (he.symm ▸ Set.mem_univ z)
  rw [Nat.card_coe_set_eq]
  exact Set.ncard_lt_card hne

#print axioms clique_empty_boundary_cover
#print axioms real_x_spoke_from_actual_delete
#print axioms twoConnected_block_has_other
#print axioms clique_empty_real_rooted
#print axioms realRoot_neighbor_ncard
#print axioms clique_empty_real_nonroot_degree
#print axioms clique_empty_real_strict_order
end TaskH.Gao
