import Research.TaskH.Gao.CaseTwoActualComponents
import Research.TaskH.Gao.IdentificationFamilyLift

/-! Equal root neighborhoods: real exterior component, strict smaller quotient and two real end edges. -/
set_option autoImplicit false
universe u
namespace TaskH.Gao
open SimpleGraph TaskH.Fan
variable {V : Type u}

theorem case2_equal_neighborhood_original_family [Fintype V] (G : SimpleGraph V)
    (x y : V) (k : ℕ) (hG : TwoConnected G) (hxy : x ≠ y)
    (hno : ¬G.Adj x y) (hk : 3 ≤ k)
    (heq : G.neighborSet y = G.neighborSet x)
    (hi : G.IsIndepSet (G.neighborSet x)) (hquad : ¬Case2RootQuad G x y)
    (hd : NonrootDegreeAtLeast G x y (k + 1))
    (ih : ∀ (W : Type u) [Fintype W] (J : SimpleGraph W) (a b : W) (r : ℕ),
      Fintype.card W < Fintype.card V → 1 ≤ r → RootedTwoConnected J a b →
      NonrootDegreeAtLeast J a b (r + 1) → HasAdmissiblePaths J a b r) :
    HasAdmissiblePaths G x y k := by
  classical
  have hd3 : NonrootDegreeAtLeast G x y 3 := by
    intro a hax hay
    have hh := hd a hax hay
    omega
  obtain ⟨w, hwClosed, hwy⟩ := equal_neighbors_exterior_exists G x y hG hxy hno hi hd3
  have hwN : w ∉ G.neighborSet x := fun h => hwClosed (Or.inr h)
  have hwx : w ≠ x := fun he => hwClosed (Or.inl he)
  let K := G.neighborSet x
  let C := equalNeighborhoodComponent G x w hwN
  let R := singletonG1Vertices G K C
  have havoid : x ∉ R ∧ y ∉ R :=
    equalNeighborhoodRegion_avoids_roots G x y w hno heq hwN hwx hwy
  have hK : 2 ≤ K.ncard := case2_neighbor_card_ge_two G x y hG hxy
  obtain ⟨a₀, ha₀⟩ := (Set.ncard_pos (Set.toFinite K)).mp (by omega : 0 < K.ncard)
  have hEcard := singleton_g1_boundary_ncard_ge_two G K C a₀ hG ha₀ hK
  obtain ⟨u, hu⟩ := (Set.ncard_pos (Set.toFinite (singletonG1Boundary G K C))).mp
    (by omega : 0 < (singletonG1Boundary G K C).ncard)
  have huE : u ∈ equalBranchBoundary G R := by
    rw [singleton_g1_full_boundary]
    exact hu
  have hEsub : equalBranchBoundary G R ⊆ G.neighborSet x :=
    equalBranchBoundary_subset G x w hwN
  let T := boundaryDomain G R
  let S := equalBranchBoundary G R \ {u}
  let SC := boundaryCollapse G R u
  let ur := boundaryRetainedRoot G R u huE
  let : Fintype (IdentificationVertex SC) := singletonG1Fintype G K C u
  have hr := singleton_g1_rooted G K C a₀ u hG ha₀ hK hu
  have hpoint : ∀ a : {z : T // z ∉ SC}, a ≠ ur → a.1.1 ≠ x ∧ a.1.1 ≠ y := by
    intro a hau
    have hau' : a.1.1 ≠ u := fun he => hau (Subtype.ext (Subtype.ext he))
    have haR : a.1.1 ∈ R := by
      rcases a.1.2 with haR | haE
      · exact haR
      · exact False.elim (a.2 ⟨haE, hau'⟩)
    exact ⟨fun he => havoid.1 (Eq.mp (congrArg (fun v : V => v ∈ R) he) haR),
      fun he => havoid.2 (Eq.mp (congrArg (fun v : V => v ∈ R) he) haR)⟩
  have hfull : ∀ a : {z : T // z ∉ SC}, a ≠ ur → ∀ z, G.Adj a.1.1 z → z ∈ T := by
    intro a hau z e
    have hau' : a.1.1 ≠ u := fun he => hau (Subtype.ext (Subtype.ext he))
    have haR : a.1.1 ∈ R := by
      rcases a.1.2 with haR | haE
      · exact haR
      · exact False.elim (a.2 ⟨haE, hau'⟩)
    exact equalBranchRegion_neighbors_full G R a.1.1 haR z e
  have hdegree := case2_induced_identification_degree G x y k hxy hno hquad T SC ur
    (fun z hz => hEsub hz.1) hpoint hfull hd
  have hxK : x ∉ K := G.irrefl
  have hyK : y ∉ K := hno
  have hdis : Disjoint R K := by
    apply Set.disjoint_left.mpr
    rintro z ⟨hzK, _⟩ hz
    exact hzK hz
  have hyRK : y ∉ R ∪ K := fun hz => hz.elim havoid.2 hyK
  have hxRK : x ∉ R ∪ K := fun hz => hz.elim havoid.1 hxK
  have hxIns : x ∉ insert y (R ∪ K) := by
    intro hh
    rcases Set.mem_insert_iff.mp hh with he | he
    · exact hxy he
    · exact hxRK he
  have hn := Set.ncard_le_card (insert x (insert y (R ∪ K)))
  rw [Set.ncard_insert_of_notMem hxIns, Set.ncard_insert_of_notMem hyRK,
    Set.ncard_union_eq hdis] at hn
  have hRcard := singletonG1Vertices_ncard G K C
  change R.ncard = Nat.card C.supp at hRcard
  have hc := singleton_g1_order G K C u hu
  change Nat.card (IdentificationVertex (boundaryCollapse G R u)) = Nat.card C.supp + 2 at hc
  have horder : Nat.card (IdentificationVertex SC) < Nat.card V := by
    change Nat.card (IdentificationVertex (boundaryCollapse G R u)) < Nat.card V
    rw [hc]
    omega
  have horder' : Fintype.card (IdentificationVertex SC) < Fintype.card V := by
    simpa only [Fintype.card_eq_nat_card] using horder
  have hchild := ih (IdentificationVertex SC) (boundaryQuotient G R u) none (some ur)
    k horder' (by omega) hr hdegree
  obtain ⟨a, step, paths, hpaths⟩ := hchild
  obtain ⟨v, q, hv, hfam, _hlen, hsupp⟩ := identification_induced_family_lift G T S ur k a step paths hpaths
  dsimp only [ur, boundaryRetainedRoot] at q hfam
  have hxT : x ∉ T := fun hz => hz.elim havoid.1 (fun hh => G.irrefl (hEsub hh))
  have hyT : y ∉ T := fun hz => hz.elim havoid.2 (fun hh => hno (hEsub hh))
  have exu : G.Adj x u := hEsub huE
  have epy : ∀ i : Fin k, G.Adj (v i) y := by
    intro i
    have eyv : G.Adj y (v i) :=
      Eq.mpr (congrArg (fun U : Set V => v i ∈ U) heq) (hEsub (hv i).1)
    exact eyv.symm
  have hxq : ∀ i, x ∉ (q i).reverse.support := by
    intro i hh
    have hh' : x ∈ (q i).support := by simpa only [Walk.support_reverse, List.mem_reverse] using hh
    exact hxT (hsupp i x hh').1
  let F : ∀ i : Fin k, G.Walk x (v i) := fun i => Walk.cons exu (q i).reverse
  have hFP : ∀ i, (F i).IsPath := fun i => (hfam.2.2 i).1.reverse.cons (hxq i)
  have hyF : ∀ i, y ∉ (F i).support := by
    intro i hh
    change y ∈ x :: (q i).reverse.support at hh
    rcases List.mem_cons.mp hh with he | hh
    · exact hxy he.symm
    · have hh' : y ∈ (q i).support := by simpa only [Walk.support_reverse, List.mem_reverse] using hh
      exact hyT (hsupp i y hh').1
  let ps : Fin k → G.Walk x y := fun i => (F i).append (epy i).toWalk
  refine ⟨a + 2, step, ps, by have hh := hfam.1; omega, hfam.2.1, ?_⟩
  intro i
  have hmeet : ∀ z, z ∈ (F i).support → z ∈ (epy i).toWalk.support → z = v i := by
    intro z hzF hzE
    rw [SimpleGraph.Adj.support_toWalk] at hzE
    have hh : z = v i ∨ z = y := by simpa using hzE
    rcases hh with he | he
    · exact he
    · exact False.elim (hyF i (Eq.mp (congrArg (fun v : V => v ∈ (F i).support) he) hzF))
  refine ⟨append_isPath_of_only_common_endpoint (hFP i) (epy i).isPath_toWalk hmeet, ?_⟩
  change ((Walk.cons exu (q i).reverse).append (epy i).toWalk).length = a + 2 + i.val * step
  rw [Walk.length_append, Walk.length_cons, Walk.length_reverse, (epy i).length_toWalk,
    (hfam.2.2 i).2]
  omega

#print axioms case2_equal_neighborhood_original_family
end TaskH.Gao
