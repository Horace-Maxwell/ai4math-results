import Research.TaskH.Gao.CaseThreeTwinDeletion
import Research.TaskH.Gao.CaseThreeCoreChoice
import Research.TaskH.Gao.SingletonCliqueNeighbors

/-! Original Case3's singleton-y-component branch chooses every actual child datum internally. -/
set_option autoImplicit false
universe u
namespace TaskH.Gao
open SimpleGraph TaskH.Fan
variable {V : Type u}

theorem case3_singleton_component_neighbor_pair [Fintype V] (G : SimpleGraph V)
    (x y p q : V) (K : Set V) (hG : TwoConnected G) (hxy : x ≠ y)
    (hno : ¬G.Adj x y) (hK : G.IsClique K)
    (hsub : K ⊆ case3CoreDomain G x y p q) (hpq : p ≠ q)
    (hyT : y ∉ insert x (insert p (insert q K)))
    (hsmall : Nat.card ((G.induce (insert x (insert p (insert q K)))ᶜ).connectedComponentMk
      ⟨y, hyT⟩).supp ≤ 1)
    (hiy : G.IsIndepSet (G.neighborSet y)) :
    G.neighborSet y = ({p, q} : Set V) := by
  classical
  let T := insert x (insert p (insert q K))
  have hfull : G.neighborSet y ⊆ T := singleton_component_neighbors_subset G T y hyT hsmall
  have hn := twoConnected_neighbor_ncard_ge_two G hG x y hxy
  have hKavoid : ∀ u ∈ K, ¬G.Adj y u := by
    intro u hu eyu
    obtain ⟨w, eyw, hwu⟩ := Set.exists_ne_of_one_lt_ncard (by omega : 1 < (G.neighborSet y).ncard) u
    have euw : G.Adj u w := by
      rcases hfull eyw with hwx | hwp | hwq | hwK
      · have eyx : G.Adj y x := Eq.mp (congrArg (fun z : V => G.Adj y z) hwx) eyw
        exact False.elim (hno eyx.symm)
      · exact Eq.mpr (congrArg (fun z : V => G.Adj u z) hwp) (hsub hu).2.2.2.2.1.symm
      · exact Eq.mpr (congrArg (fun z : V => G.Adj u z) hwq) (hsub hu).2.2.2.2.2.symm
      · exact hK hu hwK hwu.symm
    exact hiy eyu eyw hwu.symm euw
  have hpair : G.neighborSet y ⊆ ({p, q} : Set V) := by
    intro u eyu
    rcases hfull eyu with hux | hup | huq | huK
    · have eyx : G.Adj y x := Eq.mp (congrArg (fun z : V => G.Adj y z) hux) eyu
      exact False.elim (hno eyx.symm)
    · exact Or.inl hup
    · exact Or.inr huq
    · exact False.elim (hKavoid u huK eyu)
  apply Set.eq_of_subset_of_ncard_le hpair
  rw [Set.ncard_pair hpq]
  exact hn

theorem case3_twin_induced_nonroot_degree [Finite V] (G : SimpleGraph V)
    (x y p q : V) (hp : p ∈ case3TwinCarrier x y) (hq : q ∈ case3TwinCarrier x y)
    (hnx : G.neighborSet x = ({p, q} : Set V))
    (hny : G.neighborSet y = ({p, q} : Set V)) (k : ℕ)
    (hd : NonrootDegreeAtLeast G x y (k + 1)) :
    NonrootDegreeAtLeast (G.induce (case3TwinCarrier x y)) ⟨p, hp⟩ ⟨q, hq⟩ (k + 1) := by
  intro a hap haq
  have hap' : a.1 ≠ p := fun he => hap (Subtype.ext he)
  have haq' : a.1 ≠ q := fun he => haq (Subtype.ext he)
  have hfull : ∀ z, G.Adj a.1 z → z ∈ case3TwinCarrier x y := by
    intro z e
    by_contra hz
    rcases case3_twin_outer_neighbor_pair G x y p q a.1 z hnx hny hz e.symm with he | he
    · exact hap' he
    · exact haq' he
  have heq : ((G.induce (case3TwinCarrier x y)).neighborSet a).ncard =
      (G.neighborSet a.1).ncard := by
    apply Set.ncard_congr (fun z _ => z.1)
    · intro z hz; exact hz
    · intro z w _ _ he; exact Subtype.ext he
    · intro z hz; exact ⟨⟨z, hfull z hz⟩, hz, rfl⟩
  rw [heq]
  exact hd a.1 a.2.1 a.2.2

theorem case3_twin_deleted_order [Fintype V] (x y : V) (hxy : x ≠ y) :
    Nat.card (case3TwinCarrier x y) < Nat.card V := by
  have hdis : Disjoint (case3TwinCarrier x y) ({x, y} : Set V) := by
    apply Set.disjoint_left.mpr
    rintro z ⟨hzx, hzy⟩ (he | he)
    · exact hzx he
    · exact hzy he
  have hn := Set.ncard_le_card ((case3TwinCarrier x y) ∪ ({x, y} : Set V))
  rw [Set.ncard_union_eq hdis, Set.ncard_pair hxy] at hn
  rw [Nat.card_coe_set_eq]
  omega

theorem case3_singleton_component_family [Fintype V] (G : SimpleGraph V)
    (x y p q : V) (K : Set V) (k : ℕ)
    (hG : TwoConnected G) (hxy : x ≠ y) (hno : ¬G.Adj x y) (hk : 1 ≤ k)
    (hK : G.IsClique K) (hsub : K ⊆ case3CoreDomain G x y p q) (ht : 2 ≤ K.ncard)
    (exp : G.Adj x p) (exq : G.Adj x q) (hpq : p ≠ q) (hpy : p ≠ y) (hqy : q ≠ y)
    (hiy : G.IsIndepSet (G.neighborSet y))
    (horder : (G.neighborSet x).ncard ≤ (G.neighborSet y).ncard)
    (hd : NonrootDegreeAtLeast G x y (k + 1))
    (hyT : y ∉ insert x (insert p (insert q K)))
    (hsmall : Nat.card ((G.induce (insert x (insert p (insert q K)))ᶜ).connectedComponentMk
      ⟨y, hyT⟩).supp ≤ 1)
    (ih : ∀ (W : Type u) [Fintype W] (J : SimpleGraph W) (s t : W) (r : ℕ),
      Fintype.card W < Fintype.card V → 1 ≤ r → RootedTwoConnected J s t →
      NonrootDegreeAtLeast J s t (r + 1) → HasAdmissiblePaths J s t r) :
    HasAdmissiblePaths G x y k := by
  classical
  have hny := case3_singleton_component_neighbor_pair G x y p q K hG hxy hno hK hsub
    hpq hyT hsmall hiy
  have hpair : ({p, q} : Set V) ⊆ G.neighborSet x := by
    intro z hz
    rcases hz with he | he
    · exact Eq.mpr (congrArg (fun z : V => G.Adj x z) he) exp
    · exact Eq.mpr (congrArg (fun z : V => G.Adj x z) he) exq
  have hnx : G.neighborSet x = ({p, q} : Set V) := by
    symm
    apply Set.eq_of_subset_of_ncard_le hpair
    rw [hny] at horder
    exact horder
  let S := case3TwinCarrier x y
  let : Fintype S := Fintype.ofFinite _
  have hpS : p ∈ S := ⟨exp.ne.symm, hpy⟩
  have hqS : q ∈ S := ⟨exq.ne.symm, hqy⟩
  let pr : S := ⟨p, hpS⟩
  let qr : S := ⟨q, hqS⟩
  obtain ⟨a, ha⟩ := (Set.ncard_pos (Set.toFinite K)).mp (by omega : 0 < K.ncard)
  let ar : S := ⟨a, (hsub ha).1, (hsub ha).2.1⟩
  have hpa : pr ≠ ar := fun he => (hsub ha).2.2.1 (congrArg Subtype.val he).symm
  have hqa : qr ≠ ar := fun he => (hsub ha).2.2.2.1 (congrArg Subtype.val he).symm
  have hpqS : pr ≠ qr := fun he => hpq (congrArg Subtype.val he)
  have hcard : 3 ≤ Fintype.card S := by
    have hc : 2 < Fintype.card S := Fintype.two_lt_card_iff.mpr ⟨pr, qr, ar, hpqS, hpa, hqa⟩
    omega
  have hroot := case3_twin_deleted_graph_rooted G x y p q hpS hqS hpq hnx hny hG hcard
  have hdegree := case3_twin_induced_nonroot_degree G x y p q hpS hqS hnx hny k hd
  have hlt : Fintype.card S < Fintype.card V := by
    simpa only [Fintype.card_eq_nat_card] using case3_twin_deleted_order (V := V) x y hxy
  have hchild := ih S (G.induce S) pr qr k hlt hk hroot hdegree
  obtain ⟨a₀, d, paths, hpaths⟩ := hchild
  let f : G.induce S →g G := (SimpleGraph.Embedding.induce S).toHom
  have hf : Function.Injective f := Subtype.val_injective
  have hm := admissible_family_map (G.induce S) G f hf pr qr k a₀ d paths hpaths
  let r : Fin k → G.Walk p q := fun i => (paths i).map f
  have hxR : ∀ i, x ∉ (r i).support := by
    intro i hz
    obtain ⟨z, _hz, he⟩ := (hm.2 i x).mp hz
    have he' : z.1 = x := he
    exact z.2.1 he'
  have hyR : ∀ i, y ∉ (r i).support := by
    intro i hz
    obtain ⟨z, _hz, he⟩ := (hm.2 i y).mp hz
    have he' : z.1 = y := he
    exact z.2.2 he'
  have eyq : G.Adj y q := Eq.mpr (congrArg (fun U : Set V => q ∈ U) hny) (Or.inr rfl)
  let r₁ : Fin k → G.Walk x q := fun i => Walk.cons exp (r i)
  have h₁ : AdmissiblePathFamily G x q k (a₀ + 1) d r₁ := by
    refine ⟨by have hh := hpaths.1; omega, hpaths.2.1, ?_⟩
    intro i
    refine ⟨(hm.1.2.2 i).1.cons (hxR i), ?_⟩
    change (Walk.cons exp (r i)).length = a₀ + 1 + i.val * d
    rw [Walk.length_cons]
    have hl : (r i).length = a₀ + i.val * d := (hm.1.2.2 i).2
    omega
  have hy₁ : ∀ i, y ∉ (r₁ i).support := by
    intro i hz
    change y ∈ x :: (r i).support at hz
    rcases List.mem_cons.mp hz with he | hz
    · exact hxy he.symm
    · exact hyR i hz
  have hmeet : ∀ i z, z ∈ (r₁ i).support → z ∈ eyq.symm.toWalk.support → z = q := by
    intro i z hz hzE
    rw [SimpleGraph.Adj.support_toWalk] at hzE
    have hh : z = q ∨ z = y := by simpa using hzE
    rcases hh with he | he
    · exact he
    · exact False.elim (hy₁ i (Eq.mp (congrArg (fun v : V => v ∈ (r₁ i).support) he) hz))
  have hfinal := admissible_family_append_fixed_tail G x q y k (a₀ + 1) d r₁ eyq.symm.toWalk
    h₁ eyq.symm.isPath_toWalk hmeet
  exact ⟨(a₀ + 1) + eyq.symm.toWalk.length, d,
    (fun i => (r₁ i).append eyq.symm.toWalk), hfinal.1⟩

#print axioms case3_singleton_component_neighbor_pair
#print axioms case3_twin_induced_nonroot_degree
#print axioms case3_twin_deleted_order
#print axioms case3_singleton_component_family
end TaskH.Gao
