import Research.TaskH.Gao.SingletonG2Quotient
import Research.TaskH.Gao.IdentificationFamilyLift
import Research.TaskH.Gao.CliquePaths

/-! Original G2 paths lift with varying Y endpoints; genuine clique suffixes fill the AP. -/
set_option autoImplicit false
universe u
namespace TaskH.Gao
open SimpleGraph TaskH.Fan
variable {V : Type u}

theorem singleton_g2_family_lift (G : SimpleGraph V) (x y : V)
    (hxy : x ≠ y) (hno : ¬G.Adj x y) (ell a d : ℕ)
    (p : Fin ell → (singletonG2Graph G y).Walk
      (some (singletonG2Root G x y hxy hno)) none)
    (hp : AdmissiblePathFamily (singletonG2Graph G y)
      (some (singletonG2Root G x y hxy hno)) none ell a d p) :
    ∃ t : Fin ell → V, ∃ q : ∀ i, G.Walk x (t i),
      (∀ i, G.Adj y (t i)) ∧ EndpointPathFamily G ell a d (fun _ => x) t q ∧
      (∀ i, (q i).length = (p i).length) ∧
      ∀ i z, z ∈ (q i).support → z ≠ y ∧ (z = t i ∨ ¬G.Adj y z) := by
  obtain ⟨t, q, ht, hfam, hlen, hsupp⟩ := identification_family_lift_to_root
    (G.induce {z : V | z ≠ y}) (singletonG2Collapse G y)
    (singletonG2Root G x y hxy hno) ell a d p hp
  let f : G.induce {z : V | z ≠ y} →g G :=
    (SimpleGraph.Embedding.induce {z : V | z ≠ y}).toHom
  refine ⟨(fun i => (t i).1), (fun i => (q i).map f), ht, ?_, ?_, ?_⟩
  · refine ⟨hfam.1, hfam.2.1, ?_⟩
    intro i
    refine ⟨(Walk.isPath_map_iff_of_injective (f := f) Subtype.val_injective).mpr
      (hfam.2.2 i).1, ?_⟩
    exact (Walk.length_map (p := q i) (f := f)).trans (hfam.2.2 i).2
  · intro i
    exact (Walk.length_map (p := q i) (f := f)).trans (hlen i)
  · intro i z hz
    change z ∈ ((q i).map f).support at hz
    rw [Walk.support_map] at hz
    obtain ⟨v, hv, he⟩ := List.mem_map.mp hz
    have he' : v.1 = z := he
    refine ⟨Eq.mp (congrArg (fun w : V => w ≠ y) he') v.2, ?_⟩
    rcases hsupp i v hv with hv | hv
    · exact Or.inl (he'.symm.trans (congrArg Subtype.val hv))
    · exact Or.inr (Eq.mp (congrArg (fun w : V => ¬G.Adj y w) he') hv)

theorem singleton_g2_clique_suffixes [Finite V] (G : SimpleGraph V) (y : V)
    (hY : G.IsClique (G.neighborSet y)) (m : ℕ)
    (hm : m = (G.neighborSet y).ncard) (_hmpos : 1 ≤ m)
    (p : V) (hp : G.Adj y p) :
    ∃ q : Fin m → G.Walk p y,
      ∀ j, (q j).IsPath ∧ (q j).length = 1 + j.val ∧
        ∀ z ∈ (q j).support, G.Adj y z ∨ z = y := by
  classical
  let L : Set V := G.neighborSet y ∪ {y}
  have hyY : y ∉ G.neighborSet y := G.irrefl
  have hLc : L.ncard = m + 1 := by
    change (G.neighborSet y ∪ ({y} : Set V)).ncard = m + 1
    rw [Set.union_singleton, Set.ncard_insert_of_notMem hyY]
    omega
  have hL : G.IsClique L := by
    intro v hv w hw hvw
    rcases hv with hv | hv
    · rcases hw with hw | hw
      · exact hY hv hw hvw
      · have hwy : w = y := hw
        exact Eq.mpr (congrArg (fun z : V => G.Adj v z) hwy) hv.symm
    · have hvy : v = y := hv
      rcases hw with hw | hw
      · exact Eq.mpr (congrArg (fun z : V => G.Adj z w) hvy) hw
      · have hwy : w = y := hw
        exact False.elim (hvw (hvy.trans hwy.symm))
  let F := (Set.toFinite L).toFinset
  have hFc : F.card = m + 1 := by
    rw [← Set.ncard_eq_toFinset_card L (Set.toFinite L)]
    exact hLc
  have hF : G.IsClique (F : Set V) := by
    simpa only [F, Set.Finite.coe_toFinset] using hL
  have hpF : p ∈ F := (Set.toFinite L).mem_toFinset.mpr (Or.inl hp)
  have hyF : y ∈ F := (Set.toFinite L).mem_toFinset.mpr (Or.inr rfl)
  have hex : ∀ j : Fin m, ∃ q : G.Walk p y,
      q.IsPath ∧ q.length = 1 + j.val ∧ ∀ z ∈ q.support, z ∈ L := by
    intro j
    obtain ⟨q, hq, hl, hs⟩ := finset_clique_path_exact (1 + j.val) F p y
      hF hpF hyF hp.ne.symm (by omega) (by have hj := j.isLt; omega)
    exact ⟨q, hq, hl, fun z hz => (Set.toFinite L).mem_toFinset.mp (hs z hz)⟩
  choose q hq using hex
  exact ⟨q, hq⟩

theorem singleton_g2_family_assembly [Finite V] (G : SimpleGraph V)
    (x y : V) (hxy : x ≠ y) (hno : ¬G.Adj x y)
    (hY : G.IsClique (G.neighborSet y)) (ell : ℕ)
    (hell : 1 ≤ ell) (hm : 1 ≤ (G.neighborSet y).ncard)
    (hp : HasAdmissiblePaths (singletonG2Graph G y)
      (some (singletonG2Root G x y hxy hno)) none ell) :
    HasAdmissiblePaths G x y (ell + (G.neighborSet y).ncard - 1) := by
  classical
  obtain ⟨a, d, p, hp⟩ := hp
  obtain ⟨t, q, ht, hq, hlen, hsupp⟩ :=
    singleton_g2_family_lift G x y hxy hno ell a d p hp
  have hex : ∀ i : Fin ell, ∃ r : Fin ((G.neighborSet y).ncard) → G.Walk (t i) y,
      ∀ j, (r j).IsPath ∧ (r j).length = 1 + j.val ∧
        ∀ z ∈ (r j).support, G.Adj y z ∨ z = y := by
    intro i
    exact singleton_g2_clique_suffixes G y hY _ rfl hm (t i) (ht i)
  choose r hr using hex
  apply admissible_path_concatenation hell hm hq.1 (by omega : 1 ≤ 1)
    hq.2.1 (Or.inl rfl) t q r
    (fun i => (hq.2.2 i).1) (fun i j => (hr i j).1)
    (fun i => (hq.2.2 i).2)
  · intro i j
    simpa only [Nat.mul_one] using (hr i j).2.1
  · intro i j z hz hz'
    obtain ⟨hzy, he | he⟩ := hsupp i z hz
    · exact he
    · rcases (hr i j).2.2 z hz' with hzY | hzy'
      · exact False.elim (he hzY)
      · exact False.elim (hzy hzy')

#print axioms singleton_g2_family_lift
#print axioms singleton_g2_clique_suffixes
#print axioms singleton_g2_family_assembly
end TaskH.Gao
