import Research.TaskV.Stanley.PeelInventory
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph

namespace StanleyContinuation
open Finset SimpleGraph
open scoped Classical
noncomputable section
variable {V W : Type*} {J : SimpleGraph V} {K : SimpleGraph W} {w : V → ℕ} {z : W → ℕ}

/-- Equality of the multiplicities of all color multisets on nonempty connected sets. -/
def SameInventory (J : SimpleGraph V) (w : V → ℕ) (K : SimpleGraph W) (z : W → ℕ) : Prop :=
  ∀ M, Nat.card (coloredSets J w M) = Nat.card (coloredSets K z M)

theorem bag_card (s : Finset V) : (colorBag w s).card = s.card := Multiset.card_map _ _

theorem bag_insert [DecidableEq V] {a : V} {s : Finset V} (ha : a ∉ s) :
    colorBag w (insert a s) = w a ::ₘ colorBag w s := by
  simp [colorBag, Finset.insert_val_of_notMem ha]

theorem bag_singleton (a : V) : colorBag w {a} = {w a} := by simp [colorBag]

theorem tag_mem_iff {a : V} (unique : ∀ x, w x = w a → x = a) (s : Finset V) :
    w a ∈ colorBag w s ↔ a ∈ s := by
  constructor
  · intro h
    obtain ⟨x,hx,eq⟩ := Multiset.mem_map.mp h
    exact unique x eq ▸ hx
  · intro h
    exact Multiset.mem_map.mpr ⟨a,h,rfl⟩

private def singleEquiv (J : SimpleGraph V) (w : V → ℕ) (c : ℕ) :
    {x // w x = c} ≃ coloredSets J w {c} := by
  classical
  let f (x : {x // w x = c}) : coloredSets J w {c} :=
    ⟨{x.val},by
      constructor
      · rw [Finset.coe_singleton,induce_singleton_eq_top]
        exact connected_top
      · rw [bag_singleton,x.property]⟩
  apply Equiv.ofBijective f
  constructor
  · intro x y h
    exact Subtype.ext (Finset.singleton_injective (congrArg Subtype.val h))
  · rintro ⟨s,hs,h⟩
    have hc : s.card = 1 := by simp only [← bag_card (w := w),h,Multiset.card_singleton]
    obtain ⟨x,rfl⟩ := Finset.card_eq_one.mp hc
    rw [bag_singleton] at h
    exact ⟨⟨x,Multiset.singleton_inj.mp h⟩,rfl⟩

theorem singleton_inventory (same : SameInventory J w K z) (c : ℕ) :
    Nat.card {x // w x = c} = Nat.card {x // z x = c} :=
  (Nat.card_congr (singleEquiv J w c)).trans
    ((same {c}).trans (Nat.card_congr (singleEquiv K z c)).symm)

private theorem adjacent_of_connected_pair [DecidableEq V] {a x : V} (ne : a ≠ x)
    (conn : (J.induce (↑({a,x} : Finset V) : Set V)).Connected) : J.Adj a x := by
  let u : ↥({a,x} : Finset V) := ⟨a,by simp⟩
  let v : ↥({a,x} : Finset V) := ⟨x,by simp⟩
  have : Nontrivial ↥({a,x} : Finset V) := ⟨u,v,fun h => ne (congrArg Subtype.val h)⟩
  obtain ⟨b,hb⟩ := conn.preconnected.exists_adj_of_nontrivial u
  have ax : J.Adj a b.val := hb
  have bx : b.val = x := by
    rcases Finset.mem_insert.mp b.property with h|h
    · exact (ax.ne h.symm).elim
    · exact Finset.mem_singleton.mp h
  exact bx ▸ ax

private def neighborEquiv (a : V) (unique : ∀ x, w x = w a → x = a) (c : ℕ) :
    {x // J.Adj a x ∧ w x = c} ≃ coloredSets J w (w a ::ₘ {c}) := by
  classical
  let f (x : {x // J.Adj a x ∧ w x = c}) : coloredSets J w (w a ::ₘ {c}) :=
    ⟨{a,x.val},by
      constructor
      · rw [Finset.coe_pair]
        exact induce_pair_connected_of_adj x.property.1
      · rw [bag_insert (by simpa using x.property.1.ne),bag_singleton,x.property.2]⟩
  apply Equiv.ofBijective f
  constructor
  · intro x y h
    have eq : ({a,x.val} : Finset V) = {a,y.val} := congrArg Subtype.val h
    have hy : x.val ∈ ({a,y.val} : Finset V) := eq ▸ (by simp)
    exact Subtype.ext ((Finset.mem_insert.mp hy).resolve_left x.property.1.ne.symm |> Finset.mem_singleton.mp)
  · rintro ⟨s,conn,h⟩
    have ha : a ∈ s := (tag_mem_iff unique s).mp (by rw [h]; simp)
    have hc : s.card = 2 := by simp only [← bag_card (w := w),h,Multiset.card_cons,Multiset.card_singleton]
    have he : (s.erase a).card = 1 := by rw [card_erase_of_mem ha,hc]
    obtain ⟨x,hx⟩ := Finset.card_eq_one.mp he
    have ne : a ≠ x := by
      intro eq
      have bad : a ∈ s.erase a := by rw [hx,eq]; simp
      exact notMem_erase _ _ bad
    have decomp : s = {a,x} := by rw [← hx,insert_erase ha]
    subst s
    rw [bag_insert (by simpa using ne),bag_singleton] at h
    exact ⟨⟨x,adjacent_of_connected_pair ne conn,Multiset.singleton_inj.mp ((Multiset.cons_inj_right _).mp h)⟩,rfl⟩

/-- The color of any globally tagged leaf and its neighbor can be located on the rival graph. -/
theorem match_tagged_leaf [Finite V] [Finite W] (same : SameInventory J w K z)
    {a v : V} (unique : ∀ x, w x = w a → x = a) (av : J.Adj a v)
    (leaf : ∀ x, J.Adj a x → x = v) :
    ∃ b u : W, z b = w a ∧ (∀ y, z y = z b → y = b) ∧ K.Adj b u ∧
      (∀ y, K.Adj b y → y = u) ∧ z u = w v := by
  classical
  have one : Nat.card {x // w x = w a} = 1 :=
    Nat.card_eq_one_iff_exists.mpr ⟨⟨a,rfl⟩,fun x => Subtype.ext (unique x.val x.property)⟩
  obtain ⟨b,ub⟩ := Nat.card_eq_one_iff_exists.mp ((singleton_inventory same (w a)).symm.trans one)
  have uniq : ∀ y, z y = z b.val → y = b.val := fun y h =>
    congrArg Subtype.val (ub ⟨y,h.trans b.property⟩)
  have eq (c : ℕ) : Nat.card {x // J.Adj a x ∧ w x = c} = Nat.card {y // K.Adj b.val y ∧ z y = c} := by
    rw [Nat.card_congr (neighborEquiv a unique c), Nat.card_congr (neighborEquiv b.val uniq c),b.property]
    exact same _
  have only : Nat.card {x // J.Adj a x ∧ w x = w v} = 1 :=
    Nat.card_eq_one_iff_exists.mpr ⟨⟨v,av,rfl⟩,fun x => Subtype.ext (leaf x.val x.property.1)⟩
  obtain ⟨u,uu⟩ := Nat.card_eq_one_iff_exists.mp ((eq (w v)).symm.trans only)
  refine ⟨b.val,u.val,b.property,uniq,u.property.1,?_,u.property.2⟩
  intro y hy
  let e := Classical.choice (Finite.card_eq.mp (eq (z y)))
  let x := e.symm ⟨y,hy,rfl⟩
  have col : z y = w v := x.property.2.symm.trans (congrArg w (leaf x.val x.property.1))
  exact congrArg Subtype.val (uu ⟨y,hy,col⟩)

end
end StanleyContinuation
