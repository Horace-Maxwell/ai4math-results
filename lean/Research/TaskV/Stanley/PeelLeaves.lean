import Research.TaskV.Stanley.PeelRetag

namespace StanleyContinuation
open SimpleGraph
open scoped Classical
noncomputable section
variable {V : Type*} {J : SimpleGraph V} {w : V → ℕ}

/-- A leaf whose color is repeated somewhere else in the graph. -/
def repeatedLeaf (J : SimpleGraph V) (w : V → ℕ) (x : V) : Prop :=
  (∃! y, J.Adj x y) ∧ ∃ y, y ≠ x ∧ w y = w x

def atMostOneRepeatedLeaf (J : SimpleGraph V) (w : V → ℕ) : Prop :=
  ∀ x y, repeatedLeaf J w x → repeatedLeaf J w y → x = y

theorem choose_tagged_leaf [Fintype V] [Nontrivial V] (tree : J.IsTree)
    (few : atMostOneRepeatedLeaf J w) :
    ∃ a v : V, (∀ x, w x = w a → x = a) ∧ J.Adj a v ∧ (∀ y, J.Adj a y → y = v) := by
  classical
  obtain ⟨i,j,ne,di,dj⟩ := tree.exists_ne_and_degree_eq_one
  have choose (a : V) (one : J.degree a = 1) (good : ¬repeatedLeaf J w a) :
      ∃ v, (∀ x, w x = w a → x = a) ∧ J.Adj a v ∧ (∀ y, J.Adj a y → y = v) := by
    have h := J.degree_eq_one_iff_existsUnique_adj.mp one
    obtain ⟨v,av,only⟩ := h
    refine ⟨v,?_,av,only⟩
    intro x eq
    by_contra distinct
    exact good ⟨⟨v,av,only⟩,x,distinct,eq⟩
  by_cases bad : repeatedLeaf J w i
  · exact ⟨j,choose j dj (fun bj => ne (few i j bad bj))⟩
  · exact ⟨i,choose i di bad⟩

theorem retag_equal_iff (c : V → ℕ) (v : V) (tag : ℕ) (fresh : ∀ x, c x ≠ tag) (x : V) :
    retag c v tag x = tag ↔ x = v := by
  by_cases eq : x = v <;> simp [retag,eq,fresh]

theorem repeatedLeaf_before_deletion {a v : V} (ua : ∀ x, w x = w a → x = a)
    (av : J.Adj a v) (leaf : ∀ x, J.Adj a x → x = v) (x : Away a)
    (bad : repeatedLeaf (pruned J a) (retag (oldColors w a) ⟨v,av.ne.symm⟩ (w a)) x) :
    repeatedLeaf J w x.val := by
  classical
  let u : Away a := ⟨v,av.ne.symm⟩
  let c := retag (oldColors w a) u (w a)
  have fresh (y : Away a) : oldColors w a y ≠ w a := fun h => y.property (ua y.val h)
  obtain ⟨⟨p,xp,only⟩,y,ne,eq⟩ := bad
  have color : c y = c x := eq
  have tagged (t : Away a) : c t = w a ↔ t = u := retag_equal_iff _ _ _ fresh _
  have xu : x ≠ u := fun h => ne (((tagged y).mp (color.trans ((tagged x).mpr h))).trans h.symm)
  have yu : y ≠ u := fun h => xu ((tagged x).mp (color.symm.trans ((tagged y).mpr h)))
  have xv : x.val ≠ v := fun h => xu (Subtype.ext h)
  refine ⟨⟨p.val,xp,?_⟩,y.val,(fun h => ne (Subtype.ext h)),?_⟩
  · intro k hk
    have ka : k ≠ a := fun h => xv (leaf x.val (h ▸ hk).symm)
    exact congrArg Subtype.val (only ⟨k,ka⟩ hk)
  · simpa [c,retag,xu,yu] using color

theorem atMostOne_after_deletion {a v : V} (few : atMostOneRepeatedLeaf J w)
    (ua : ∀ x, w x = w a → x = a) (av : J.Adj a v) (leaf : ∀ x, J.Adj a x → x = v) :
    atMostOneRepeatedLeaf (pruned J a) (retag (oldColors w a) ⟨v,av.ne.symm⟩ (w a)) := by
  intro x y hx hy
  exact Subtype.ext (few _ _ (repeatedLeaf_before_deletion ua av leaf x hx)
    (repeatedLeaf_before_deletion ua av leaf y hy))

theorem tree_after_deletion [Finite V] {a v : V} (tree : J.IsTree) (av : J.Adj a v)
    (leaf : ∀ x, J.Adj a x → x = v) : (pruned J a).IsTree := by
  classical
  let := Fintype.ofFinite V
  have deg : J.degree a = 1 := J.degree_eq_one_iff_existsUnique_adj.mpr ⟨v,av,leaf⟩
  exact ⟨tree.connected.induce_compl_singleton_of_degree_eq_one deg,tree.isAcyclic.induce _⟩

end
end StanleyContinuation
