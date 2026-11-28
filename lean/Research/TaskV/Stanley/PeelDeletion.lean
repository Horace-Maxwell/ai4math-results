import Research.TaskV.Stanley.PeelTagged

namespace StanleyContinuation
open Finset SimpleGraph
open scoped Classical
noncomputable section
variable {V W : Type*} {J : SimpleGraph V} {K : SimpleGraph W} {w : V → ℕ} {z : W → ℕ}

abbrev Away (a : V) := {x : V // x ≠ a}

abbrev pruned (J : SimpleGraph V) (a : V) : SimpleGraph (Away a) := J.induce {x | x ≠ a}

abbrev oldColors (w : V → ℕ) (a : V) (x : Away a) : ℕ := w x.val

private def ambient {a : V} (s : Finset (Away a)) : Finset V :=
  s.map (Function.Embedding.subtype _)

private theorem absent {a : V} (s : Finset (Away a)) : a ∉ ambient s :=
  fun h => s.property_of_mem_map_subtype h rfl

private theorem mem_ambient {a : V} (s : Finset (Away a)) (x : Away a) :
    x.val ∈ ambient s ↔ x ∈ s := by
  exact Finset.mem_map' _

private theorem bag_ambient {a : V} (s : Finset (Away a)) :
    colorBag w (ambient s) = colorBag (oldColors w a) s := by
  simp [colorBag,ambient,Multiset.map_map,oldColors]

private theorem conn_ambient {a : V} (s : Finset (Away a)) :
    (J.induce (ambient s : Set V)).Connected ↔ ((pruned J a).induce (s : Set (Away a))).Connected := by
  let f : ((pruned J a).induce (s : Set (Away a))) ≃g J.induce (ambient s : Set V) := {
    toFun := fun x => ⟨x.val.val,(mem_ambient s x.val).mpr x.property⟩
    invFun := fun x => ⟨⟨x.val,s.property_of_mem_map_subtype x.property⟩,(mem_ambient s _).mp x.property⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl
    map_rel_iff' := Iff.rfl }
  exact f.connected_iff.symm

/-- Adding a pendant vertex to a nonempty set preserves connectivity exactly on sets
containing its unique neighbor and connected before the addition. -/
theorem connected_insert_leaf_iff [Finite V] [DecidableEq V] {a v : V}
    (av : J.Adj a v) (leaf : ∀ x, J.Adj a x → x = v) {s : Finset V}
    (ha : a ∉ s) (hs : s.Nonempty) :
    (J.induce (↑(insert a s) : Set V)).Connected ↔ (J.induce (s : Set V)).Connected ∧ v ∈ s := by
  classical
  let T := J.induce (↑(insert a s) : Set V)
  let A : ↥(insert a s) := ⟨a,mem_insert_self _ _⟩
  constructor
  · intro h
    obtain ⟨x,hx⟩ := hs
    let X : ↥(insert a s) := ⟨x,mem_insert_of_mem hx⟩
    have : Nontrivial ↥(insert a s) :=
      ⟨A,X,fun he => ha (by have eq : a = x := congrArg Subtype.val he; rwa [eq])⟩
    obtain ⟨b,hb⟩ := h.preconnected.exists_adj_of_nontrivial A
    have eq : b.val = v := leaf b.val hb
    have hv : v ∈ s := eq ▸ ((mem_insert.mp b.property).resolve_left (show J.Adj a b.val from hb).ne.symm)
    have deg : T.degree A = 1 := degree_eq_one_iff_existsUnique_adj.mpr
      ⟨b,hb,fun y hy => Subtype.ext ((leaf y.val hy).trans eq.symm)⟩
    have c := h.induce_compl_singleton_of_degree_eq_one deg
    let f : (J.induce (s : Set V)) ≃g T.induce {A}ᶜ := {
      toFun := fun y => ⟨⟨y.val,mem_insert_of_mem y.property⟩,fun e =>
        ha (by have eq : y.val = a := congrArg Subtype.val e; rw [← eq]; exact y.property)⟩
      invFun := fun y => ⟨y.val.val,(mem_insert.mp y.val.property).resolve_left (fun e =>
        y.property (Subtype.ext e))⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_rel_iff' := Iff.rfl }
    exact ⟨f.connected_iff.mpr c,hv⟩
  · rintro ⟨h,hv⟩
    have pre : (J.induce {a}).Preconnected := .of_subsingleton
    have c := connected_induce_union pre h.preconnected (Set.mem_singleton a) hv av
    rw [Finset.coe_insert]
    simpa only [Set.singleton_union] using c

private def deletedEquiv {a : V} (unique : ∀ x, w x = w a → x = a) {M : Multiset ℕ}
    (noTag : w a ∉ M) :
    coloredSets (pruned J a) (oldColors w a) M ≃ coloredSets J w M := by
  classical
  let f (t : coloredSets (pruned J a) (oldColors w a) M) : coloredSets J w M :=
    ⟨ambient t.val,(conn_ambient _).mpr t.property.1,(bag_ambient _).trans t.property.2⟩
  apply Equiv.ofBijective f
  constructor
  · intro x y h
    exact Subtype.ext (Finset.map_injective _ (congrArg Subtype.val h))
  · rintro ⟨s,conn,bag⟩
    have ha : a ∉ s := fun h => noTag (bag ▸ (tag_mem_iff unique s).mpr h)
    let t := s.subtype (· ≠ a)
    have ht : ambient t = s := subtype_map_of_mem (fun _ hx e => ha (e ▸ hx))
    have c := (conn_ambient (J := J) t).mp (ht ▸ conn)
    have b := (bag_ambient (w := w) t).symm.trans (ht ▸ bag)
    exact ⟨⟨t,c,b⟩,Subtype.ext ht⟩

private theorem deleted_no_tag {a : V} (unique : ∀ x, w x = w a → x = a)
    (s : Finset (Away a)) : w a ∉ colorBag (oldColors w a) s := by
  rw [← bag_ambient,tag_mem_iff unique]
  exact absent s

private theorem emptyDeleted {a : V} {M : Multiset ℕ} (ua : ∀ x, w x = w a → x = a) (tag : w a ∈ M) :
    IsEmpty (coloredSets (pruned J a) (oldColors w a) M) :=
  ⟨fun t => deleted_no_tag ua t.val (by rw [t.property.2]; exact tag)⟩

theorem same_deleted {a : V} {b : W} (same : SameInventory J w K z)
    (ua : ∀ x, w x = w a → x = a) (ub : ∀ y, z y = z b → y = b) (ab : w a = z b) :
    SameInventory (pruned J a) (oldColors w a) (pruned K b) (oldColors z b) := by
  intro M
  by_cases ha : w a ∈ M
  · let := emptyDeleted (J := J) ua ha
    let := emptyDeleted (J := K) ub (ab ▸ ha)
    rw [Nat.card_of_isEmpty,Nat.card_of_isEmpty]
  · rw [Nat.card_congr (deletedEquiv (J := J) ua ha),
        Nat.card_congr (deletedEquiv (J := K) ub (ab ▸ ha))]
    exact same M

/-- The coefficient counting sets which contain the neighbor, after deleting a unique-color leaf. -/
def pointedSets (J : SimpleGraph V) (w : V → ℕ) (v : V) (M : Multiset ℕ) :=
  {t : coloredSets J w M // v ∈ t.val}

instance [Finite V] (v : V) (M : Multiset ℕ) : Finite (pointedSets J w v M) := by
  unfold pointedSets; infer_instance

private def pointedEquiv [Finite V] {a v : V} (unique : ∀ x, w x = w a → x = a)
    (av : J.Adj a v) (leaf : ∀ x, J.Adj a x → x = v) {M : Multiset ℕ} (nonzero : M ≠ 0) :
    pointedSets (pruned J a) (oldColors w a) ⟨v,av.ne.symm⟩ M ≃ coloredSets J w (w a ::ₘ M) := by
  classical
  let f (r : pointedSets (pruned J a) (oldColors w a) ⟨v,av.ne.symm⟩ M) :
      coloredSets J w (w a ::ₘ M) := by
    let t := r.val.val
    have hv : v ∈ ambient t := (mem_ambient t ⟨v,av.ne.symm⟩).mpr r.property
    refine ⟨insert a (ambient t), (connected_insert_leaf_iff av leaf (absent t) ⟨v,hv⟩).mpr
        ⟨(conn_ambient _).mpr r.val.property.1,hv⟩,?_⟩
    rw [bag_insert (absent t),bag_ambient]
    exact congrArg _ r.val.property.2
  apply Equiv.ofBijective f
  constructor
  · intro x y h
    have e : insert a (ambient x.val.val) = insert a (ambient y.val.val) := congrArg Subtype.val h
    apply Subtype.ext
    apply Subtype.ext
    apply Finset.map_injective (Function.Embedding.subtype _)
    have d := congrArg (fun s => s.erase a) e
    simp only [Finset.erase_insert (absent _)] at d
    exact d
  · rintro ⟨s,cs,bag⟩
    have ha : a ∈ s := (tag_mem_iff unique s).mp (by rw [bag]; simp)
    let r := s.erase a
    have hr : a ∉ r := notMem_erase _ _
    have ins : insert a r = s := insert_erase ha
    have br : colorBag w r = M := by
      rw [← ins,bag_insert hr] at bag
      exact (Multiset.cons_inj_right _).mp bag
    have non : r.Nonempty := Finset.nonempty_iff_ne_empty.mpr (fun e => nonzero (by simp [← br,e,colorBag]))
    obtain ⟨cr,hv⟩ := (connected_insert_leaf_iff av leaf hr non).mp (ins ▸ cs)
    let t := r.subtype (· ≠ a)
    have ht : ambient t = r := subtype_map_of_mem (fun _ hx e => hr (e ▸ hx))
    have c := (conn_ambient (J := J) t).mp (ht ▸ cr)
    have b := (bag_ambient (w := w) t).symm.trans (ht ▸ br)
    have mem := (mem_ambient t ⟨v,av.ne.symm⟩).mp (ht ▸ hv)
    exact ⟨⟨⟨t,c,b⟩,mem⟩,Subtype.ext ((congrArg (insert a) ht).trans ins)⟩

private theorem emptyPointed (L : SimpleGraph V) (c : V → ℕ) (p : V) : IsEmpty (pointedSets L c p 0) :=
  ⟨fun x => by
    have h : (colorBag c x.val.val).card = 0 := by rw [x.val.property.2]; rfl
    rw [bag_card,Finset.card_eq_zero] at h
    exact Finset.notMem_empty _ (h ▸ x.property)⟩

theorem same_pointed_deleted [Finite V] [Finite W] {a v : V} {b u : W}
    (same : SameInventory J w K z) (ua : ∀ x, w x = w a → x = a)
    (ub : ∀ y, z y = z b → y = b) (ab : w a = z b)
    (av : J.Adj a v) (bv : K.Adj b u)
    (la : ∀ x, J.Adj a x → x = v) (lb : ∀ y, K.Adj b y → y = u) (M : Multiset ℕ) :
    Nat.card (pointedSets (pruned J a) (oldColors w a) ⟨v,av.ne.symm⟩ M) =
    Nat.card (pointedSets (pruned K b) (oldColors z b) ⟨u,bv.ne.symm⟩ M) := by
  by_cases zero : M = 0
  · subst M
    let := emptyPointed (pruned J a) (oldColors w a) ⟨v,av.ne.symm⟩
    let := emptyPointed (pruned K b) (oldColors z b) ⟨u,bv.ne.symm⟩
    rw [Nat.card_of_isEmpty,Nat.card_of_isEmpty]
  · rw [Nat.card_congr (pointedEquiv ua av la zero),Nat.card_congr (pointedEquiv ub bv lb zero),ab]
    exact same _

end
end StanleyContinuation
