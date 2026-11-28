import Research.TaskV.Stanley.PeelDeletion

namespace StanleyContinuation
open Finset SimpleGraph
open scoped Classical
noncomputable section
variable {V W : Type*} {J : SimpleGraph V} {K : SimpleGraph W} {w : V → ℕ} {z : W → ℕ}

def retag (w : V → ℕ) (v : V) (tag : ℕ) (x : V) : ℕ := if x = v then tag else w x

private theorem bag_without {v : V} (tag : ℕ) {s : Finset V} (h : v ∉ s) :
    colorBag (retag w v tag) s = colorBag w s :=
  Multiset.map_congr rfl (fun x hx => by
    have ne : x ≠ v := fun eq => h (eq ▸ hx)
    simp [retag,ne])

private theorem retag_mem {v : V} {tag : ℕ} (fresh : ∀ x, w x ≠ tag) (s : Finset V) :
    tag ∈ colorBag (retag w v tag) s ↔ v ∈ s := by
  have hv : retag w v tag v = tag := by simp [retag]
  have unique : ∀ x, retag w v tag x = retag w v tag v → x = v := by
    intro x h
    by_contra ne
    exact fresh x (by simpa [retag,ne] using h)
  simpa only [hv] using tag_mem_iff unique s

private theorem retag_bags [DecidableEq V] {v : V} (tag : ℕ) {s : Finset V} (h : v ∈ s) :
    colorBag (retag w v tag) s = tag ::ₘ colorBag w (s.erase v) ∧
    colorBag w s = w v ::ₘ colorBag w (s.erase v) := by
  have no : v ∉ s.erase v := notMem_erase _ _
  constructor
  · calc
      _ = colorBag (retag w v tag) (insert v (s.erase v)) := congrArg _ (insert_erase h).symm
      _ = _ := by rw [bag_insert no,bag_without _ no]; simp [retag]
  · calc
      _ = colorBag w (insert v (s.erase v)) := congrArg _ (insert_erase h).symm
      _ = _ := bag_insert no

private def restrictSets (d w : V → ℕ) (L : SimpleGraph V) (M N : Multiset ℕ)
    (p : Finset V → Prop) (h : ∀ s, colorBag d s = M ↔ colorBag w s = N ∧ p s) :
    coloredSets L d M ≃ {t : coloredSets L w N // p t.val} where
  toFun t := ⟨⟨t.val,t.property.1,((h _).mp t.property.2).1⟩,((h _).mp t.property.2).2⟩
  invFun t := ⟨t.val.val,t.val.property.1,(h _).mpr ⟨t.val.property.2,t.property⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

private theorem retag_present {tag : ℕ} (v : V) (fresh : ∀ x, w x ≠ tag)
    {M : Multiset ℕ} (has : tag ∈ M) :
    Nat.card (coloredSets J (retag w v tag) M) =
      Nat.card (pointedSets J w v (w v ::ₘ M.erase tag)) := by
  classical
  apply Nat.card_congr
  apply restrictSets _ w J M _ (fun s => v ∈ s)
  intro s
  constructor
  · intro eq
    have hv := (retag_mem (v := v) fresh s).mp (eq ▸ has)
    obtain ⟨changeBag,oldBag⟩ := retag_bags (w := w) tag hv
    refine ⟨?_,hv⟩
    rw [oldBag,← eq,changeBag,Multiset.erase_cons_head]
  · rintro ⟨eq,hv⟩
    obtain ⟨changeBag,oldBag⟩ := retag_bags (w := w) tag hv
    rw [oldBag] at eq
    rw [changeBag,(Multiset.cons_inj_right _).mp eq,Multiset.cons_erase has]

private theorem retag_absent {tag : ℕ} (v : V) (fresh : ∀ x, w x ≠ tag)
    {M : Multiset ℕ} (no : tag ∉ M) :
    Nat.card (coloredSets J (retag w v tag) M) =
      Nat.card {t : coloredSets J w M // v ∉ t.val} := by
  apply Nat.card_congr
  apply restrictSets _ w J M M (fun s => v ∉ s)
  intro s
  constructor
  · intro eq
    have hv : v ∉ s := fun h => no (eq ▸ (retag_mem fresh s).mpr h)
    exact ⟨(bag_without tag hv).symm.trans eq,hv⟩
  · rintro ⟨eq,hv⟩
    exact (bag_without tag hv).trans eq

private theorem complement_count [Finite V] (v : V) (M : Multiset ℕ) :
    Nat.card {t : coloredSets J w M // v ∉ t.val} =
      Nat.card (coloredSets J w M) - Nat.card (pointedSets J w v M) := by
  classical
  have e := Nat.card_congr (Equiv.sumCompl (fun t : coloredSets J w M => v ∈ t.val))
  rw [Nat.card_sum] at e
  unfold pointedSets
  omega

/-- Transfer the deleted leaf's color to its neighbor. In the reduced graph it is globally fresh. -/
theorem same_retag [Finite V] [Finite W] (same : SameInventory J w K z) {v : V} {u : W}
    {tag : ℕ} (fresh : ∀ x, w x ≠ tag) (fresh' : ∀ y, z y ≠ tag) (vu : w v = z u)
    (pointed : ∀ M, Nat.card (pointedSets J w v M) = Nat.card (pointedSets K z u M)) :
    SameInventory J (retag w v tag) K (retag z u tag) := by
  intro M
  by_cases has : tag ∈ M
  · rw [retag_present v fresh has,retag_present u fresh' has,vu,pointed]
  · rw [retag_absent v fresh has,retag_absent u fresh' has,complement_count,complement_count,same,pointed]

/-- A complete deletion step. Only the first graph is assumed to have the specified tagged leaf.
The rival's matching leaf, its neighbor's original color, and the entire new inventory are deduced. -/
theorem peel_step [Finite V] [Finite W] (same : SameInventory J w K z)
    {a v : V} (unique : ∀ x, w x = w a → x = a) (av : J.Adj a v)
    (leaf : ∀ x, J.Adj a x → x = v) :
    ∃ b u : W, ∃ bu : K.Adj b u, z b = w a ∧ (∀ y, z y = z b → y = b) ∧
      (∀ y, K.Adj b y → y = u) ∧ z u = w v ∧
      SameInventory (pruned J a) (retag (oldColors w a) ⟨v,av.ne.symm⟩ (w a))
        (pruned K b) (retag (oldColors z b) ⟨u,bu.ne.symm⟩ (w a)) := by
  obtain ⟨b,u,ab,ub,bu,lb,vu⟩ := match_tagged_leaf same unique av leaf
  refine ⟨b,u,bu,ab,ub,lb,vu,same_retag (same_deleted same unique ub ab.symm)
    (fun x h => x.property (unique x.val h)) (fun x h => x.property (ub x.val (h.trans ab.symm)))
    vu.symm (same_pointed_deleted same unique ub ab.symm av bu leaf lb)⟩

/-- The ordinary CSF supplies the whole input to a first pruning step on the two unrooted cores. -/
theorem core_peel_step_of_sameCSF {n m : ℕ} {G : SimpleGraph (Fin n)} {H : SimpleGraph (Fin m)}
    (tg : G.IsTree) (th : H.IsTree) (pw : PeelingWeights G) (same : SameCSF G H)
    {a v : ↥(core G)} (unique : ∀ x : ↥(core G), coreWeight G x = coreWeight G a → x = a)
    (av : (coreGraph G).Adj a v) (leaf : ∀ x, (coreGraph G).Adj a x → x = v) :
    ∃ b u : ↥(core H), ∃ bu : (coreGraph H).Adj b u, coreWeight H b = coreWeight G a ∧
      (∀ y : ↥(core H), coreWeight H y = coreWeight H b → y = b) ∧
      (∀ y, (coreGraph H).Adj b y → y = u) ∧ coreWeight H u = coreWeight G v ∧
      SameInventory (pruned (coreGraph G) a)
        (retag (oldColors (fun x : ↥(core G) => coreWeight G x) a) ⟨v,av.ne.symm⟩ (coreWeight G a))
        (pruned (coreGraph H) b)
        (retag (oldColors (fun y : ↥(core H) => coreWeight H y) b) ⟨u,bu.ne.symm⟩ (coreWeight G a)) :=
  peel_step (peel_coloredSets_of_sameCSF tg th pw same) unique av leaf

end
end StanleyContinuation
