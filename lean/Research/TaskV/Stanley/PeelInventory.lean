import Research.TaskV.Stanley.PeelLabelings

namespace StanleyContinuation
open Finset SimpleGraph
open scoped Classical
noncomputable section

def colorBag {V : Type*} (w : V → ℕ) (s : Finset V) : Multiset ℕ := s.val.map w

def coloredSets {V : Type*} (J : SimpleGraph V) (w : V → ℕ) (M : Multiset ℕ) :=
  {s : Finset V // (J.induce (s : Set V)).Connected ∧ colorBag w s = M}

instance {V : Type*} [Finite V] (J : SimpleGraph V) (w : V → ℕ) (M : Multiset ℕ) :
    Finite (coloredSets J w M) := by unfold coloredSets; infer_instance

private theorem bag_full_iso {V I : Type*} [Fintype V] [Fintype I] {w : V → ℕ} {c : I → ℕ}
    (e : ColorIso w c) : colorBag w univ = colorBag c univ := by
  unfold colorBag
  rw [← Multiset.map_univ_val_equiv e.val, Multiset.map_map]
  exact congrArg (fun f : V → ℕ => (univ : Finset V).val.map f) (funext fun v => (e.property v).symm)

private theorem colorBag_count {A : Type*} [Fintype A] (g : A → ℕ) (j : ℕ) :
      (colorBag g univ).count j = Nat.card {v : A // g v = j} := by
    rw [colorBag,Multiset.count_map,Nat.card_eq_fintype_card,Fintype.card_subtype]
    change (univ.filter (fun v => j = g v)).card = _
    apply congrArg Finset.card
    exact Finset.filter_congr fun _ _ => eq_comm

private theorem iso_of_bag {V I : Type*} [Fintype V] [Fintype I] {w : V → ℕ} {c : I → ℕ}
    (eq : colorBag w univ = colorBag c univ) : Nonempty (ColorIso w c) := by
  classical
  have h (j : ℕ) : Nat.card {v : V // w v = j} = Nat.card {x : I // c x = j} := by
    exact (colorBag_count w j).symm.trans ((congrArg (Multiset.count j) eq).trans (colorBag_count c j))
  let fiber (j : ℕ) := Classical.choice (Finite.card_eq.mp (h j))
  exact ⟨⟨Equiv.ofFiberEquiv fiber,Equiv.ofFiberEquiv_map fiber⟩⟩

private theorem split_inventory {V : Type*} [Fintype V] (w : V → ℕ) (s : Finset V) :
    colorBag w s + colorBag (fun x : Exterior s => w x.val) univ = colorBag w univ := by
  classical
  have extbag : colorBag (fun x : Exterior s => w x.val) univ = colorBag w sᶜ := by
    unfold colorBag
    have h := univ_val_map_subtype_restrict w (fun x => x ∉ s)
    simpa only [Subtype.restrict_def, Function.comp_def, filter_notMem_eq_sdiff, compl_eq_univ_sdiff] using h
  rw [extbag]
  unfold colorBag
  rw [← Multiset.map_add]
  apply congrArg
  change (s.disjUnion sᶜ disjoint_compl_right).val = univ.val
  rw [disjUnion_eq_union, union_compl]
  
theorem exterior_labelings_iff {V I : Type*} [Fintype V] [Fintype I] (w : V → ℕ) (c : I → ℕ)
    {M : Multiset ℕ} (total : M + colorBag c univ = colorBag w univ) (s : Finset V) :
    Nonempty (Labelings w c s) ↔ colorBag w s = M := by
  have h := (split_inventory w s).trans total.symm
  constructor
  · rintro ⟨e⟩
    rw [bag_full_iso e] at h
    exact add_right_cancel h
  · intro e
    rw [e] at h
    exact iso_of_bag (add_left_cancel h)

theorem atomic_profile_formula {V I : Type*} [Fintype V] [Fintype I] (J : SimpleGraph V)
    (w : V → ℕ) (c : I → ℕ) (M : Multiset ℕ)
    (total : M + colorBag c univ = colorBag w univ)
    (atom : ∀ i (s : Finset V), 2 ≤ s.card → (∑ x ∈ s, w x) ≠ c i) :
    Nat.card (WeightedBlocks J w (fun o : Option I => o.elim M.sum c)) =
      Nat.card (coloredSets J w M) * Nat.card (ColorIso c c) := by
  rw [atomic_partition_count J w c M.sum atom]
  congr 1
  apply Nat.card_congr
  apply Equiv.subtypeEquivRight
  intro s
  constructor
  · rintro ⟨conn,_,labels⟩
    exact ⟨conn,(exterior_labelings_iff w c total s).mp labels⟩
  · rintro ⟨conn,bag⟩
    exact ⟨conn,congrArg Multiset.sum bag,(exterior_labelings_iff w c total s).mpr bag⟩

/-- A proper atomic weighting on the core, in the domain used by the weighted block counts. -/
def atomicColors {V : Type*} (w : V → ℕ) : Prop :=
  ∀ x (s : Finset V), 2 ≤ s.card → (∑ v ∈ s, w v) ≠ w x

theorem atomicColors_transport {V W : Type*} (w : V → ℕ) (z : W → ℕ)
    (e : ColorIso w z) (atom : atomicColors w) : atomicColors z := by
  intro x s hs h
  obtain ⟨a,rfl⟩ := e.val.surjective x
  let t := s.map e.val.symm.toEmbedding
  have ht : 2 ≤ t.card := by simpa only [t,card_map] using hs
  apply atom a t ht
  have weights (y : W) : w (e.val.symm y) = z y := by
    simpa only [Equiv.apply_symm_apply] using (e.property (e.val.symm y)).symm
  simpa only [t,sum_map,Equiv.coe_toEmbedding,weights,e.property] using h

private theorem compare_witness {V W : Type*} [Fintype V] [Fintype W]
    (J : SimpleGraph V) (K : SimpleGraph W) (w : V → ℕ) (z : W → ℕ)
    (tw : ∀ x, 2 ≤ w x) (aw : atomicColors w) (e : ColorIso w z)
    (s : Finset V) (cs : (J.induce (s : Set V)).Connected)
    (blocks : ∀ (p : Option (Exterior s) → ℕ), (∀ i, 2 ≤ p i) →
      Nat.card (WeightedBlocks J w p) = Nat.card (WeightedBlocks K z p)) :
    Nat.card (coloredSets J w (colorBag w s)) = Nat.card (coloredSets K z (colorBag w s)) := by
  classical
  let c (v : Exterior s) := w v.val
  let M := colorBag w s
  have total := split_inventory w s
  have total' := total.trans (bag_full_iso e)
  have left := atomic_profile_formula J w c M total (fun i => aw i.val)
  have az := atomicColors_transport w z e aw
  have right := atomic_profile_formula K z c M total' (fun i t ht => by
    simpa only [c, ← e.property i.val] using az (e.val i.val) t ht)
  obtain ⟨x⟩ := cs.nonempty
  have dm : 2 ≤ M.sum := (tw x.val).trans
    (single_le_sum (fun v _ => Nat.zero_le (w v)) x.property)
  have eq := blocks (fun o => o.elim M.sum c) (fun i => by
    cases i with
    | none => exact dm
    | some j => exact tw j.val)
  rw [left,right] at eq
  have ne : Nonempty (ColorIso c c) := ⟨⟨Equiv.refl _,fun _ => rfl⟩⟩
  exact Nat.eq_of_mul_eq_mul_right Nat.card_pos eq

theorem coreColoredSets_of_sameCSF {n m : ℕ} {G : SimpleGraph (Fin n)} {H : SimpleGraph (Fin m)}
    (tg : G.IsTree) (th : H.IsTree) (large : 2 ≤ (core G).card)
    (proper : ∀ v ∈ core G, 2 ≤ coreWeight G v)
    (atoms : ∀ v ∈ core G, ∀ P : Finset (Fin n), P ⊆ core G → 2 ≤ P.card →
      (∑ u ∈ P, coreWeight G u) ≠ coreWeight G v) (same : SameCSF G H)
    (M : Multiset ℕ) :
    Nat.card (coloredSets (coreGraph G) (fun x => coreWeight G x) M) =
      Nat.card (coloredSets (coreGraph H) (fun x => coreWeight H x) M) := by
  classical
  let w (x : ↥(core G)) := coreWeight G x
  let z (x : ↥(core H)) := coreWeight H x
  have hn : 2 ≤ n := large.trans (by simpa only [Fintype.card_fin] using card_le_univ (core G))
  obtain ⟨eqv,weights⟩ := coreWeights_of_sameCSF tg th hn proper same
  let e : ColorIso w z := ⟨eqv,weights⟩
  let inv : ColorIso z w := ⟨eqv.symm,fun x => by
    simpa only [Equiv.apply_symm_apply] using (weights (eqv.symm x)).symm⟩
  have aw : atomicColors w := by
    intro v t ht
    let emb := Function.Embedding.subtype (fun x => x ∈ core G)
    have ins : t.map emb ⊆ core G := fun _ h => t.property_of_mem_map_subtype h
    have h := atoms v.val v.property (t.map emb) ins (by simpa only [card_map] using ht)
    simpa only [sum_map,emb,Function.Embedding.coe_subtype,w] using h
  have pw (x) : 2 ≤ w x := proper _ x.property
  have pz (y) : 2 ≤ z y := (pw (eqv.symm y)).trans_eq (inv.property y)
  have cg := card_pos.mp (by omega : 0 < (core G).card)
  obtain ⟨v,hv⟩ := cg
  have ch : (core H).Nonempty := ⟨(eqv ⟨v,hv⟩).val,(eqv ⟨v,hv⟩).property⟩
  by_cases hg : Nonempty (coloredSets (coreGraph G) w M)
  · obtain ⟨⟨s,cs,rfl⟩⟩ := hg
    exact compare_witness _ _ w z pw aw e s cs (sameCoreBlocks_of_sameCSF tg th ⟨v,hv⟩ ch same)
  by_cases hh : Nonempty (coloredSets (coreGraph H) z M)
  · obtain ⟨⟨s,cs,rfl⟩⟩ := hh
    exact (compare_witness _ _ z w pz (atomicColors_transport w z e aw) inv s cs
      (fun p hp => (sameCoreBlocks_of_sameCSF tg th ⟨v,hv⟩ ch same p hp).symm)).symm
  have : IsEmpty (coloredSets (coreGraph G) w M) := not_nonempty_iff.mp hg
  have : IsEmpty (coloredSets (coreGraph H) z M) := not_nonempty_iff.mp hh
  change Nat.card (coloredSets _ w M) = Nat.card (coloredSets _ z M)
  rw [Nat.card_of_isEmpty,Nat.card_of_isEmpty]

theorem peel_coloredSets_of_sameCSF {n m : ℕ} {G : SimpleGraph (Fin n)} {H : SimpleGraph (Fin m)}
    (tg : G.IsTree) (th : H.IsTree) (peel : PeelingWeights G) (same : SameCSF G H)
    (M : Multiset ℕ) :
    Nat.card (coloredSets (coreGraph G) (fun x => coreWeight G x) M) =
      Nat.card (coloredSets (coreGraph H) (fun x => coreWeight H x) M) :=
  coreColoredSets_of_sameCSF tg th peel.1 peel.2.1 peel.2.2.1 same M

end
end StanleyContinuation
