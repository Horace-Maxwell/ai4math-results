import Research.TaskV.Stanley.PeelPartitions

namespace StanleyContinuation
open Finset SimpleGraph
noncomputable section

/-- A weight-preserving enumeration of one finite colored set by another. -/
abbrev ColorIso {V I : Type*} (w : V → ℕ) (c : I → ℕ) :=
  {e : V ≃ I // ∀ x, c (e x) = w x}

abbrev Exterior {V : Type*} (s : Finset V) := {x : V // x ∉ s}

private def recolorEquiv {V I : Type*} {w : V → ℕ} {c : I → ℕ}
    (b : ColorIso w c) : ColorIso w c ≃ ColorIso c c where
  toFun f := ⟨b.val.symm.trans f.val, fun i => by
    obtain ⟨x,rfl⟩ := b.val.surjective i
    simpa only [Equiv.trans_apply, Equiv.symm_apply_apply] using (f.property x).trans (b.property x).symm⟩
  invFun f := ⟨b.val.trans f.val, fun x => (f.property _).trans (b.property x)⟩
  left_inv f := Subtype.ext (Equiv.ext fun x => by simp)
  right_inv f := Subtype.ext (Equiv.ext fun x => by simp)

def Eligible {V I : Type*} (J : SimpleGraph V) (w : V → ℕ) (c : I → ℕ) (d : ℕ) :=
  {s : Finset V // (J.induce (s : Set V)).Connected ∧
    (∑ x ∈ s, w x) = d ∧ Nonempty (ColorIso (fun x : Exterior s => w x.val) c)}

abbrev Labelings {V I : Type*} (w : V → ℕ) (c : I → ℕ) (s : Finset V) :=
  ColorIso (fun x : Exterior s => w x.val) c

abbrev Presented {V I : Type*} (J : SimpleGraph V) (w : V → ℕ) (c : I → ℕ) (d : ℕ) :=
  Σ s : Eligible J w c d, Labelings w c s.val

private def encode {V I : Type*} {w : V → ℕ} {c : I → ℕ} {s : Finset V}
    (e : Labelings w c s) (x : V) : Option I := by
  classical exact if h : x ∈ s then none else some (e.val ⟨x,h⟩)

private theorem encode_fiber_none {V I : Type*} [Fintype V] {w : V → ℕ} {c : I → ℕ}
    {s : Finset V} (e : Labelings w c s) : weightFiber (encode e) none = s := by
  classical
  ext x
  by_cases h : x ∈ s <;> simp [encode,h]

private theorem encode_fiber_some {V I : Type*} [Fintype V] {w : V → ℕ} {c : I → ℕ}
    {s : Finset V} (e : Labelings w c s) (i : I) :
    weightFiber (encode e) (some i) = {(e.val.symm i).val} := by
  classical
  ext x
  by_cases h : x ∈ s
  · have ne : x ≠ (e.val.symm i).val := fun eq => (e.val.symm i).property (eq ▸ h)
    simp [encode,h,ne]
  · simp only [mem_weightFiber, encode, dite_eq_right h, Option.some.injEq, mem_singleton]
    exact e.val.eq_symm_apply.symm.trans Subtype.ext_iff

private def present_block {V I : Type*} [Fintype V] {J : SimpleGraph V}
    {w : V → ℕ} {c : I → ℕ} {d : ℕ} (p : Presented J w c d) :
    WeightedBlocks J w (fun o : Option I => o.elim d c) := by
  classical
  refine ⟨encode p.2,fun o => ?_⟩
  cases o with
  | none => rw [encode_fiber_none]; exact ⟨p.1.property.2.1,p.1.property.1⟩
  | some i =>
    rw [encode_fiber_some, sum_singleton, coe_singleton]
    refine ⟨?_,(SimpleGraph.connected_iff _).mpr ⟨fun _ _ => Reachable.of_subsingleton,inferInstance⟩⟩
    change w _ = c i
    simpa only [Equiv.apply_symm_apply] using (p.2.property (p.2.val.symm i)).symm

private theorem present_injective {V I : Type*} [Fintype V] (J : SimpleGraph V)
    (w : V → ℕ) (c : I → ℕ) (d : ℕ) : Function.Injective (@present_block V I _ J w c d) := by
  classical
  rintro ⟨⟨s,hs⟩,e⟩ ⟨⟨t,ht⟩,f⟩ eq
  have fixed : encode e = encode f := congrArg Subtype.val eq
  have st : s = t := (encode_fiber_none e).symm.trans ((congrArg (fun g => weightFiber g none) fixed).trans
    (encode_fiber_none f))
  subst t
  have ef : e = f := by
    apply Subtype.ext
    apply Equiv.ext
    intro x
    have h := congrFun fixed x.val
    simpa only [encode, dite_eq_right x.property, Option.some.injEq] using h
  subst f
  rfl

/-- Every block with an atomic prescribed mass consists of one core vertex. -/
private theorem atomic_fiber {V I : Type*} [Fintype V] {J : SimpleGraph V} {w : V → ℕ} {c : I → ℕ}
    {d : ℕ} (atom : ∀ i (s : Finset V), 2 ≤ s.card → (∑ x ∈ s, w x) ≠ c i)
    (f : WeightedBlocks J w (fun o : Option I => o.elim d c)) (i : I) :
    ∃! v, f.val v = some i := by
  classical
  let t := weightFiber f.val (some i)
  obtain ⟨q⟩ := (f.property (some i)).2.nonempty
  have pos : 0 < t.card := card_pos.mpr ⟨q.val,q.property⟩
  have small : ¬2 ≤ t.card := fun h => atom i t h (f.property (some i)).1
  obtain ⟨u,hu⟩ := card_eq_one.mp (by omega : t.card = 1)
  have iff (v : V) : f.val v = some i ↔ v = u := by
    rw [← mem_weightFiber]
    change v ∈ t ↔ v = u
    rw [hu,mem_singleton]
  exact ⟨u,(iff u).mpr rfl,fun v h => (iff v).mp h⟩

private theorem present_surjective {V I : Type*} [Fintype V] (J : SimpleGraph V)
    (w : V → ℕ) (c : I → ℕ) (d : ℕ)
    (atom : ∀ i (s : Finset V), 2 ≤ s.card → (∑ x ∈ s, w x) ≠ c i) :
    Function.Surjective (@present_block V I _ J w c d) := by
  classical
  intro f
  let s := weightFiber f.val none
  have out (x : Exterior s) : (f.val x.val).isSome := by
    cases hx : f.val x.val with
    | none => exact (x.property ((mem_weightFiber ..).mpr hx)).elim
    | some i => rfl
  let g (x : Exterior s) := (f.val x.val).get (out x)
  have ge (x : Exterior s) : some (g x) = f.val x.val := Option.some_get _
  have bij : Function.Bijective g := by
    constructor
    · intro x y eq
      obtain ⟨u,_,unique⟩ := atomic_fiber atom f (g x)
      exact Subtype.ext ((unique _ (ge x).symm).trans (unique _ ((ge y).symm.trans (congrArg some eq.symm))).symm)
    · intro i
      obtain ⟨v,hv,_⟩ := atomic_fiber atom f i
      have vo : v ∉ s := by simp [s,hv]
      exact ⟨⟨v,vo⟩,Option.some.inj ((ge ⟨v,vo⟩).trans hv)⟩
  let ei := Equiv.ofBijective g bij
  have wt (x : Exterior s) : c (g x) = w x.val := by
    obtain ⟨u,_,uniq⟩ := atomic_fiber atom f (g x)
    have fib : weightFiber f.val (some (g x)) = {x.val} := by
      ext y
      rw [mem_weightFiber,mem_singleton]
      exact ⟨fun h => (uniq y h).trans (uniq x.val (ge x).symm).symm,fun h => h ▸ (ge x).symm⟩
    have hh := (f.property (some (g x))).1
    rw [fib,sum_singleton] at hh
    exact hh.symm
  let e : Labelings w c s := ⟨ei,wt⟩
  refine ⟨⟨⟨s,(f.property none).2,(f.property none).1,⟨e⟩⟩,e⟩,?_⟩
  apply Subtype.ext
  funext v
  change encode e v = f.val v
  by_cases h : v ∈ s
  · simpa only [encode,dite_eq_left h] using ((mem_weightFiber f.val none v).mp h).symm
  · simp only [encode,dite_eq_right h]
    exact ge ⟨v,h⟩

theorem atomic_partition_count {V I : Type*} [Fintype V] (J : SimpleGraph V)
    (w : V → ℕ) (c : I → ℕ) (d : ℕ)
    (atom : ∀ i (s : Finset V), 2 ≤ s.card → (∑ x ∈ s, w x) ≠ c i) :
    Nat.card (WeightedBlocks J w (fun o : Option I => o.elim d c)) =
      Nat.card (Eligible J w c d) * Nat.card (ColorIso c c) := by
  let e := Equiv.ofBijective _ ⟨present_injective J w c d,present_surjective J w c d atom⟩
  rw [← Nat.card_congr e, ← Nat.card_prod]
  apply Nat.card_congr
  exact (Equiv.sigmaCongrRight (fun s : Eligible J w c d => recolorEquiv s.property.2.2.some)).trans
    (Equiv.sigmaEquivProd _ _)

end
end StanleyContinuation
