import Research.TaskH.Gao.FamilyOperations
import Research.TaskH.Fan.AdjEqConnectivity

/-! Actual deletion of two degree-two twin roots; every augmented-child deletion is mapped. -/
set_option autoImplicit false
universe u
namespace TaskH.Gao
open SimpleGraph TaskH.Fan
variable {V : Type u}

def case3TwinCarrier (x y : V) : Set V := {v | v ≠ x ∧ v ≠ y}

noncomputable def case3TwinMap (x y : V) (t : case3TwinCarrier x y) : V → case3TwinCarrier x y := by
  classical
  exact fun v => if hv : v ∈ case3TwinCarrier x y then ⟨v, hv⟩ else t

theorem case3TwinMap_mem (x y : V) (t : case3TwinCarrier x y) (v : V)
    (hv : v ∈ case3TwinCarrier x y) : case3TwinMap x y t v = ⟨v, hv⟩ := by
  classical
  unfold case3TwinMap
  exact dite_eq_left hv

theorem case3TwinMap_not_mem (x y : V) (t : case3TwinCarrier x y) (v : V)
    (hv : v ∉ case3TwinCarrier x y) : case3TwinMap x y t v = t := by
  classical
  unfold case3TwinMap
  exact dite_eq_right hv

theorem case3TwinMap_surjective (x y : V) (t : case3TwinCarrier x y) :
    Function.Surjective (case3TwinMap x y t) := by
  intro a
  exact ⟨a.1, (case3TwinMap_mem x y t a.1 a.2).trans (Subtype.ext rfl)⟩

theorem case3_twin_outer_neighbor_pair (G : SimpleGraph V) (x y p q a b : V)
    (hnx : G.neighborSet x = ({p, q} : Set V))
    (hny : G.neighborSet y = ({p, q} : Set V))
    (hb : b ∉ case3TwinCarrier x y) (e : G.Adj b a) : a = p ∨ a = q := by
  classical
  by_cases hbx : b = x
  · have e' : G.Adj x a := Eq.mp (congrArg (fun z : V => G.Adj z a) hbx) e
    exact Eq.mp (congrArg (fun S : Set V => a ∈ S) hnx) e'
  · have hby : b = y := by
      by_contra hby
      exact hb ⟨hbx, hby⟩
    have e' : G.Adj y a := Eq.mp (congrArg (fun z : V => G.Adj z a) hby) e
    exact Eq.mp (congrArg (fun S : Set V => a ∈ S) hny) e'

theorem case3_twin_pair_adj_or_eq (G : SimpleGraph V) (x y p q : V)
    (hp : p ∈ case3TwinCarrier x y) (hq : q ∈ case3TwinCarrier x y)
    (a t : case3TwinCarrier x y) (ha : a.1 = p ∨ a.1 = q) (ht : t.1 = p ∨ t.1 = q) :
    a = t ∨ ((G.induce (case3TwinCarrier x y)) ⊔
      SimpleGraph.edge (⟨p, hp⟩ : case3TwinCarrier x y) ⟨q, hq⟩).Adj a t := by
  classical
  by_cases he : a = t
  · exact Or.inl he
  · right
    right
    apply (SimpleGraph.edge_adj (⟨p, hp⟩ : case3TwinCarrier x y) ⟨q, hq⟩ a t).mpr
    refine ⟨?_, he⟩
    rcases ha with hap | haq
    · rcases ht with htp | htq
      · exact False.elim (he (Subtype.ext (hap.trans htp.symm)))
      · exact Or.inl ⟨Subtype.ext hap, Subtype.ext htq⟩
    · rcases ht with htp | htq
      · exact Or.inr ⟨Subtype.ext haq, Subtype.ext htp⟩
      · exact False.elim (he (Subtype.ext (haq.trans htq.symm)))

theorem case3TwinMap_adj_or_eq (G : SimpleGraph V) (x y p q : V)
    (hp : p ∈ case3TwinCarrier x y) (hq : q ∈ case3TwinCarrier x y)
    (hnx : G.neighborSet x = ({p, q} : Set V))
    (hny : G.neighborSet y = ({p, q} : Set V))
    (t : case3TwinCarrier x y) (ht : t.1 = p ∨ t.1 = q)
    {a b : V} (e : G.Adj a b) :
    case3TwinMap x y t a = case3TwinMap x y t b ∨
      ((G.induce (case3TwinCarrier x y)) ⊔
        SimpleGraph.edge (⟨p, hp⟩ : case3TwinCarrier x y) ⟨q, hq⟩).Adj
          (case3TwinMap x y t a) (case3TwinMap x y t b) := by
  classical
  by_cases ha : a ∈ case3TwinCarrier x y
  · by_cases hb : b ∈ case3TwinCarrier x y
    · rw [case3TwinMap_mem x y t a ha, case3TwinMap_mem x y t b hb]
      exact Or.inr (Or.inl e)
    · rw [case3TwinMap_mem x y t a ha, case3TwinMap_not_mem x y t b hb]
      exact case3_twin_pair_adj_or_eq G x y p q hp hq ⟨a, ha⟩ t
        (case3_twin_outer_neighbor_pair G x y p q a b hnx hny hb e.symm) ht
  · by_cases hb : b ∈ case3TwinCarrier x y
    · rw [case3TwinMap_not_mem x y t a ha, case3TwinMap_mem x y t b hb]
      rcases case3_twin_pair_adj_or_eq G x y p q hp hq ⟨b, hb⟩ t
        (case3_twin_outer_neighbor_pair G x y p q b a hnx hny ha e) ht with he | he
      · exact Or.inl he.symm
      · exact Or.inr he.symm
    · left
      rw [case3TwinMap_not_mem x y t a ha, case3TwinMap_not_mem x y t b hb]

theorem case3TwinMap_ne (x y : V) (t z : case3TwinCarrier x y)
    (htz : t ≠ z) (a : V) (haz : a ≠ z.1) : case3TwinMap x y t a ≠ z := by
  classical
  by_cases ha : a ∈ case3TwinCarrier x y
  · rw [case3TwinMap_mem x y t a ha]
    intro he
    exact haz (congrArg Subtype.val he)
  · rw [case3TwinMap_not_mem x y t a ha]
    exact htz

theorem case3_twin_delete_connected (G : SimpleGraph V) (x y p q : V)
    (hp : p ∈ case3TwinCarrier x y) (hq : q ∈ case3TwinCarrier x y)
    (hnx : G.neighborSet x = ({p, q} : Set V))
    (hny : G.neighborSet y = ({p, q} : Set V))
    (t z : case3TwinCarrier x y) (ht : t.1 = p ∨ t.1 = q) (htz : t ≠ z)
    (hG : (G.induce {a : V | a ≠ z.1}).Connected) :
    (((G.induce (case3TwinCarrier x y)) ⊔
      SimpleGraph.edge (⟨p, hp⟩ : case3TwinCarrier x y) ⟨q, hq⟩).induce
        {a : case3TwinCarrier x y | a ≠ z}).Connected := by
  let f : {a : V // a ≠ z.1} → {a : case3TwinCarrier x y // a ≠ z} := fun a =>
    ⟨case3TwinMap x y t a.1, case3TwinMap_ne x y t z htz a.1 a.2⟩
  have hs : Function.Surjective f := by
    intro a
    have haz : a.1.1 ≠ z.1 := fun he => a.2 (Subtype.ext he)
    refine ⟨⟨a.1.1, haz⟩, ?_⟩
    apply Subtype.ext
    exact (case3TwinMap_mem x y t a.1.1 a.1.2).trans (Subtype.ext rfl)
  have hf : ∀ {a b : {a : V // a ≠ z.1}},
      (G.induce {a : V | a ≠ z.1}).Adj a b → f a = f b ∨
      (((G.induce (case3TwinCarrier x y)) ⊔
        SimpleGraph.edge (⟨p, hp⟩ : case3TwinCarrier x y) ⟨q, hq⟩).induce
          {a : case3TwinCarrier x y | a ≠ z}).Adj (f a) (f b) := by
    intro a b e
    rcases case3TwinMap_adj_or_eq G x y p q hp hq hnx hny t ht e with he | he
    · exact Or.inl (Subtype.ext he)
    · exact Or.inr he
  exact connected_of_surjective_adj_or_eq f hs hf hG

theorem case3_twin_deleted_graph_rooted [Fintype V] (G : SimpleGraph V) (x y p q : V)
    [Fintype (case3TwinCarrier x y)]
    (hp : p ∈ case3TwinCarrier x y) (hq : q ∈ case3TwinCarrier x y) (hpq : p ≠ q)
    (hnx : G.neighborSet x = ({p, q} : Set V))
    (hny : G.neighborSet y = ({p, q} : Set V))
    (hG : TwoConnected G) (hcard : 3 ≤ Fintype.card (case3TwinCarrier x y)) :
    RootedTwoConnected (G.induce (case3TwinCarrier x y)) ⟨p, hp⟩ ⟨q, hq⟩ := by
  classical
  let pr : case3TwinCarrier x y := ⟨p, hp⟩
  let qr : case3TwinCarrier x y := ⟨q, hq⟩
  let J := (G.induce (case3TwinCarrier x y)) ⊔ SimpleGraph.edge pr qr
  have hprq : pr ≠ qr := fun he => hpq (congrArg Subtype.val he)
  have hc : J.Connected := connected_of_surjective_adj_or_eq (case3TwinMap x y pr)
    (case3TwinMap_surjective x y pr)
    (case3TwinMap_adj_or_eq G x y p q hp hq hnx hny pr (Or.inl rfl)) hG.2.1
  refine ⟨hprq, hcard, hc, ?_⟩
  intro z
  by_cases hzp : z = pr
  · have hqz : qr ≠ z := fun he => hprq (hzp.symm.trans he.symm)
    exact case3_twin_delete_connected G x y p q hp hq hnx hny qr z (Or.inr rfl) hqz (hG.2.2 z.1)
  · exact case3_twin_delete_connected G x y p q hp hq hnx hny pr z (Or.inl rfl)
      (Ne.symm hzp) (hG.2.2 z.1)

#print axioms case3TwinCarrier
#print axioms case3TwinMap
#print axioms case3TwinMap_mem
#print axioms case3TwinMap_not_mem
#print axioms case3TwinMap_surjective
#print axioms case3_twin_outer_neighbor_pair
#print axioms case3_twin_pair_adj_or_eq
#print axioms case3TwinMap_adj_or_eq
#print axioms case3TwinMap_ne
#print axioms case3_twin_delete_connected
#print axioms case3_twin_deleted_graph_rooted
end TaskH.Gao
