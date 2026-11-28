import Research.TaskV.Stanley.Histogram
import Mathlib.Combinatorics.SimpleGraph.Acyclic

namespace StanleyContinuation
open SimpleGraph
noncomputable section

private abbrev Reduced {V : Type*} (v : V) := ↥(({v} : Set V)ᶜ)

private def removeLeaf {V C : Type*} {G : SimpleGraph V} (v : V)
    (a : ProperAssignments G C) : ProperAssignments (G.induce {v}ᶜ) C :=
  ⟨fun w => a.val w.val, fun x y h => a.property x.val y.val h⟩

private def addLeaf {V C : Type*} [DecidableEq V] {G : SimpleGraph V} {v u : V}
    (hvu : G.Adj v u) (huniq : ∀ w, G.Adj v w → w = u)
    (g : ProperAssignments (G.induce {v}ᶜ) C) (c : C)
    (hc : c ≠ g.val ⟨u, hvu.ne.symm⟩) : ProperAssignments G C := by
  refine ⟨fun x => if hx : x = v then c else g.val ⟨x, hx⟩, ?_⟩
  intro x y hxy
  by_cases hx : x = v
  · subst x
    have hy : y = u := huniq y hxy
    subst y
    simpa [hvu.ne.symm] using hc
  by_cases hy : y = v
  · subst y
    have hxu : x = u := huniq x hxy.symm
    subst x
    simpa [hvu.ne.symm] using hc.symm
  exact (by simpa [hx, hy] using g.property ⟨x,hx⟩ ⟨y,hy⟩ hxy)

private def leafEquiv {V C : Type*} [DecidableEq V] {G : SimpleGraph V} {v u : V}
    (hvu : G.Adj v u) (huniq : ∀ w, G.Adj v w → w = u) :
    ProperAssignments G C ≃
      Σ g : ProperAssignments (G.induce {v}ᶜ) C, {c : C // c ≠ g.val ⟨u,hvu.ne.symm⟩} where
  toFun a := ⟨removeLeaf v a, ⟨a.val v,a.property v u hvu⟩⟩
  invFun z := addLeaf hvu huniq z.1 z.2.val z.2.property
  left_inv a := by
    apply Subtype.ext
    funext x
    by_cases hx : x = v <;> simp [addLeaf, removeLeaf, hx]
  right_inv := by
    rintro ⟨g,⟨c,hc⟩⟩
    have hr : removeLeaf v (addLeaf hvu huniq g c hc) = g := by
      apply Subtype.ext
      funext w
      have hw : w.val ≠ v := w.property
      simp [removeLeaf, addLeaf, hw]
    apply Sigma.ext hr
    apply (Subtype.heq_iff_coe_eq ?_).mpr
    · change (addLeaf hvu huniq g c hc).val v = c
      simp [addLeaf]
    · intro x
      change (x ≠ (addLeaf hvu huniq g c hc).val u) ↔ (x ≠ g.val ⟨u,hvu.ne.symm⟩)
      simp [addLeaf, hvu.ne.symm]

private theorem leaf_card {V : Type*} [Finite V] {G : SimpleGraph V} {v u : V}
    (hvu : G.Adj v u) (huniq : ∀ w, G.Adj v w → w = u) (q : ℕ) :
    Nat.card (ProperAssignments G (Fin q)) =
      Nat.card (ProperAssignments (G.induce {v}ᶜ) (Fin q)) * (q-1) := by
  classical
  let := Fintype.ofFinite (ProperAssignments (G.induce {v}ᶜ) (Fin q))
  rw [Nat.card_congr (leafEquiv (C := Fin q) hvu huniq), Nat.card_sigma]
  simp [Nat.card_eq_fintype_card, Fintype.card_subtype_compl]

private theorem tree_card_aux (q n : ℕ) : ∀ {V : Type*} [Fintype V] (G : SimpleGraph V),
    Fintype.card V = n → G.IsTree →
    Nat.card (ProperAssignments G (Fin q)) = q * (q-1)^(n-1) := by
  classical
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro V inst G hsize ht
    have : Nonempty V := ht.connected.nonempty
    cases subsingleton_or_nontrivial V with
    | inl hs =>
      let := hs
      have hn : n = 1 := hsize.symm.trans (by
        simpa only [Nat.card_eq_fintype_card] using (Nat.card_unique (α := V)))
      let e : ProperAssignments G (Fin q) ≃ (V → Fin q) := {
        toFun := Subtype.val
        invFun := fun f => ⟨f, fun x y h => (h.ne (Subsingleton.elim x y)).elim⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
      rw [Nat.card_congr e, Nat.card_fun, Nat.card_eq_fintype_card (α := V), hsize, hn]
      simp
    | inr hnt =>
      let := hnt
      obtain ⟨v,hv⟩ := ht.exists_vert_degree_one_of_nontrivial
      obtain ⟨u,hvu,hu⟩ := degree_eq_one_iff_existsUnique_adj.mp hv
      have hred : Fintype.card (Reduced v) = n-1 := by
        change Fintype.card {x : V // ¬x = v} = n-1
        rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq, hsize]
      have hn : 1 < n := hsize ▸ Fintype.one_lt_card
      have ht' : (G.induce {v}ᶜ).IsTree :=
        ⟨ht.connected.induce_compl_singleton_of_degree_eq_one hv, ht.isAcyclic.induce _⟩
      rw [leaf_card hvu hu q, ih (n-1) (by omega) _ hred ht', mul_assoc, ← pow_succ]
      congr 2
      omega

private def assemble {V C : Type*} {G : SimpleGraph V}
    (f : ∀ c : G.ConnectedComponent, ProperAssignments c.toSimpleGraph C) (v : V) : C :=
  (f (G.connectedComponentMk v)).val ⟨v,rfl⟩

private theorem assemble_eq {V C : Type*} {G : SimpleGraph V}
    (f : ∀ c : G.ConnectedComponent, ProperAssignments c.toSimpleGraph C)
    (c : G.ConnectedComponent) (x : c) : assemble f x.val = (f c).val x := by
  rcases x with ⟨v,hv⟩
  change G.connectedComponentMk v = c at hv
  subst c
  rfl

private def componentAssignmentEquiv {V C : Type*} (G : SimpleGraph V) :
    ProperAssignments G C ≃ (∀ c : G.ConnectedComponent, ProperAssignments c.toSimpleGraph C) where
  toFun f c := ⟨fun x => f.val x.val, fun x y h => f.property x.val y.val h⟩
  invFun f := ⟨assemble f, by
    intro x y hxy
    let c := G.connectedComponentMk x
    let vx : c := ⟨x,rfl⟩
    let vy : c := ⟨y,(ConnectedComponent.connectedComponentMk_eq_of_adj hxy).symm⟩
    change assemble f vx.val ≠ assemble f vy.val
    rw [assemble_eq f c vx, assemble_eq f c vy]
    exact (f c).property vx vy hxy⟩
  left_inv _ := rfl
  right_inv f := by
    funext c
    apply Subtype.ext
    funext x
    exact assemble_eq f c x

theorem forest_proper_card {V : Type*} [Finite V] (G : SimpleGraph V)
    (hG : G.IsAcyclic) (q : ℕ) (_hq : 2 ≤ q) :
    Nat.card (ProperAssignments G (Fin q)) =
      q ^ Nat.card G.ConnectedComponent * (q-1) ^ (Nat.card V - Nat.card G.ConnectedComponent) := by
  classical
  let := Fintype.ofFinite V
  let := Fintype.ofFinite G.ConnectedComponent
  let (c : G.ConnectedComponent) := Fintype.ofFinite c
  have hsum : ∑ c : G.ConnectedComponent, Fintype.card c = Fintype.card V := by
    let e : (Σ c : G.ConnectedComponent, ↥c) ≃ V := Equiv.sigmaFiberEquiv G.connectedComponentMk
    simpa only [Fintype.card_sigma] using Fintype.card_congr e
  have haux : (∑ c : G.ConnectedComponent, (Fintype.card c - 1)) +
      Fintype.card G.ConnectedComponent = Fintype.card V := by
    calc
      _ = ∑ c : G.ConnectedComponent, ((Fintype.card c - 1) + 1) := by
        simp [Finset.sum_add_distrib]
      _ = ∑ c : G.ConnectedComponent, Fintype.card c := by
        apply Finset.sum_congr rfl
        intro c _
        have : Nonempty c := c.connected_toSimpleGraph.nonempty
        have := Fintype.card_pos (α := c)
        omega
      _ = _ := hsum
  rw [Nat.card_congr (componentAssignmentEquiv (C := Fin q) G), Nat.card_pi]
  simp_rw [fun (c : G.ConnectedComponent) =>
    tree_card_aux q (Fintype.card c) c.toSimpleGraph rfl (hG.isTree_connectedComponent c)]
  rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  simp only [Finset.prod_const, Finset.card_univ, Nat.card_eq_fintype_card]
  congr 2
  omega

end
end StanleyContinuation
