import Research.TaskH.Fan.Identification

/-! One genuine fresh-root extension: every deletion is checked on actual vertices. -/
set_option autoImplicit false
universe u v
namespace TaskH.Gao
open SimpleGraph TaskH.Fan
variable {V : Type u} {W : Type v}

theorem connected_of_one_extra_vertex (H : SimpleGraph W) (J : SimpleGraph V)
    (z : V) (f : W → V) (hH : H.Connected)
    (hedge : ∀ u v, H.Adj u v → J.Adj (f u) (f v))
    (hcover : ∀ p : V, p = z ∨ ∃ u, f u = p)
    (w : W) (hzw : J.Adj z (f w)) : J.Connected := by
  let fh : H →g J := {
    toFun := f
    map_rel' := by
      intro a b e
      exact hedge a b e }
  have hto : ∀ p : V, J.Reachable z p := by
    intro p
    rcases hcover p with rfl | ⟨u, rfl⟩
    · exact Reachable.rfl
    · exact hzw.reachable.trans ((hH w u).map fh)
  refine { preconnected := ?_, nonempty := ⟨z⟩ }
  intro p q
  exact (hto p).symm.trans (hto q)

theorem one_root_extension_rooted [Fintype W] (H : SimpleGraph W)
    (J : SimpleGraph (Option W)) (b w : W) (hH : TwoConnected H)
    (hret : ∀ u v, J.Adj (some u) (some v) ↔ H.Adj u v)
    (hw : J.Adj none (some w)) (hwb : w ≠ b) :
    RootedTwoConnected J none (some b) := by
  let K : SimpleGraph (Option W) := J ⊔ SimpleGraph.edge none (some b)
  have hKret : ∀ u v, H.Adj u v → K.Adj (some u) (some v) := by
    intro u v e
    change J.Adj (some u) (some v) ∨ (SimpleGraph.edge none (some b)).Adj (some u) (some v)
    exact Or.inl ((hret u v).mpr e)
  have hne : (none : Option W) ≠ some b := by
    intro he
    cases he
  have htest : K.Adj none (some b) := by
    change J.Adj none (some b) ∨ (SimpleGraph.edge none (some b)).Adj none (some b)
    right
    apply (SimpleGraph.edge_adj none (some b) none (some b)).mpr
    exact ⟨Or.inl ⟨rfl, rfl⟩, hne⟩
  have hK : K.Connected := by
    refine connected_of_one_extra_vertex H K none Option.some hH.2.1 hKret ?_ b htest
    intro p
    cases p with
    | none => exact Or.inl rfl
    | some u => exact Or.inr ⟨u, rfl⟩
  have hcard : 3 ≤ Fintype.card (Option W) := by
    rw [Fintype.card_option]
    have hc := hH.1
    omega
  change (none : Option W) ≠ some b ∧ TwoConnected K
  refine ⟨hne, hcard, hK, ?_⟩
  intro z
  cases z with
  | none =>
    let f : H →g K.induce {p : Option W | p ≠ none} := {
      toFun := fun u => ⟨some u, by intro he; cases he⟩
      map_rel' := by
        intro u v e
        exact hKret u v e }
    have hs : Function.Surjective f := by
      rintro ⟨p, hp⟩
      cases p with
      | none => exact False.elim (hp rfl)
      | some u => exact ⟨u, Subtype.ext rfl⟩
    exact SimpleGraph.Connected.map f hs hH.2.1
  | some r =>
    let A : Set W := {u | u ≠ r}
    let D : SimpleGraph {p : Option W // p ≠ some r} := K.induce {p | p ≠ some r}
    let zn : {p : Option W // p ≠ some r} := ⟨none, by intro he; cases he⟩
    let f : A → {p : Option W // p ≠ some r} :=
      fun u => ⟨some u.1, fun he => u.2 (Option.some.inj he)⟩
    have hDedge : ∀ u v : A, (H.induce A).Adj u v → D.Adj (f u) (f v) := by
      intro u v e
      exact hKret u.1 v.1 e
    have hcover : ∀ p : {p : Option W // p ≠ some r}, p = zn ∨ ∃ u : A, f u = p := by
      rintro ⟨p, hp⟩
      cases p with
      | none => exact Or.inl (Subtype.ext rfl)
      | some u =>
        refine Or.inr ⟨⟨u, ?_⟩, Subtype.ext rfl⟩
        intro he
        exact hp (congrArg Option.some he)
    have hspoke : ∃ u : A, D.Adj zn (f u) := by
      by_cases hr : r = b
      · refine ⟨⟨w, fun he => hwb (he.trans hr)⟩, ?_⟩
        change K.Adj none (some w)
        change J.Adj none (some w) ∨ (SimpleGraph.edge none (some b)).Adj none (some w)
        exact Or.inl hw
      · exact ⟨⟨b, Ne.symm hr⟩, htest⟩
    obtain ⟨u, hu⟩ := hspoke
    exact connected_of_one_extra_vertex (H.induce A) D zn f (hH.2.2 r)
      hDedge hcover u hu

theorem identification_rooted_of_exterior_twoConnected (G : SimpleGraph V) (S : Set V)
    [Fintype {v : V // v ∉ S}] (b w : {v : V // v ∉ S})
    (hH : TwoConnected (V := {v : V // v ∉ S}) (G.induce {v : V | v ∉ S}))
    (hspoke : ∃ s ∈ S, G.Adj s w.1) (hwb : w ≠ b) :
    RootedTwoConnected (identificationGraph G S) none (some b) := by
  exact one_root_extension_rooted (W := {v : V // v ∉ S})
    (G.induce {v : V | v ∉ S})
    (identificationGraph G S) b w hH (fun _ _ => Iff.rfl) hspoke hwb

#print axioms connected_of_one_extra_vertex
#print axioms one_root_extension_rooted
#print axioms identification_rooted_of_exterior_twoConnected
end TaskH.Gao
