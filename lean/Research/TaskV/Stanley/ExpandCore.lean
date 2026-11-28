import Research.TaskV.Stanley.StarBasics

namespace StanleyContinuation
open SimpleGraph Finset
noncomputable section

private theorem pointed_equiv {α β : Type*} [Finite α] [Finite β] (a : α) (b : β)
    (h : Nat.card α = Nat.card β) : ∃ e : α ≃ β, e a = b := by
  classical
  obtain ⟨e⟩ := Finite.card_eq.mp h
  exact ⟨e.trans (Equiv.swap (e a) b), Equiv.swap_apply_left ..⟩

private theorem adjacency_by_centers {n : ℕ} {G : SimpleGraph (Fin n)}
    (h : G.Connected) (hc : (core G).Nonempty) (x y : Fin n) :
    let g := starCenter h hc
    G.Adj x y ↔
      (x ≠ y ∧ (x = (g y : Fin n) ∨ y = (g x : Fin n))) ∨
      (x = (g x : Fin n) ∧ y = (g y : Fin n) ∧ G.Adj (g x) (g y)) := by
  classical
  dsimp only
  constructor
  · intro he
    by_cases hx : x ∈ core G
    · by_cases hy : y ∈ core G
      · have ex := starCenter_core h hc ⟨x,hx⟩
        have ey := starCenter_core h hc ⟨y,hy⟩
        right
        simpa only [ex,ey,true_and] using he
      · exact Or.inl ⟨he.ne, Or.inl (starCenter_leaf_eq h hc hy he.symm).symm⟩
    · exact Or.inl ⟨he.ne, Or.inr (starCenter_leaf_eq h hc hx he).symm⟩
  · rintro (⟨hne, he | he⟩ | ⟨hx,hy,he⟩)
    · have hy : y ∉ core G := by
        intro hy
        exact hne (he.trans (congrArg Subtype.val (starCenter_core h hc ⟨y,hy⟩)))
      exact he ▸ (starCenter_leaf h hc hy).symm
    · have hx : x ∉ core G := by
        intro hx
        exact hne (he.trans (congrArg Subtype.val (starCenter_core h hc ⟨x,hx⟩))).symm
      exact he ▸ starCenter_leaf h hc hx
    · exact hx.symm ▸ hy.symm ▸ he

/-- A weight-preserving graph isomorphism of nonleaf cores extends over the ordinary leaves. -/
theorem expand_weighted_core_iso {n m : ℕ} {G : SimpleGraph (Fin n)} {H : SimpleGraph (Fin m)}
    (hG : G.Connected) (hH : H.Connected) (cg : (core G).Nonempty) (ch : (core H).Nonempty)
    (e : (G.induce (core G : Set (Fin n))) ≃g (H.induce (core H : Set (Fin m))))
    (weight : ∀ a : ↥(core G), coreWeight G a = coreWeight H (e a)) :
    Nonempty (G ≃g H) := by
  classical
  let g := starCenter hG cg
  let h := starCenter hH ch
  let fiberG (a : ↥(core G)) := {x : Fin n // g x = a}
  let fiberH (b : ↥(core H)) := {y : Fin m // h y = b}
  let baseG (a : ↥(core G)) : fiberG a := ⟨a,starCenter_core hG cg a⟩
  let baseH (b : ↥(core H)) : fiberH b := ⟨b,starCenter_core hH ch b⟩
  have paired (a : ↥(core G)) : ∃ i : fiberG a ≃ fiberH (e a), i (baseG a) = baseH (e a) :=
    pointed_equiv _ _ ((starCenter_fiber_card hG cg a).trans
      ((weight a).trans (starCenter_fiber_card hH ch (e a)).symm))
  choose i hi using paired
  let f := (Equiv.sigmaFiberEquiv g).symm.trans
    ((Equiv.sigmaCongr e.toEquiv i).trans (Equiv.sigmaFiberEquiv h))
  have center (x : Fin n) : h (f x) = e (g x) := (i (g x) ⟨x,rfl⟩).property
  have maps (a : ↥(core G)) : f (a : Fin n) = (e a : Fin m) := by
    have aux (x : Fin n) (a : ↥(core G)) (hg : g x = a) : f x = (i a ⟨x,hg⟩).val := by
      subst a
      rfl
    rw [aux a a (starCenter_core hG cg a)]
    exact congrArg Subtype.val (hi a)
  have mapped (x : Fin n) : (h (f x) : Fin m) = f (g x) :=
    (congrArg Subtype.val (center x)).trans (maps (g x)).symm
  refine ⟨{ toEquiv := f, map_rel_iff' := ?_ }⟩
  intro x y
  refine (adjacency_by_centers hH ch (f x) (f y)).trans
    (Iff.trans ?_ (adjacency_by_centers hG cg x y).symm)
  change ((f x ≠ f y ∧ (f x = (h (f y) : Fin m) ∨ f y = (h (f x) : Fin m))) ∨
    (f x = (h (f x) : Fin m) ∧ f y = (h (f y) : Fin m) ∧ H.Adj (h (f x)) (h (f y)))) ↔ _
  have edge : H.Adj (h (f x)) (h (f y)) ↔ G.Adj (g x) (g y) := by
    rw [center,center]
    exact e.map_rel_iff
  rw [edge]
  simp only [mapped, ne_eq, f.apply_eq_iff_eq]
  exact Iff.rfl

end
end StanleyContinuation
