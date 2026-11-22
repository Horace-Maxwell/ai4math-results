import Research.TaskP.RootRadius.RootData

open Polynomial
namespace TaskP.GraphRootRadius.Proof
open Challenge

variable {V I : Type*} [Fintype I] [Fintype V]

noncomputable def bundle (F : I → Finset V) : Finset (I × V) :=
  (Finset.univ.sigma F).map (Equiv.sigmaEquivProd I V).toEmbedding

omit [Fintype V] in
@[simp] theorem mem_bundle (F : I → Finset V) (i : I) (v : V) :
    (i,v) ∈ bundle F ↔ v ∈ F i := by
  classical
  simp only [bundle, Finset.mem_map, Finset.mem_sigma, Finset.mem_univ, true_and,
    Equiv.toEmbedding_apply, Equiv.sigmaEquivProd_apply]
  constructor
  · rintro ⟨⟨j,w⟩, hw, e⟩
    cases e
    exact hw
  · exact fun h => ⟨⟨i,v⟩,h,rfl⟩

omit [Fintype V] in
theorem card_bundle (F : I → Finset V) : (bundle F).card = ∑ i, (F i).card := by
  simp [bundle]

noncomputable def familyEquiv : (I → Finset V) ≃ Finset (I × V) := by
  classical
  exact {
    toFun := bundle
    invFun := fun T i => Finset.univ.filter fun v => (i,v) ∈ T
    left_inv := by intro F; funext i; ext v; simp
    right_inv := by intro T; ext ⟨i,v⟩; simp
  }

omit [Fintype I] [Fintype V] in
theorem dominates_nonempty [Nonempty V] (B : SimpleGraph V) {S : Finset V}
    (h : Dominates B S) : S.Nonempty := by
  simpa only [Finset.nonempty_iff_ne_empty] using
    (fun e : S = ∅ => not_dominates_empty B (e ▸ h))

omit [Fintype V] in
theorem dominates_join_iff {a m : ℕ} [Nonempty V] (hm : 0 < m) (B : SimpleGraph V)
    (S : Finset (Fin a)) (F : Fin m → Finset V) :
    Dominates (petalJoin a m B) (S.disjSum (bundle F)) ↔
      S.Nonempty ∨ ∀ i, Dominates B (F i) := by
  classical
  constructor
  · intro h
    by_cases hS : S.Nonempty
    · exact Or.inl hS
    · right
      have h0 := Finset.not_nonempty_iff_eq_empty.mp hS
      subst S
      intro i v
      rcases h (.inr (i,v)) with hv | ⟨w, hw, he⟩
      · left
        simpa using hv
      · rcases w with j | ⟨j,u⟩
        · simp at hw
        · change i = j ∧ B.Adj v u at he
          rcases he with ⟨rfl, hu⟩
          exact Or.inr ⟨u, by simpa using hw, hu⟩
  · rintro (⟨c,hc⟩ | h)
    · rintro (i | ⟨i,v⟩)
      · by_cases he : i = c
        · exact Or.inl (by simpa [he] using hc)
        · exact Or.inr ⟨.inl c, by simpa using hc, he⟩
      · exact Or.inr ⟨.inl c, by simpa using hc, trivial⟩
    · rintro (i | ⟨i,v⟩)
      · let j : Fin m := ⟨0,hm⟩
        obtain ⟨u,hu⟩ := dominates_nonempty B (h j)
        exact Or.inr ⟨.inr (j,u), by simp [hu], trivial⟩
      · rcases h i v with hv | ⟨u,hu,he⟩
        · exact Or.inl (by simp [hv])
        · exact Or.inr ⟨.inr (i,u), by simp [hu], rfl, he⟩

end TaskP.GraphRootRadius.Proof
