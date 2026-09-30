import Research.Backfill.Paper8.Proof.Tree.Build

/-!
# Paper 8, Theorem 1: transfer of good switchings, relabelling, `K_1` and `K_2`

Goodness (`IsGood`) transfers along a bijection `e` of the index sets with `A u v = B (e u) (e v)`
(eigenvectors and dot products are carried by `x ↦ x ∘ e`), in particular along graph
isomorphisms. Relabelling the branches of `T(a)` by a bijection `π` gives an isomorphic tree
(`permIso`). On one vertex the all-ones switching is good for every matrix (`K_1`); a tree on two
vertices is isomorphic to `⊤ : SimpleGraph (Fin 2)` (`K_2`).
-/

set_option autoImplicit false

open BackfillPaper8.Challenge SimpleGraph Matrix

namespace P8Tree

section Transfer

variable {V W : Type} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]

omit [DecidableEq V] [DecidableEq W] in
theorem mulVec_comp_equiv (A : Matrix V V ℝ) (B : Matrix W W ℝ) (e : V ≃ W)
    (hA : ∀ u v, A u v = B (e u) (e v)) (y : W → ℝ) : A *ᵥ (y ∘ e) = (B *ᵥ y) ∘ e := by
  funext u
  simp only [Matrix.mulVec, dotProduct, Function.comp_apply, hA]
  exact Equiv.sum_comp e (fun w => B (e u) w * y w)

/-- Goodness transfers along a bijection of the index sets carrying `A` to `B`. -/
theorem isGood_of_equiv (A : Matrix V V ℝ) (B : Matrix W W ℝ) (e : V ≃ W)
    (hA : ∀ u v, A u v = B (e u) (e v)) {s : W → ℝ} (hs : IsGood B s) : IsGood A (s ∘ e) := by
  rw [P8Basic.isGood_iff] at hs ⊢
  intro θ hθ
  rw [P8Basic.isEigenvalue_iff] at hθ
  obtain ⟨x, hx0, hx⟩ := hθ
  have hθ' : IsEigenvalue B θ := by
    rw [P8Basic.isEigenvalue_iff]
    refine ⟨x ∘ e.symm, ?_, ?_⟩
    · intro h
      apply hx0
      funext v
      have := congrFun h (e v)
      simpa using this
    · have h1 := mulVec_comp_equiv A B e hA (x ∘ e.symm)
      have h2 : (x ∘ e.symm) ∘ e = x := by
        funext v
        simp
      rw [h2, hx] at h1
      funext w
      have h3 := congrFun h1 (e.symm w)
      simp only [Function.comp_apply, Equiv.apply_symm_apply, Pi.smul_apply, smul_eq_mul] at h3
      simp only [Pi.smul_apply, smul_eq_mul, Function.comp_apply]
      exact h3.symm
  obtain ⟨y, hy, hys⟩ := hs θ hθ'
  refine ⟨y ∘ e, ?_, ?_⟩
  · rw [mulVec_comp_equiv A B e hA y, hy]
    funext v
    simp
  · have h4 : (y ∘ e) ⬝ᵥ (s ∘ e) = y ⬝ᵥ s := by
      simp only [dotProduct, Function.comp_apply]
      exact Equiv.sum_comp e (fun w => y w * s w)
    rw [h4]
    exact hys

/-- Goodness transfers along graph isomorphisms. -/
theorem isGood_of_iso {G : SimpleGraph V} {H : SimpleGraph W} [DecidableRel G.Adj]
    [DecidableRel H.Adj] (φ : G ≃g H) {s : W → ℝ} (hs : IsGood (H.adjMatrix ℝ) s) :
    IsGood (G.adjMatrix ℝ) (s ∘ φ) :=
  isGood_of_equiv (G.adjMatrix ℝ) (H.adjMatrix ℝ) φ.toEquiv
    (fun u v => by simp [adjMatrix_apply, φ.map_adj_iff]) hs

omit [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W] in
theorem isSwitching_comp {e : V → W} {s : W → ℝ} (hs : IsSwitching s) : IsSwitching (s ∘ e) :=
  fun v => hs (e v)

end Transfer

section Perm

variable {k k' : ℕ} {a : Fin k → ℕ} {a' : Fin k' → ℕ}

/-- Relabelling the branches: `TV a ≃ TV a'` when `a i = a' (π i)`. -/
def permEquiv (π : Fin k ≃ Fin k') (h : ∀ i, a i = a' (π i)) : TV a ≃ TV a' :=
  Equiv.optionCongr (Equiv.sigmaCongr π fun i => Equiv.optionCongr (finCongr (h i)))

theorem permEquiv_none (π : Fin k ≃ Fin k') (h : ∀ i, a i = a' (π i)) :
    permEquiv π h none = none := rfl

theorem permEquiv_v (π : Fin k ≃ Fin k') (h : ∀ i, a i = a' (π i)) (i : Fin k) :
    permEquiv π h (some ⟨i, none⟩) = some ⟨π i, none⟩ := rfl

theorem permEquiv_l (π : Fin k ≃ Fin k') (h : ∀ i, a i = a' (π i)) (i : Fin k) (j : Fin (a i)) :
    permEquiv π h (some ⟨i, some j⟩) = some ⟨π i, some (finCongr (h i) j)⟩ := rfl

/-- `T(a) ≃g T(a')` when `a i = a' (π i)` for a bijection `π` of the branches. -/
def permIso (π : Fin k ≃ Fin k') (h : ∀ i, a i = a' (π i)) : treeT a ≃g treeT a' where
  toEquiv := permEquiv π h
  map_rel_iff' := by
    intro x y
    rcases x with _ | ⟨i, _ | j⟩ <;> rcases y with _ | ⟨i', _ | j'⟩ <;>
      simp only [permEquiv_none, permEquiv_v, permEquiv_l, P8Basic.adj_c_c, P8Basic.adj_c_v,
        P8Basic.adj_c_l, P8Basic.adj_v_c, P8Basic.adj_v_v, P8Basic.adj_v_l, P8Basic.adj_l_c,
        P8Basic.adj_l_v, P8Basic.adj_l_l, π.apply_eq_iff_eq]

end Perm

section Small

/-- `K_1`: on one vertex the switching `1` is good for every matrix. -/
theorem isGood_one_of_card_one {V : Type} [Fintype V] [DecidableEq V] (A : Matrix V V ℝ)
    (h1 : Fintype.card V = 1) : IsGood A (fun _ => 1) := by
  rw [P8Basic.isGood_iff]
  intro θ hθ
  rw [P8Basic.isEigenvalue_iff] at hθ
  obtain ⟨x, hx0, hx⟩ := hθ
  refine ⟨x, hx, ?_⟩
  obtain ⟨u, hu⟩ := Fintype.card_eq_one_iff.1 h1
  have hsum : x ⬝ᵥ (fun _ => (1 : ℝ)) = x u := by
    simp only [dotProduct, mul_one]
    rw [Finset.sum_eq_single u]
    · intro v _ hv
      exact absurd (hu v) hv
    · simp
  rw [hsum]
  intro h
  apply hx0
  funext v
  rw [hu v]
  exact h

/-- `K_2`: a tree on two vertices is isomorphic to the complete graph on `Fin 2`. -/
theorem iso_top_of_card_two {V : Type} [Fintype V] (T : SimpleGraph V) (hT : T.IsTree)
    (h2 : Fintype.card V = 2) : Nonempty (T ≃g (⊤ : SimpleGraph (Fin 2))) := by
  let e : V ≃ Fin 2 := Fintype.equivFinOfCardEq h2
  have hadj : ∀ u v, T.Adj u v ↔ u ≠ v := by
    intro u v
    refine ⟨T.ne_of_adj, fun huv => ?_⟩
    obtain ⟨p⟩ := hT.connected u v
    cases p with
    | nil => exact absurd rfl huv
    | @cons _ w _ h q =>
      by_contra hn
      have hw : w ≠ v := fun hwv => hn (hwv ▸ h)
      have hwu : w ≠ u := (T.ne_of_adj h).symm
      have h1 : (e u).val ≠ (e v).val := fun hh => huv (e.injective (Fin.ext hh))
      have h2 : (e w).val ≠ (e v).val := fun hh => hw (e.injective (Fin.ext hh))
      have h3 : (e w).val ≠ (e u).val := fun hh => hwu (e.injective (Fin.ext hh))
      have := (e u).isLt
      have := (e v).isLt
      have := (e w).isLt
      omega
  exact ⟨{ toEquiv := e, map_rel_iff' := fun {u v} => by rw [top_adj, hadj, e.injective.ne_iff] }⟩

end Small

end P8Tree
