import Research.WordRepTensor.Proof.WRWords
import Research.WordRepTensor.Proof.WRGraphs

/-!
# Heredity of word-representability, and the graph of a homomorphism

Proofs of the frozen statements `WordRepresentableOfEmbedding` and `EmbeddingOfHom`
(written by Claude, 2026-09-28).
-/

set_option autoImplicit false

namespace ClaudeWordRep

open WordRepTensor.Challenge SimpleGraph

section Lists

variable {α β : Type} [DecidableEq α] [DecidableEq β]

omit [DecidableEq α] [DecidableEq β] in
theorem filterMap_eq_map_filter (h : α → Option β) (p : α → Bool) (ψ : α → β)
    (hh : ∀ z, h z = if p z then some (ψ z) else none) :
    ∀ w : List α, w.filterMap h = (w.filter p).map ψ := by
  intro w
  induction w with
  | nil => rfl
  | cons a t ih =>
    rw [List.filterMap_cons, hh a, List.filter_cons]
    by_cases hp : p a <;> simp [hp, ih]

theorem noRepeat_map (ψ : α → β) :
    ∀ L : List α, (∀ a ∈ L, ∀ b ∈ L, ψ a = ψ b → a = b) →
      noRepeat (L.map ψ) = noRepeat L := by
  intro L
  induction L with
  | nil => intro _; rfl
  | cons a t ih =>
    intro hinj
    have ht : ∀ x ∈ t, ∀ y ∈ t, ψ x = ψ y → x = y := fun x hx y hy =>
      hinj x (List.mem_cons_of_mem a hx) y (List.mem_cons_of_mem a hy)
    rw [List.map_cons]
    apply Bool.eq_iff_iff.mpr
    rw [noRepeat_cons, noRepeat_cons, ih ht]
    apply and_congr Iff.rfl
    constructor
    · intro h b hb hab
      subst hab
      apply h (ψ a)
      · cases t with
        | nil => simp at hb
        | cons c t => simp at hb; simp [hb]
      · rfl
    · intro h b hb hab
      cases t with
      | nil => simp at hb
      | cons c t =>
        simp only [List.map_cons, List.head?_cons, Option.some.injEq] at hb
        apply h c (by simp) (hinj a (by simp) c (by simp) (hb ▸ hab))

end Lists

open Classical in
/-- Heredity: a graph that embeds as an induced subgraph into a word-representable graph is
word-representable. -/
theorem wordRepresentableOfEmbedding : WordRepresentableOfEmbedding := by
  intro V W _ _ G H ⟨f⟩ ⟨w, hw⟩
  let g : W → Option V := fun z => if h : ∃ x, f x = z then some (Classical.choose h) else none
  have hg : ∀ v, g (f v) = some v := by
    intro v
    simp only [g]
    split
    · rename_i h'
      exact congrArg some (f.injective (Classical.choose_spec h'))
    · rename_i h'
      exact absurd ⟨v, rfl⟩ h'
  have hgnone : ∀ z, (¬ ∃ x, f x = z) → g z = none := fun z hz => by simp [g, hz]
  refine ⟨w.filterMap g, ?_, ?_⟩
  · intro v
    exact List.mem_filterMap.mpr ⟨f v, hw.1 (f v), hg v⟩
  · intro x y hxy
    have hfxy : f x ≠ f y := fun h => hxy (f.injective h)
    rw [← f.map_rel_iff, hw.2 (f x) (f y) hfxy]
    unfold Alternate
    rw [List.filter_filterMap]
    let ψ : W → V := fun z => if z = f x then x else y
    have hh : ∀ z, (g z).filter (fun v => v == x || v == y) =
        if (z == f x || z == f y) then some (ψ z) else none := by
      intro z
      by_cases hz : ∃ v, f v = z
      · obtain ⟨v, rfl⟩ := hz
        rw [hg v]
        by_cases hvx : v = x
        · subst hvx; simp [ψ]
        · by_cases hvy : v = y
          · subst hvy
            simp [ψ, Ne.symm hfxy]
          · have h1 : f v ≠ f x := fun h => hvx (f.injective h)
            have h2 : f v ≠ f y := fun h => hvy (f.injective h)
            simp [hvx, hvy, h1, h2]
      · rw [hgnone z hz]
        have h1 : z ≠ f x := fun h => hz ⟨x, h.symm⟩
        have h2 : z ≠ f y := fun h => hz ⟨y, h.symm⟩
        simp [h1, h2]
    rw [filterMap_eq_map_filter _ _ ψ hh w, noRepeat_map ψ]
    intro a ha b hb hab
    simp only [List.mem_filter, Bool.or_eq_true, beq_iff_eq] at ha hb
    rcases ha.2 with rfl | rfl <;> rcases hb.2 with rfl | rfl
    · rfl
    · simp [ψ, Ne.symm hfxy] at hab
      exact absurd hab hxy
    · simp [ψ, Ne.symm hfxy] at hab
      exact absurd hab.symm hxy
    · rfl

/-- The graph of a homomorphism `G →g H` is an induced copy of `G` in `G × H`. -/
theorem embeddingOfHom : EmbeddingOfHom := by
  intro V W G H ⟨f⟩
  refine ⟨⟨⟨fun x => (x, f x), fun a b h => congrArg Prod.fst h⟩, ?_⟩⟩
  intro a b
  simp only [tensorProd_adj]
  exact ⟨fun h => h.1, fun h => ⟨h, f.map_rel h⟩⟩

#print axioms wordRepresentableOfEmbedding
#print axioms embeddingOfHom

end ClaudeWordRep
