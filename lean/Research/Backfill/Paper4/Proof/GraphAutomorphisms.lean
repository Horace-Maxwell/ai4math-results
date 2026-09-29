import Research.Backfill.Paper4.Challenge

/-! Complete automorphism counts for the two frozen eight-vertex graphs.
Every automorphism is classified by degrees and adjacency; no permutation census is assumed.
Compilation and acceptance evidence is recorded separately. -/
set_option autoImplicit false

namespace CodexPaper4
open BackfillPaper4
namespace GraphAutomorphisms

local instance : DecidableRel Challenge.G1.Adj := fun i j =>
  inferInstanceAs (Decidable ((i.val, j.val) ∈ Challenge.g1Edges ∨
    (j.val, i.val) ∈ Challenge.g1Edges))
local instance : DecidableRel Challenge.G2.Adj := fun i j =>
  inferInstanceAs (Decidable ((i.val, j.val) ∈ Challenge.g2Edges ∨
    (j.val, i.val) ∈ Challenge.g2Edges))

def sigma1 : Challenge.G1 ≃g Challenge.G1 where
  toFun := ![0, 6, 4, 7, 2, 5, 1, 3]
  invFun := ![0, 6, 4, 7, 2, 5, 1, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel
  map_rel_iff' := by decide +kernel

def sigma2 : Challenge.G2 ≃g Challenge.G2 where
  toFun := ![0, 4, 3, 2, 1, 5, 6, 7]
  invFun := ![0, 4, 3, 2, 1, 5, 6, 7]
  left_inv := by decide +kernel
  right_inv := by decide +kernel
  map_rel_iff' := by decide +kernel

theorem sigma1_involutive : ∀ x : Fin 8, sigma1 (sigma1 x) = x := by decide +kernel
theorem sigma2_involutive : ∀ x : Fin 8, sigma2 (sigma2 x) = x := by decide +kernel

theorem image_ne_fixed {V : Type*} (f : V → V) (hf : Function.Injective f)
    {x y : V} (hxy : x ≠ y) (hy : f y = y) : f x ≠ y := by
  intro h
  exact hxy (hf (h.trans hy.symm))

theorem g1_degree0 : Challenge.G1.degree 0 = 4 := by decide +kernel
theorem g1_degree2 : Challenge.G1.degree 2 = 3 := by decide +kernel
theorem g1_degree4 : Challenge.G1.degree 4 = 3 := by decide +kernel
theorem g1_degree4_unique : ∀ x : Fin 8, Challenge.G1.degree x = 4 → x = 0 := by decide +kernel
theorem g1_degree3_choices : ∀ x : Fin 8, Challenge.G1.degree x = 3 → x = 2 ∨ x = 4 := by
  decide +kernel
theorem g1_det4 : ∀ x : Fin 8, Challenge.G1.degree x = 3 → x ≠ 2 → x = 4 := by decide +kernel
theorem g1_det5 : ∀ x : Fin 8,
    Challenge.G1.Adj 2 x → Challenge.G1.Adj 4 x → x ≠ 0 → x = 5 := by decide +kernel
theorem g1_det3 : ∀ x : Fin 8,
    Challenge.G1.Adj 2 x → x ≠ 0 → x ≠ 5 → x = 3 := by decide +kernel
theorem g1_det1 : ∀ x : Fin 8, Challenge.G1.Adj 3 x → x ≠ 2 → x = 1 := by decide +kernel
theorem g1_det7 : ∀ x : Fin 8,
    Challenge.G1.Adj 4 x → x ≠ 0 → x ≠ 5 → x = 7 := by decide +kernel
theorem g1_det6 : ∀ x : Fin 8, Challenge.G1.Adj 7 x → x ≠ 4 → x = 6 := by decide +kernel

theorem g1_fix0 (e : Challenge.G1 ≃g Challenge.G1) : e 0 = 0 :=
  g1_degree4_unique (e 0) ((e.degree_eq 0).trans g1_degree0)

theorem g1_fix2_identity (e : Challenge.G1 ≃g Challenge.G1) (h2 : e 2 = 2) :
    e = SimpleGraph.Iso.refl := by
  have h0 := g1_fix0 e
  have h4 : e 4 = 4 := g1_det4 (e 4) ((e.degree_eq 4).trans g1_degree4)
    (image_ne_fixed e e.injective (by decide : (4 : Fin 8) ≠ 2) h2)
  have h25 : Challenge.G1.Adj 2 (e 5) := by
    simpa only [h2] using e.map_adj_iff.mpr (by decide : Challenge.G1.Adj 2 5)
  have h45 : Challenge.G1.Adj 4 (e 5) := by
    simpa only [h4] using e.map_adj_iff.mpr (by decide : Challenge.G1.Adj 4 5)
  have h5 : e 5 = 5 := g1_det5 (e 5) h25 h45
    (image_ne_fixed e e.injective (by decide : (5 : Fin 8) ≠ 0) h0)
  have h23 : Challenge.G1.Adj 2 (e 3) := by
    simpa only [h2] using e.map_adj_iff.mpr (by decide : Challenge.G1.Adj 2 3)
  have h3 : e 3 = 3 := g1_det3 (e 3) h23
    (image_ne_fixed e e.injective (by decide : (3 : Fin 8) ≠ 0) h0)
    (image_ne_fixed e e.injective (by decide : (3 : Fin 8) ≠ 5) h5)
  have h31 : Challenge.G1.Adj 3 (e 1) := by
    simpa only [h3] using e.map_adj_iff.mpr (by decide : Challenge.G1.Adj 3 1)
  have h1 : e 1 = 1 := g1_det1 (e 1) h31
    (image_ne_fixed e e.injective (by decide : (1 : Fin 8) ≠ 2) h2)
  have h47 : Challenge.G1.Adj 4 (e 7) := by
    simpa only [h4] using e.map_adj_iff.mpr (by decide : Challenge.G1.Adj 4 7)
  have h7 : e 7 = 7 := g1_det7 (e 7) h47
    (image_ne_fixed e e.injective (by decide : (7 : Fin 8) ≠ 0) h0)
    (image_ne_fixed e e.injective (by decide : (7 : Fin 8) ≠ 5) h5)
  have h76 : Challenge.G1.Adj 7 (e 6) := by
    simpa only [h7] using e.map_adj_iff.mpr (by decide : Challenge.G1.Adj 7 6)
  have h6 : e 6 = 6 := g1_det6 (e 6) h76
    (image_ne_fixed e e.injective (by decide : (6 : Fin 8) ≠ 4) h4)
  ext x
  fin_cases x <;> simp_all

theorem g1_classify (e : Challenge.G1 ≃g Challenge.G1) :
    e = SimpleGraph.Iso.refl ∨ e = sigma1 := by
  rcases g1_degree3_choices (e 2) ((e.degree_eq 2).trans g1_degree2) with h2 | h2
  · exact Or.inl (g1_fix2_identity e h2)
  · right
    let f : Challenge.G1 ≃g Challenge.G1 := sigma1.comp e
    have hf2 : f 2 = 2 := by
      change sigma1 (e 2) = 2
      rw [h2]
      rfl
    have hf := g1_fix2_identity f hf2
    ext x
    have h := congrArg (fun g : Challenge.G1 ≃g Challenge.G1 => g x) hf
    change sigma1 (e x) = x at h
    have h' := congrArg (fun y => sigma1 y) h
    rw [sigma1_involutive] at h'
    exact congrArg Fin.val h'

theorem g2_degree0 : Challenge.G2.degree 0 = 3 := by decide +kernel
theorem g2_degree2 : Challenge.G2.degree 2 = 3 := by decide +kernel
theorem g2_degree3 : Challenge.G2.degree 3 = 3 := by decide +kernel
theorem g2_degree5 : Challenge.G2.degree 5 = 2 := by decide +kernel
theorem g2_degree6 : Challenge.G2.degree 6 = 2 := by decide +kernel
theorem g2_degree7 : Challenge.G2.degree 7 = 1 := by decide +kernel
theorem g2_det7 : ∀ x y : Fin 8,
    Challenge.G2.degree x = 1 → Challenge.G2.Adj x y → Challenge.G2.degree y = 2 → x = 7 := by
  decide +kernel
theorem g2_det6 : ∀ x : Fin 8, Challenge.G2.Adj 7 x → x = 6 := by decide +kernel
theorem g2_det0 : ∀ x : Fin 8, Challenge.G2.Adj 6 x → x ≠ 7 → x = 0 := by decide +kernel
theorem g2_det5 : ∀ x : Fin 8, Challenge.G2.degree x = 2 → x ≠ 6 → x = 5 := by decide +kernel
theorem g2_degree3_choices : ∀ x : Fin 8,
    Challenge.G2.degree x = 3 → x ≠ 0 → x = 2 ∨ x = 3 := by decide +kernel
theorem g2_det3 : ∀ x : Fin 8,
    Challenge.G2.degree x = 3 → x ≠ 0 → x ≠ 2 → x = 3 := by decide +kernel
theorem g2_det1 : ∀ x : Fin 8,
    Challenge.G2.Adj 2 x → x ≠ 0 → x ≠ 5 → x = 1 := by decide +kernel
theorem g2_det4 : ∀ x : Fin 8,
    Challenge.G2.Adj 3 x → x ≠ 0 → x ≠ 5 → x = 4 := by decide +kernel

theorem g2_fixed_points (e : Challenge.G2 ≃g Challenge.G2) :
    e 7 = 7 ∧ e 6 = 6 ∧ e 0 = 0 ∧ e 5 = 5 := by
  have h7 : e 7 = 7 := g2_det7 (e 7) (e 6) ((e.degree_eq 7).trans g2_degree7)
    (e.map_adj_iff.mpr (by decide : Challenge.G2.Adj 7 6)) ((e.degree_eq 6).trans g2_degree6)
  have h76 : Challenge.G2.Adj 7 (e 6) := by
    simpa only [h7] using e.map_adj_iff.mpr (by decide : Challenge.G2.Adj 7 6)
  have h6 := g2_det6 (e 6) h76
  have h60 : Challenge.G2.Adj 6 (e 0) := by
    simpa only [h6] using e.map_adj_iff.mpr (by decide : Challenge.G2.Adj 6 0)
  have h0 := g2_det0 (e 0) h60
    (image_ne_fixed e e.injective (by decide : (0 : Fin 8) ≠ 7) h7)
  have h5 := g2_det5 (e 5) ((e.degree_eq 5).trans g2_degree5)
    (image_ne_fixed e e.injective (by decide : (5 : Fin 8) ≠ 6) h6)
  exact ⟨h7, h6, h0, h5⟩

theorem g2_fix2_identity (e : Challenge.G2 ≃g Challenge.G2) (h2 : e 2 = 2) :
    e = SimpleGraph.Iso.refl := by
  obtain ⟨h7, h6, h0, h5⟩ := g2_fixed_points e
  have h3 := g2_det3 (e 3) ((e.degree_eq 3).trans g2_degree3)
    (image_ne_fixed e e.injective (by decide : (3 : Fin 8) ≠ 0) h0)
    (image_ne_fixed e e.injective (by decide : (3 : Fin 8) ≠ 2) h2)
  have h21 : Challenge.G2.Adj 2 (e 1) := by
    simpa only [h2] using e.map_adj_iff.mpr (by decide : Challenge.G2.Adj 2 1)
  have h1 := g2_det1 (e 1) h21
    (image_ne_fixed e e.injective (by decide : (1 : Fin 8) ≠ 0) h0)
    (image_ne_fixed e e.injective (by decide : (1 : Fin 8) ≠ 5) h5)
  have h34 : Challenge.G2.Adj 3 (e 4) := by
    simpa only [h3] using e.map_adj_iff.mpr (by decide : Challenge.G2.Adj 3 4)
  have h4 := g2_det4 (e 4) h34
    (image_ne_fixed e e.injective (by decide : (4 : Fin 8) ≠ 0) h0)
    (image_ne_fixed e e.injective (by decide : (4 : Fin 8) ≠ 5) h5)
  ext x
  fin_cases x <;> simp_all

theorem g2_classify (e : Challenge.G2 ≃g Challenge.G2) :
    e = SimpleGraph.Iso.refl ∨ e = sigma2 := by
  have h0 := (g2_fixed_points e).2.2.1
  have hne := image_ne_fixed e e.injective (by decide : (2 : Fin 8) ≠ 0) h0
  rcases g2_degree3_choices (e 2) ((e.degree_eq 2).trans g2_degree2) hne with h2 | h2
  · exact Or.inl (g2_fix2_identity e h2)
  · right
    let f : Challenge.G2 ≃g Challenge.G2 := sigma2.comp e
    have hf2 : f 2 = 2 := by
      change sigma2 (e 2) = 2
      rw [h2]
      rfl
    have hf := g2_fix2_identity f hf2
    ext x
    have h := congrArg (fun g : Challenge.G2 ≃g Challenge.G2 => g x) hf
    change sigma2 (e x) = x at h
    have h' := congrArg (fun y => sigma2 y) h
    rw [sigma2_involutive] at h'
    exact congrArg Fin.val h'

theorem g1_aut_card : Nat.card (Challenge.G1 ≃g Challenge.G1) = 2 := by
  apply Nat.card_eq_two_iff.mpr
  refine ⟨SimpleGraph.Iso.refl, sigma1, ?_, ?_⟩
  · intro h
    have h2 := congrArg (fun e : Challenge.G1 ≃g Challenge.G1 => e 2) h
    exact (by decide : (2 : Fin 8) ≠ 4) h2
  · ext e
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_univ, iff_true]
    exact g1_classify e

theorem g2_aut_card : Nat.card (Challenge.G2 ≃g Challenge.G2) = 2 := by
  apply Nat.card_eq_two_iff.mpr
  refine ⟨SimpleGraph.Iso.refl, sigma2, ?_, ?_⟩
  · intro h
    have h2 := congrArg (fun e : Challenge.G2 ≃g Challenge.G2 => e 2) h
    exact (by decide : (2 : Fin 8) ≠ 3) h2
  · ext e
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_univ, iff_true]
    exact g2_classify e

end GraphAutomorphisms

theorem check_Sec4_aut : Challenge.Sec4_aut :=
  ⟨GraphAutomorphisms.g1_aut_card, GraphAutomorphisms.g2_aut_card⟩

#print axioms check_Sec4_aut

end CodexPaper4
