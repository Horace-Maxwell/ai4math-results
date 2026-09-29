import Research.Backfill.Paper3.Proof.CD.Markov

/-!
# `G_n = k H_d ∪ r K_{d,d}` and Lemma 6 evaluated

Regularity is checked through `Nat.card` of neighbour sets (independent of the `Fintype`
instances): copies (`⊥ □ H`) and disjoint sums (`⊕g`) keep the neighbour sets of each vertex up
to an injective image. Bipartiteness: a 2-colouring of `H` pulls back along `Prod.snd`, and
`colorable_sum`. Lemma 6 at a real point: `P_d(q)² - P_{H_d}(q) = 2 (q - 1) D(q)`.
-/

set_option autoImplicit false

namespace P3CD

open Finset SimpleGraph Polynomial BackfillPaper3.Challenge P3Basic

theorem isRegular_iff_natCard {V : Type*} (G : SimpleGraph V) [G.LocallyFinite] (d : ℕ) :
    G.IsRegularOfDegree d ↔ ∀ v, Nat.card (G.neighborSet v) = d := by
  simp only [SimpleGraph.IsRegularOfDegree, ← SimpleGraph.card_neighborSet_eq_degree,
    Nat.card_eq_fintype_card]

theorem neighborSet_copies {W : Type*} (m : ℕ) (H : SimpleGraph W) (p : Fin m × W) :
    (copies m H).neighborSet p = (fun y => (p.1, y)) '' H.neighborSet p.2 := by
  ext ⟨j, y⟩
  simp only [SimpleGraph.mem_neighborSet, SimpleGraph.boxProd_adj, SimpleGraph.bot_adj,
    false_and, false_or, Set.mem_image, Prod.mk.injEq]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨y, h1, h2, rfl⟩
  · rintro ⟨y', h1, h2, rfl⟩
    exact ⟨h1, h2⟩

theorem natCard_neighborSet_copies {W : Type*} (m : ℕ) (H : SimpleGraph W) (p : Fin m × W) :
    Nat.card ((copies m H).neighborSet p) = Nat.card (H.neighborSet p.2) := by
  rw [neighborSet_copies]
  exact Nat.card_image_of_injective (fun y₁ y₂ h => congrArg Prod.snd h) _

theorem natCard_neighborSet_Kdd (d : ℕ) (v : Fin d ⊕ Fin d) :
    Nat.card ((Kdd d).neighborSet v) = d := by
  rcases v with a | a
  · have h : (Kdd d).neighborSet (.inl a) = Set.range Sum.inr := by
      ext (x | x) <;> simp
    rw [h, Nat.card_range_of_injective Sum.inr_injective, Nat.card_eq_fintype_card,
      Fintype.card_fin]
  · have h : (Kdd d).neighborSet (.inr a) = Set.range Sum.inl := by
      ext (x | x) <;> simp
    rw [h, Nat.card_range_of_injective Sum.inl_injective, Nat.card_eq_fintype_card,
      Fintype.card_fin]

theorem Gn_regular (d m : ℕ) (a₁ b₁ a₂ b₂ : Fin d)
    (hH : (Hd d a₁ b₁ a₂ b₂).IsRegularOfDegree d) : (Gn d m a₁ b₁ a₂ b₂).IsRegularOfDegree d := by
  rw [isRegular_iff_natCard] at hH ⊢
  rintro (p | p)
  · show Nat.card ((copies (m / 2) (Hd d a₁ b₁ a₂ b₂) ⊕g KddUnion (m % 2) d).neighborSet
      (.inl p)) = d
    rw [SimpleGraph.neighborSet_sum_inl, Nat.card_image_of_injective Sum.inl_injective,
      natCard_neighborSet_copies]
    exact hH p.2
  · show Nat.card ((copies (m / 2) (Hd d a₁ b₁ a₂ b₂) ⊕g KddUnion (m % 2) d).neighborSet
      (.inr p)) = d
    rw [SimpleGraph.neighborSet_sum_inr, Nat.card_image_of_injective Sum.inr_injective,
      natCard_neighborSet_copies]
    exact natCard_neighborSet_Kdd d p.2

theorem colorable_copies {W : Type*} (m : ℕ) (H : SimpleGraph W) {n : ℕ} (hH : H.Colorable n) :
    (copies m H).Colorable n := by
  obtain ⟨c⟩ := hH
  let f : copies m H →g H := ⟨Prod.snd, fun {p q} h => by
    rcases SimpleGraph.boxProd_adj.1 h with ⟨h1, _⟩ | ⟨h1, _⟩
    · exact absurd h1 (by simp)
    · exact h1⟩
  exact ⟨c.comp f⟩

theorem Gn_bipartite (d m : ℕ) (a₁ b₁ a₂ b₂ : Fin d) (hH : (Hd d a₁ b₁ a₂ b₂).IsBipartite) :
    (Gn d m a₁ b₁ a₂ b₂).IsBipartite :=
  SimpleGraph.colorable_sum.2 ⟨colorable_copies _ _ hH,
    colorable_copies _ _ (SimpleGraph.IsBipartite.completeBipartiteGraph _ _)⟩

/-- Lemma 6 at a real point: `P_d(q)² - P_{H_d}(q) = 2 (q - 1) D(q)`. -/
theorem base_diff (h6 : Lemma6) (d : ℕ) (hd : 2 ≤ d) (a₁ b₁ a₂ b₂ : Fin d) (q : ℝ) :
    Pf d q ^ 2 - evalR (edgePoly (Hd d a₁ b₁ a₂ b₂)) q = 2 * (q - 1) * evalR (Dpoly d) q := by
  have h := congrArg (fun p => evalR p q) (h6 d hd a₁ b₁ a₂ b₂).1
  have e1 : evalR (edgePoly (KddUnion 2 d) - edgePoly (Hd d a₁ b₁ a₂ b₂)) q =
      evalR (edgePoly (KddUnion 2 d)) q - evalR (edgePoly (Hd d a₁ b₁ a₂ b₂)) q := by
    unfold evalR
    exact map_sub _ _ _
  have e2 : evalR (2 * (X - 1) * Dpoly d) q = 2 * (q - 1) * evalR (Dpoly d) q := by
    simp only [evalR, map_mul, map_sub, Polynomial.aeval_X, map_one, map_ofNat]
  rw [e1, e2, evalR_KddUnion] at h
  exact h

end P3CD
