import Research.TaskH.Six.HexagonWordsCardinality

/-!
A concrete family of 5760 different ordered hexagons in an actual K_(4,6)
subgraph. Extra edges in the ambient graph cause no identification of words.
The finite embedding-cardinality theorem supplies the count symbolically.
-/

set_option autoImplicit false

universe u

namespace TaskH.Six

open SimpleGraph Challenge

variable {V : Type u} {G : SimpleGraph V}

abbrev BipartiteSixParameter := Bool × (Fin 3 ↪ Fin 4) × (Fin 3 ↪ Fin 6)

def bipartiteSixWord (q : Fin 4 → V) (t : Fin 6 → V)
    (p : BipartiteSixParameter) : Fin 6 → V :=
  if p.1 then
    ![t (p.2.2 0), q (p.2.1 0), t (p.2.2 1), q (p.2.1 1), t (p.2.2 2), q (p.2.1 2)]
  else
    ![q (p.2.1 0), t (p.2.2 0), q (p.2.1 1), t (p.2.2 1), q (p.2.1 2), t (p.2.2 2)]

def bipartiteSixLeftIndex (reverse : Bool) (i : Fin 3) : Fin 6 :=
  if reverse then ![1, 3, 5] i else ![0, 2, 4] i

def bipartiteSixRightIndex (reverse : Bool) (i : Fin 3) : Fin 6 :=
  if reverse then ![0, 2, 4] i else ![1, 3, 5] i

theorem bipartiteSixWord_left (q : Fin 4 → V) (t : Fin 6 → V)
    (p : BipartiteSixParameter) (i : Fin 3) :
    bipartiteSixWord q t p (bipartiteSixLeftIndex p.1 i) = q (p.2.1 i) := by
  rcases p with ⟨b, l, r⟩
  cases b <;> fin_cases i <;> rfl

theorem bipartiteSixWord_right (q : Fin 4 → V) (t : Fin 6 → V)
    (p : BipartiteSixParameter) (i : Fin 3) :
    bipartiteSixWord q t p (bipartiteSixRightIndex p.1 i) = t (p.2.2 i) := by
  rcases p with ⟨b, l, r⟩
  cases b <;> fin_cases i <;> rfl

theorem bipartiteSixWord_injective (q : Fin 4 → V) (t : Fin 6 → V)
    (hq : Function.Injective q) (ht : Function.Injective t)
    (hqt : ∀ i j, q i ≠ t j) (p : BipartiteSixParameter) :
    Function.Injective (bipartiteSixWord q t p) := by
  rcases p with ⟨b, l, r⟩
  have hl := l.injective
  have hr := r.injective
  have htq : ∀ j i, t j ≠ q i := fun j i => (hqt i j).symm
  cases b <;> intro i j hij <;> fin_cases i <;> fin_cases j <;>
    simp_all [bipartiteSixWord, hq.eq_iff, ht.eq_iff, hl.eq_iff, hr.eq_iff]

theorem bipartiteSixWord_parameters_injective (q : Fin 4 → V) (t : Fin 6 → V)
    (hq : Function.Injective q) (ht : Function.Injective t)
    (hqt : ∀ i j, q i ≠ t j) : Function.Injective (bipartiteSixWord q t) := by
  rintro ⟨b, l, r⟩ ⟨b', l', r'⟩ he
  have hb : b = b' := by
    have h0 := congrFun he 0
    cases b <;> cases b'
    · rfl
    · exact False.elim (hqt (l 0) (r' 0) (by simpa [bipartiteSixWord] using h0))
    · exact False.elim (hqt (l' 0) (r 0) (by simpa [bipartiteSixWord] using h0.symm))
    · rfl
  subst b'
  have hl : l = l' := by
    apply DFunLike.coe_injective
    funext i
    apply hq
    rw [← bipartiteSixWord_left q t (b, l, r) i,
      ← bipartiteSixWord_left q t (b, l', r') i]
    exact congrFun he (bipartiteSixLeftIndex b i)
  have hr : r = r' := by
    apply DFunLike.coe_injective
    funext i
    apply ht
    rw [← bipartiteSixWord_right q t (b, l, r) i,
      ← bipartiteSixWord_right q t (b, l', r') i]
    exact congrFun he (bipartiteSixRightIndex b i)
  exact Prod.ext rfl (Prod.ext hl hr)

theorem bipartiteSixWord_isHexagon (q : Fin 4 → V) (t : Fin 6 → V)
    (hq : Function.Injective q) (ht : Function.Injective t)
    (hqt : ∀ i j, q i ≠ t j) (hcross : ∀ i j, G.Adj (q i) (t j))
    (p : BipartiteSixParameter) : IsHexagon G (bipartiteSixWord q t p) := by
  have hi := bipartiteSixWord_injective q t hq ht hqt p
  rcases p with ⟨b, l, r⟩
  cases b
  · exact ⟨hi, hcross (l 0) (r 0), (hcross (l 1) (r 0)).symm,
      hcross (l 1) (r 1), (hcross (l 2) (r 1)).symm,
      hcross (l 2) (r 2), (hcross (l 0) (r 2)).symm⟩
  · exact ⟨hi, (hcross (l 0) (r 0)).symm, hcross (l 0) (r 1),
      (hcross (l 1) (r 1)).symm, hcross (l 1) (r 2),
      (hcross (l 2) (r 2)).symm, hcross (l 2) (r 0)⟩

noncomputable def bipartiteSixWords (q : Fin 4 → V) (t : Fin 6 → V) :
    Finset (Fin 6 → V) := by
  classical
  exact Finset.univ.image (bipartiteSixWord q t)

theorem bipartiteSixWords_card (q : Fin 4 → V) (t : Fin 6 → V)
    (hq : Function.Injective q) (ht : Function.Injective t)
    (hqt : ∀ i j, q i ≠ t j) : (bipartiteSixWords q t).card = 5760 := by
  classical
  rw [bipartiteSixWords, Finset.card_image_of_injective _
    (bipartiteSixWord_parameters_injective q t hq ht hqt), Finset.card_univ]
  norm_num [BipartiteSixParameter, Fintype.card_prod, Fintype.card_embedding_eq,
    Nat.descFactorial]

theorem bipartiteSixWords_subset_hexagonWords [Fintype V]
    (q : Fin 4 → V) (t : Fin 6 → V)
    (hq : Function.Injective q) (ht : Function.Injective t)
    (hqt : ∀ i j, q i ≠ t j) (hcross : ∀ i j, G.Adj (q i) (t j)) :
    bipartiteSixWords q t ⊆ hexagonWords G := by
  classical
  intro f hf
  obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp hf
  exact (mem_hexagonWords_iff _).mpr (bipartiteSixWord_isHexagon q t hq ht hqt hcross p)

theorem actual_bipartite_four_six_modCycleCount_ge [Fintype V]
    (q : Fin 4 → V) (t : Fin 6 → V)
    (hq : Function.Injective q) (ht : Function.Injective t)
    (hqt : ∀ i j, q i ≠ t j) (hcross : ∀ i j, G.Adj (q i) (t j)) :
    480 ≤ modCycleCount 6 G := by
  classical
  have hlo := Finset.card_le_card (bipartiteSixWords_subset_hexagonWords
    q t hq ht hqt hcross)
  rw [bipartiteSixWords_card q t hq ht hqt] at hlo
  have hhi := hexagonWords_card_le_twelve_mul_modCycleCount (G := G)
  omega

end TaskH.Six

#print axioms TaskH.Six.BipartiteSixParameter
#print axioms TaskH.Six.bipartiteSixWord
#print axioms TaskH.Six.bipartiteSixLeftIndex
#print axioms TaskH.Six.bipartiteSixRightIndex
#print axioms TaskH.Six.bipartiteSixWord_left
#print axioms TaskH.Six.bipartiteSixWord_right
#print axioms TaskH.Six.bipartiteSixWord_injective
#print axioms TaskH.Six.bipartiteSixWord_parameters_injective
#print axioms TaskH.Six.bipartiteSixWord_isHexagon
#print axioms TaskH.Six.bipartiteSixWords
#print axioms TaskH.Six.bipartiteSixWords_card
#print axioms TaskH.Six.bipartiteSixWords_subset_hexagonWords
#print axioms TaskH.Six.actual_bipartite_four_six_modCycleCount_ge
