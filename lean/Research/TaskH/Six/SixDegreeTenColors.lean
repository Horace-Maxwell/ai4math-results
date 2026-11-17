import Research.TaskH.Six.SingletonClique

/-!
Actual degree-ten neighbor color fibers in a K4-free equality branch.
There are exactly two singleton colors and four fibers of size two.
No adjacency between the two singleton vertices is asserted.
-/

set_option autoImplicit false

universe u

namespace TaskH.Six

open SimpleGraph _root_.TaskH.Challenge
open scoped Classical

variable {V : Type u} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem degreeTenSingletonNeighbor_val_injective (v : V)
    (c : (G.induce {x | x ≠ v}).Coloring (Fin 6)) :
    Function.Injective (fun i : ↥(singletonNeighborColors v c) =>
      (singletonNeighbor v c i).val) := by
  intro i j he
  have hn : singletonNeighbor v c i = singletonNeighbor v c j := Subtype.ext he
  have hh := congrArg (neighborColor v c) hn
  rw [singletonNeighbor_color, singletonNeighbor_color] at hh
  exact Subtype.ext hh

theorem singleton_colors_card_le_two_of_cliqueFree_four
    (hcrit : IsCriticalPlus 6 G) (hs : ShortSixCycles G) (hr : RainbowSixCycles G)
    (hfree : G.CliqueFree 4) (v : V)
    (c : (G.induce {x | x ≠ v}).Coloring (Fin 6)) :
    (singletonNeighborColors v c).card ≤ 2 := by
  classical
  by_contra hbig
  have hthree : 3 ≤ (singletonNeighborColors v c).card := by omega
  obtain ⟨S, hsub, hScard⟩ := Finset.exists_subset_card_eq hthree
  let e : Fin 3 ≃ ↥S := (Finset.equivFinOfCardEq hScard).symm
  let j : Fin 3 → ↥(singletonNeighborColors v c) :=
    fun i => ⟨(e i).val, hsub (e i).property⟩
  have hj : Function.Injective j := by
    intro i k he
    apply e.injective
    apply Subtype.ext
    exact congrArg (fun x : ↥(singletonNeighborColors v c) => x.val) he
  let N : Fin 3 → V := fun i => (singletonNeighbor v c (j i)).val
  have hNi : Function.Injective N := (degreeTenSingletonNeighbor_val_injective v c).comp hj
  have hroot : ∀ i, G.Adj v (N i) := fun i => (singletonNeighbor v c (j i)).property
  have hroot' : ∀ i, G.Adj (N i) v := fun i => (hroot i).symm
  have hNv : ∀ i, v ≠ N i := fun i => (hroot i).ne
  have hNv' : ∀ i, N i ≠ v := fun i => (hNv i).symm
  have hNN : ∀ i k, i ≠ k → G.Adj (N i) (N k) := by
    intro i k hik
    exact singleton_neighbors_adj hcrit hs hr v c hthree (j i) (j k)
      (fun he => hik (hj he))
  let q : Fin 4 → V := ![v, N 0, N 1, N 2]
  have hqi : Function.Injective q := by
    intro i k he
    fin_cases i <;> fin_cases k <;> simp_all [q, hNi.eq_iff]
  have hqadj : ∀ i k : Fin 4, i ≠ k → G.Adj (q i) (q k) := by
    intro i k hik
    fin_cases i <;> fin_cases k <;> simp_all [q]
  let Q := Finset.univ.image q
  have hQc : G.IsClique (Q : Set V) := by
    intro x hx y hy hxy
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hy
    exact hqadj i k (fun he => hxy (congrArg q he))
  have hQcard : Q.card = 4 := by
    change (Finset.univ.image q).card = 4
    rw [Finset.card_image_of_injective _ hqi, Finset.card_univ, Fintype.card_fin]
  exact hfree Q ⟨hQc, hQcard⟩

theorem degreeTen_singleton_colors_card
    (hcrit : IsCriticalPlus 6 G) (hs : ShortSixCycles G) (hr : RainbowSixCycles G)
    (hfree : G.CliqueFree 4) (v : V)
    (c : (G.induce {x | x ≠ v}).Coloring (Fin 6)) (hv : G.degree v = 10) :
    (singletonNeighborColors v c).card = 2 := by
  have hlo := singletonNeighborColors_card_ge hcrit v c
  have hhi := singleton_colors_card_le_two_of_cliqueFree_four hcrit hs hr hfree v c
  rw [hv] at hlo
  omega

theorem degreeTen_neighborColorFiber_card
    (hcrit : IsCriticalPlus 6 G) (hs : ShortSixCycles G) (hr : RainbowSixCycles G)
    (hfree : G.CliqueFree 4) (v : V)
    (c : (G.induce {x | x ≠ v}).Coloring (Fin 6)) (hv : G.degree v = 10) (i : Fin 6) :
    (neighborColorFiber v c i).card =
      if i ∈ singletonNeighborColors v c then 1 else 2 := by
  classical
  let S := singletonNeighborColors v c
  have hS : S.card = 2 := degreeTen_singleton_colors_card hcrit hs hr hfree v c hv
  have hpos : ∀ k : Fin 6, 0 < (neighborColorFiber v c k).card := by
    intro k
    obtain ⟨z, hz⟩ := critical_neighborColor_surjective hcrit v c k
    exact Finset.card_pos.mpr ⟨z, (mem_neighborColorFiber v c k z).mpr hz⟩
  have hlo : ∀ k ∈ (Finset.univ : Finset (Fin 6)),
      (if k ∈ S then 1 else 2 : ℕ) ≤ (neighborColorFiber v c k).card := by
    intro k _hk
    by_cases hk : k ∈ S
    · rw [ite_eq_left hk]
      exact ((mem_singletonNeighborColors v c k).mp hk).symm.le
    · rw [ite_eq_right hk]
      have hne : (neighborColorFiber v c k).card ≠ 1 := by
        intro he
        exact hk ((mem_singletonNeighborColors v c k).mpr he)
      have hp := hpos k
      omega
  have hindicator : (∑ k : Fin 6, if k ∈ S then 1 else 0 : ℕ) = S.card := by
    have hf : (Finset.univ.filter (fun k : Fin 6 => k ∈ S)) = S := by ext k; simp
    calc
      _ = (Finset.univ.filter (fun k : Fin 6 => k ∈ S)).card := by
        simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
      _ = _ := congrArg Finset.card hf
  have hpair : ∀ k : Fin 6,
      (if k ∈ S then 1 else 2 : ℕ) + (if k ∈ S then 1 else 0 : ℕ) = 2 := by
    intro k
    split_ifs <;> rfl
  have hsumlo : (∑ k : Fin 6, if k ∈ S then 1 else 2 : ℕ) = 10 := by
    have he : (∑ k : Fin 6, if k ∈ S then 1 else 2 : ℕ) + S.card = 12 := by
      rw [← hindicator, ← Finset.sum_add_distrib]
      norm_num [hpair]
    omega
  have hsumhi : (∑ k : Fin 6, (neighborColorFiber v c k).card) = 10 := by
    rw [sum_neighborColorFiber_card, G.card_neighborSet_eq_degree, hv]
  have heq : (∑ k : Fin 6, if k ∈ S then 1 else 2 : ℕ) =
      ∑ k : Fin 6, (neighborColorFiber v c k).card := hsumlo.trans hsumhi.symm
  exact ((Finset.sum_eq_sum_iff_of_le hlo).mp heq i (Finset.mem_univ _)).symm

end TaskH.Six

#print axioms TaskH.Six.degreeTenSingletonNeighbor_val_injective
#print axioms TaskH.Six.singleton_colors_card_le_two_of_cliqueFree_four
#print axioms TaskH.Six.degreeTen_singleton_colors_card
#print axioms TaskH.Six.degreeTen_neighborColorFiber_card
