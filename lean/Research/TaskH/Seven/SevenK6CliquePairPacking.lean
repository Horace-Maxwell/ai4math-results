import Research.TaskH.Seven.SevenK6CliquePairPaths

set_option autoImplicit false

universe u

namespace TaskH.Seven

open SimpleGraph _root_.TaskH.Challenge _root_.TaskH.Six
open scoped Classical

variable {V : Type u} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem six_clique_hook_pair_exact (hcrit : IsCriticalPlus 7 G)
    (hs : ShortSevenCycles G) (hr : RainbowSevenCycles G)
    (hc : modCycleCount 7 G = 2880) (hn : 9 ≤ Fintype.card V)
    (q : Fin 6 → V) (hq : Function.Injective q)
    (hclique : ∀ i j, i ≠ j → G.Adj (q i) (q j))
    (y : V) (hy : ∀ i, y ≠ q i)
    (hy0 : G.Adj y (q 0)) (hy1 : G.Adj y (q 1)) :
    ∀ i : Fin 6, G.Adj y (q i) ↔ i = 0 ∨ i = 1 := by
  classical
  have hle := critical_six_clique_hooks_card_le_two hcrit hs hr hc hn q hq hclique y hy
  have hmem : ∀ i : Fin 6, i ∈ sixCliqueHooks G q y ↔ G.Adj y (q i) := by
    intro i
    simp only [sixCliqueHooks, Finset.mem_filter, Finset.mem_univ, true_and]
  have hsub : ({0, 1} : Finset (Fin 6)) ⊆ sixCliqueHooks G q y := by
    intro i hi
    rcases Finset.mem_insert.mp hi with rfl | hi
    · exact (hmem 0).mpr hy0
    · have he : i = 1 := Finset.mem_singleton.mp hi
      subst i
      exact (hmem 1).mpr hy1
  have he : sixCliqueHooks G q y = {0, 1} := by
    symm
    apply Finset.eq_of_subset_of_card_le hsub
    simpa only [Finset.card_pair (by decide : (0 : Fin 6) ≠ 1)] using hle
  intro i
  have hi : i ∈ sixCliqueHooks G q y ↔ G.Adj y (q i) := by simp [sixCliqueHooks]
  rw [← hi, he]
  simp only [Finset.mem_insert, Finset.mem_singleton]

omit [Fintype V] in
theorem six_pair_anchor_neighbors_exact (q : Fin 6 → V) (y : V)
    (hexact : ∀ i : Fin 6, G.Adj y (q i) ↔ i = 0 ∨ i = 1) :
    packingNeighborsIn G (sixCliqueSevenSet q y) y = {q 0, q 1} := by
  classical
  ext x
  simp only [packingNeighborsIn, Finset.mem_filter, sixCliqueSevenSet,
    Finset.mem_insert, mem_sixCliqueSet, Finset.mem_singleton]
  constructor
  · rintro ⟨hx | ⟨i, hi⟩, hadj⟩
    · exact (hadj.ne hx.symm).elim
    · have hqi : G.Adj y (q i) := by simpa only [hi] using hadj
      rcases (hexact i).mp hqi with rfl | rfl
      · exact Or.inl hi.symm
      · exact Or.inr hi.symm
  · rintro (rfl | rfl)
    · exact ⟨Or.inr ⟨0, rfl⟩, (hexact 0).mpr (Or.inl rfl)⟩
    · exact ⟨Or.inr ⟨1, rfl⟩, (hexact 1).mpr (Or.inr rfl)⟩

theorem six_pair_family_neighbors_exact (hcrit : IsCriticalPlus 7 G)
    (hr : RainbowSevenCycles G) (hn : 11 ≤ Fintype.card V)
    (q : Fin 6 → V) (hq : Function.Injective q)
    (hclique : ∀ i j, i ≠ j → G.Adj (q i) (q j))
    (y : V) (hy : ∀ i, y ≠ q i)
    (hexact : ∀ i : Fin 6, G.Adj y (q i) ↔ i = 0 ∨ i = 1)
    (x : V) (hx : x ∈ sixPairFamily G q y) :
    packingNeighborsIn G (sixCliqueSevenSet q y) x = {q 0, q 1} := by
  rcases Finset.mem_insert.mp hx with hxy | hx
  · rw [hxy]
    exact six_pair_anchor_neighbors_exact q y hexact
  · exact six_pair_clone_neighbors_exact hcrit hr hn q hq hclique y hy
      ((hexact 0).mpr (Or.inl rfl)) ((hexact 1).mpr (Or.inr rfl)) x hx

/-- Actual disjoint outside-neighbor pools yield n ≥ 13+7r, including the
anchor y as an additional member of the same independent forced family. -/
theorem six_pair_clone_packing (hcrit : IsCriticalPlus 7 G)
    (hr : RainbowSevenCycles G) (hn : 11 ≤ Fintype.card V)
    (hdegree : ∀ x : V, 8 ≤ G.degree x)
    (q : Fin 6 → V) (hq : Function.Injective q)
    (hclique : ∀ i j, i ≠ j → G.Adj (q i) (q j))
    (y : V) (hy : ∀ i, y ≠ q i)
    (hexact : ∀ i : Fin 6, G.Adj y (q i) ↔ i = 0 ∨ i = 1) :
    13 + 7 * (sixPairClones G q y).card ≤ Fintype.card V := by
  classical
  let T := sixCliqueSevenSet q y
  let Z := sixPairClones G q y
  let W := sixPairFamily G q y
  let H := (T ∪ Z)ᶜ
  have hy0 := (hexact 0).mpr (Or.inl rfl)
  have hy1 := (hexact 1).mpr (Or.inr rfl)
  have hind := six_pair_family_independent hcrit hr hn q hq hclique y hy hy0 hy1
  have hrow : ∀ x ∈ W, 6 ≤ (packingNeighborsIn G H x).card := by
    intro x hx
    have hin : (packingNeighborsIn G T x).card ≤ 2 := by
      rw [six_pair_family_neighbors_exact hcrit hr hn q hq hclique y hy hexact x hx]
      exact Finset.card_le_two
    have hout := packingNeighborsIn_compl_lower T x 8 2 (hdegree x) hin
    have hsub : packingNeighborsIn G Tᶜ x ⊆ packingNeighborsIn G H x := by
      intro z hz
      have hzT := Finset.mem_compl.mp (Finset.mem_filter.mp hz).1
      have hxz := (Finset.mem_filter.mp hz).2
      have hzZ : z ∉ Z := by
        intro hzZ
        have hzW : z ∈ sixPairFamily G q y := Finset.mem_insert_of_mem hzZ
        exact hind x hx z hzW hxz
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_compl.mpr ?_, hxz⟩
      intro hzu
      exact (Finset.mem_union.mp hzu).elim hzT hzZ
    exact hout.trans (Finset.card_le_card hsub)
  have hcommon : ∀ z ∈ H, ∀ x ∈ W, ∀ x' ∈ W,
      G.Adj x z → G.Adj x' z → x = x' := by
    intro z hz x hx x' hx' hxz hx'z
    have hzT : z ∉ sixCliqueSevenSet q y := by
      intro hm
      exact (Finset.mem_compl.mp hz) (Finset.mem_union_left Z hm)
    exact six_pair_family_common_neighbor_unique hcrit hr hn q hq hclique y hy hy0 hy1
      z hzT x hx x' hx' hxz hx'z
  have hpack := actual_open_neighborhood_uniform_packing W H 6 hrow hcommon
  have hT : T.card = 7 := sixCliqueSevenSet_card q hq y hy
  have hTZ : Disjoint T Z := by
    apply Finset.disjoint_left.mpr
    intro x hxT hxZ
    exact six_pair_clone_outside q y x hxZ hxT
  have hyZ : y ∉ Z := by
    intro hyZ
    exact six_pair_clone_outside q y y hyZ (Finset.mem_insert_self y (sixCliqueSet q))
  have hW : W.card = Z.card + 1 := Finset.card_insert_of_notMem hyZ
  have hU : (T ∪ Z).card = 7 + Z.card := by rw [Finset.card_union_of_disjoint hTZ, hT]
  have hH := Finset.card_add_card_compl (T ∪ Z)
  change (T ∪ Z).card + H.card = Fintype.card V at hH
  rw [hW] at hpack
  rw [hU] at hH
  change 13 + 7 * Z.card ≤ Fintype.card V
  omega

end TaskH.Seven

#print axioms TaskH.Seven.six_clique_hook_pair_exact
#print axioms TaskH.Seven.six_pair_anchor_neighbors_exact
#print axioms TaskH.Seven.six_pair_family_neighbors_exact
#print axioms TaskH.Seven.six_pair_clone_packing
