import Research.TaskH.Six.SixFiveCliquePairPaths

set_option autoImplicit false

universe u

namespace TaskH.Six

open SimpleGraph _root_.TaskH.Challenge
open scoped Classical

variable {V : Type u} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem five_clique_hook_pair_exact (hcrit : IsCriticalPlus 6 G)
    (hs : ShortSixCycles G) (hr : RainbowSixCycles G)
    (hc : modCycleCount 6 G = 420) (hn : 8 ≤ Fintype.card V)
    (q : Fin 5 → V) (hq : Function.Injective q)
    (hclique : ∀ i j, i ≠ j → G.Adj (q i) (q j))
    (y : V) (hy : ∀ i, y ≠ q i)
    (hy0 : G.Adj y (q 0)) (hy1 : G.Adj y (q 1)) :
    ∀ i : Fin 5, G.Adj y (q i) ↔ i = 0 ∨ i = 1 := by
  classical
  have hle := critical_five_clique_hooks_card_le_two hcrit hs hr hc hn q hq hclique y hy
  have hmem : ∀ i : Fin 5, i ∈ fiveCliqueHooks G q y ↔ G.Adj y (q i) := by
    intro i
    simp only [fiveCliqueHooks, Finset.mem_filter, Finset.mem_univ, true_and]
  have hsub : ({0, 1} : Finset (Fin 5)) ⊆ fiveCliqueHooks G q y := by
    intro i hi
    rcases Finset.mem_insert.mp hi with rfl | hi
    · exact (hmem 0).mpr hy0
    · have he : i = 1 := Finset.mem_singleton.mp hi
      subst i
      exact (hmem 1).mpr hy1
  have he : fiveCliqueHooks G q y = {0, 1} := by
    symm
    apply Finset.eq_of_subset_of_card_le hsub
    simpa only [Finset.card_pair (by decide : (0 : Fin 5) ≠ 1)] using hle
  intro i
  have hi : i ∈ fiveCliqueHooks G q y ↔ G.Adj y (q i) := by simp [fiveCliqueHooks]
  rw [← hi, he]
  simp only [Finset.mem_insert, Finset.mem_singleton]

omit [Fintype V] in
theorem five_pair_anchor_neighbors_exact (q : Fin 5 → V) (y : V)
    (hexact : ∀ i : Fin 5, G.Adj y (q i) ↔ i = 0 ∨ i = 1) :
    packingNeighborsIn G (fiveCliqueSixSet q y) y = {q 0, q 1} := by
  classical
  ext x
  simp only [packingNeighborsIn, Finset.mem_filter, fiveCliqueSixSet,
    Finset.mem_insert, mem_fiveCliqueSet, Finset.mem_singleton]
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

theorem five_pair_family_neighbors_exact (hcrit : IsCriticalPlus 6 G)
    (hr : RainbowSixCycles G) (hn : 10 ≤ Fintype.card V)
    (q : Fin 5 → V) (hq : Function.Injective q)
    (hclique : ∀ i j, i ≠ j → G.Adj (q i) (q j))
    (y : V) (hy : ∀ i, y ≠ q i)
    (hexact : ∀ i : Fin 5, G.Adj y (q i) ↔ i = 0 ∨ i = 1)
    (x : V) (hx : x ∈ fivePairFamily G q y) :
    packingNeighborsIn G (fiveCliqueSixSet q y) x = {q 0, q 1} := by
  rcases Finset.mem_insert.mp hx with hxy | hx
  · rw [hxy]
    exact five_pair_anchor_neighbors_exact q y hexact
  · exact five_pair_clone_neighbors_exact hcrit hr hn q hq hclique y hy
      ((hexact 0).mpr (Or.inl rfl)) ((hexact 1).mpr (Or.inr rfl)) x hx

/-- Actual disjoint outside-neighbor pools yield n ≥ 12+7r, including the
anchor y as an additional member of the same independent forced family. -/
theorem five_pair_clone_packing (hcrit : IsCriticalPlus 6 G)
    (hr : RainbowSixCycles G) (hn : 10 ≤ Fintype.card V)
    (hdegree : ∀ x : V, 8 ≤ G.degree x)
    (q : Fin 5 → V) (hq : Function.Injective q)
    (hclique : ∀ i j, i ≠ j → G.Adj (q i) (q j))
    (y : V) (hy : ∀ i, y ≠ q i)
    (hexact : ∀ i : Fin 5, G.Adj y (q i) ↔ i = 0 ∨ i = 1) :
    12 + 7 * (fivePairClones G q y).card ≤ Fintype.card V := by
  classical
  let T := fiveCliqueSixSet q y
  let Z := fivePairClones G q y
  let W := fivePairFamily G q y
  let H := (T ∪ Z)ᶜ
  have hy0 := (hexact 0).mpr (Or.inl rfl)
  have hy1 := (hexact 1).mpr (Or.inr rfl)
  have hind := five_pair_family_independent hcrit hr hn q hq hclique y hy hy0 hy1
  have hrow : ∀ x ∈ W, 6 ≤ (packingNeighborsIn G H x).card := by
    intro x hx
    have hin : (packingNeighborsIn G T x).card ≤ 2 := by
      rw [five_pair_family_neighbors_exact hcrit hr hn q hq hclique y hy hexact x hx]
      exact Finset.card_le_two
    have hout := packingNeighborsIn_compl_lower T x 8 2 (hdegree x) hin
    have hsub : packingNeighborsIn G Tᶜ x ⊆ packingNeighborsIn G H x := by
      intro z hz
      have hzT := Finset.mem_compl.mp (Finset.mem_filter.mp hz).1
      have hxz := (Finset.mem_filter.mp hz).2
      have hzZ : z ∉ Z := by
        intro hzZ
        have hzW : z ∈ fivePairFamily G q y := Finset.mem_insert_of_mem hzZ
        exact hind x hx z hzW hxz
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_compl.mpr ?_, hxz⟩
      intro hzu
      exact (Finset.mem_union.mp hzu).elim hzT hzZ
    exact hout.trans (Finset.card_le_card hsub)
  have hcommon : ∀ z ∈ H, ∀ x ∈ W, ∀ x' ∈ W,
      G.Adj x z → G.Adj x' z → x = x' := by
    intro z hz x hx x' hx' hxz hx'z
    have hzT : z ∉ fiveCliqueSixSet q y := by
      intro hm
      exact (Finset.mem_compl.mp hz) (Finset.mem_union_left Z hm)
    exact five_pair_family_common_neighbor_unique hcrit hr hn q hq hclique y hy hy0 hy1
      z hzT x hx x' hx' hxz hx'z
  have hpack := actual_open_neighborhood_uniform_packing W H 6 hrow hcommon
  have hT : T.card = 6 := fiveCliqueSixSet_card q hq y hy
  have hTZ : Disjoint T Z := by
    apply Finset.disjoint_left.mpr
    intro x hxT hxZ
    exact five_pair_clone_outside q y x hxZ hxT
  have hyZ : y ∉ Z := by
    intro hyZ
    exact five_pair_clone_outside q y y hyZ (Finset.mem_insert_self y (fiveCliqueSet q))
  have hW : W.card = Z.card + 1 := Finset.card_insert_of_notMem hyZ
  have hU : (T ∪ Z).card = 6 + Z.card := by rw [Finset.card_union_of_disjoint hTZ, hT]
  have hH := Finset.card_add_card_compl (T ∪ Z)
  change (T ∪ Z).card + H.card = Fintype.card V at hH
  rw [hW] at hpack
  rw [hU] at hH
  change 12 + 7 * Z.card ≤ Fintype.card V
  omega

end TaskH.Six

#print axioms TaskH.Six.five_clique_hook_pair_exact
#print axioms TaskH.Six.five_pair_anchor_neighbors_exact
#print axioms TaskH.Six.five_pair_family_neighbors_exact
#print axioms TaskH.Six.five_pair_clone_packing
