import Research.TaskH.Six.SixFiveCliqueSets

set_option autoImplicit false

universe u

namespace TaskH.Six

open SimpleGraph _root_.TaskH.Challenge
open scoped Classical

variable {V : Type u} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem exists_five_pair_reindex (a b : Fin 5) (hab : a ≠ b) :
    ∃ ρ : Equiv.Perm (Fin 5), ρ 0 = a ∧ ρ 1 = b := by
  classical
  let τ : Equiv.Perm (Fin 5) := Equiv.swap a 0
  have hτa : τ a = 0 := by simp [τ]
  have hτb : τ b ≠ 0 := by
    intro he
    exact hab (τ.injective (hτa.trans he.symm))
  let π : Equiv.Perm (Fin 5) := τ.trans (Equiv.swap (τ b) 1)
  have hπa : π a = 0 := by
    change Equiv.swap (τ b) 1 (τ a) = 0
    rw [hτa]
    exact Equiv.swap_apply_of_ne_of_ne (Ne.symm hτb) (by decide)
  have hπb : π b = 1 := by
    change Equiv.swap (τ b) 1 (τ b) = 1
    exact Equiv.swap_apply_left _ _
  refine ⟨π.symm, ?_, ?_⟩
  · apply π.injective
    simpa only [Equiv.apply_symm_apply] using hπa.symm
  · apply π.injective
    simpa only [Equiv.apply_symm_apply] using hπb.symm

omit [Fintype V] in
/-- Arbitrary actual hook vertices are relabeled into the finite two-hook
certificate; the underlying original-vertex set and coloring are unchanged. -/
theorem actual_five_clique_pair_coloring_constraint
    (hr : RainbowSixCycles G) (w : V)
    (d : (G.induce {x | x ≠ w}).Coloring (Fin 6))
    (q : Fin 5 → V) (hq : Function.Injective q)
    (hclique : ∀ i j, i ≠ j → G.Adj (q i) (q j))
    (y : V) (hy : ∀ i, y ≠ q i)
    (a b : Fin 5) (hab : a ≠ b) (hya : G.Adj y (q a)) (hyb : G.Adj y (q b))
    (hqw : ∀ i, q i ≠ w) (hyw : y ≠ w)
    (z : V) (hzw : z ≠ w) (hzout : z ≠ y ∧ ∀ i, z ≠ q i) :
    (packingNeighborsIn G (fiveCliqueSixSet q y) z).card ≤ 1 ∨
      d ⟨z, hzw⟩ = d ⟨y, hyw⟩ ∧
        packingNeighborsIn G (fiveCliqueSixSet q y) z ⊆ {q a, q b} := by
  classical
  obtain ⟨ρ, hρ0, hρ1⟩ := exists_five_pair_reindex a b hab
  let p := q ∘ ρ
  let e := fiveCliqueWithPoint p y
  have hp : Function.Injective p := hq.comp ρ.injective
  have hyp : ∀ i, y ≠ p i := fun i => hy (ρ i)
  have hpclique : ∀ i j, i ≠ j → G.Adj (p i) (p j) := by
    intro i j hij
    exact hclique (ρ i) (ρ j) (ρ.injective.ne hij)
  have hy0 : G.Adj y (p 0) := by simpa only [p, Function.comp_apply, hρ0] using hya
  have hy1 : G.Adj y (p 1) := by simpa only [p, Function.comp_apply, hρ1] using hyb
  have he : Function.Injective e := fiveCliqueWithPoint_injective p y hp hyp
  have hcan := actual_five_clique_two_attachment_coloring_constraints hr w d p hp hpclique
    y hyp hy0 hy1 (fun i => hqw (ρ i)) hyw z hzw ⟨hzout.1, fun i => hzout.2 (ρ i)⟩
  have hset : fiveCliqueSixSet q y = Finset.univ.image e := by
    rw [← fiveCliqueSixSet_reindex q ρ y, fiveCliqueSixSet_eq_image]
  have hcard : (packingNeighborsIn G (fiveCliqueSixSet q y) z).card =
      (fiveCliqueTwoNeighborIndices G e z).card := by
    rw [hset, fiveCliqueTwoNeighbors_card e he z]
  rcases hcan with hsmall | ⟨hcolor, hsub⟩
  · exact Or.inl (by rw [hcard]; exact hsmall)
  · refine Or.inr ⟨hcolor, ?_⟩
    intro x hx
    rw [hset, fiveCliqueTwoNeighbors_image] at hx
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
    rcases Finset.mem_insert.mp (hsub hi) with hi | hi
    · subst i
      exact Finset.mem_insert.mpr (Or.inl (congrArg q hρ0))
    · have hi0 : i = 1 := Finset.mem_singleton.mp hi
      subst i
      exact Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr (congrArg q hρ1)))

omit [Fintype V] in
theorem five_clique_three_hooks_outside_small_coloring
    (hr : RainbowSixCycles G) (w : V)
    (d : (G.induce {x | x ≠ w}).Coloring (Fin 6))
    (q : Fin 5 → V) (hq : Function.Injective q)
    (hclique : ∀ i j, i ≠ j → G.Adj (q i) (q j))
    (y : V) (hy : ∀ i, y ≠ q i)
    (a b c : Fin 5) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hya : G.Adj y (q a)) (hyb : G.Adj y (q b)) (hyc : G.Adj y (q c))
    (hqw : ∀ i, q i ≠ w) (hyw : y ≠ w)
    (z : V) (hzw : z ≠ w) (hzout : z ≠ y ∧ ∀ i, z ≠ q i) :
    (packingNeighborsIn G (fiveCliqueSixSet q y) z).card ≤ 1 := by
  classical
  let N := packingNeighborsIn G (fiveCliqueSixSet q y) z
  by_contra hlarge
  have hab' := actual_five_clique_pair_coloring_constraint hr w d q hq hclique
    y hy a b hab hya hyb hqw hyw z hzw hzout
  have hac' := actual_five_clique_pair_coloring_constraint hr w d q hq hclique
    y hy a c hac hya hyc hqw hyw z hzw hzout
  have hsubab : N ⊆ {q a, q b} := (hab'.resolve_left hlarge).2
  have hsubac : N ⊆ {q a, q c} := (hac'.resolve_left hlarge).2
  have hsub : N ⊆ {q a} := by
    intro x hx
    have hxab := hsubab hx
    have hxac := hsubac hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hxab hxac
    apply Finset.mem_singleton.mpr
    rcases hxab with hxa | hxb
    · exact hxa
    · rcases hxac with hxa | hxc
      · exact hxa
      · exact (hbc (hq (hxb.symm.trans hxc))).elim
  have hh := Finset.card_le_card hsub
  simp only [Finset.card_singleton] at hh
  exact hlarge hh

/-- Criticality chooses an actual deleted vertex outside the configuration
and the outside point. No coloring-extension premise is added. -/
theorem critical_five_clique_three_hooks_outside_small
    (hcrit : IsCriticalPlus 6 G) (hr : RainbowSixCycles G)
    (hn : 8 ≤ Fintype.card V)
    (q : Fin 5 → V) (hq : Function.Injective q)
    (hclique : ∀ i j, i ≠ j → G.Adj (q i) (q j))
    (y : V) (hy : ∀ i, y ≠ q i)
    (a b c : Fin 5) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hya : G.Adj y (q a)) (hyb : G.Adj y (q b)) (hyc : G.Adj y (q c))
    (z : V) (hzout : z ∉ fiveCliqueSixSet q y) :
    (packingNeighborsIn G (fiveCliqueSixSet q y) z).card ≤ 1 := by
  classical
  let T := fiveCliqueSixSet q y
  let S := insert z T
  have hT : T.card = 6 := fiveCliqueSixSet_card q hq y hy
  have hS : S.card ≤ 7 := by
    have hh := Finset.card_insert_le z T
    change (insert z T).card ≤ 7
    omega
  have hlt : S.card < (Finset.univ : Finset V).card := by
    rw [Finset.card_univ]
    omega
  obtain ⟨w, _hw, hwout⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
  have hyT : y ∈ T := Finset.mem_insert_self _ _
  have hqiT : ∀ i, q i ∈ T := by
    intro i
    exact Finset.mem_insert_of_mem ((mem_fiveCliqueSet q _).mpr ⟨i, rfl⟩)
  have hzw : z ≠ w := fun he => hwout (he ▸ Finset.mem_insert_self z T)
  have hyw : y ≠ w := fun he => hwout (he ▸ Finset.mem_insert_of_mem hyT)
  have hqw : ∀ i, q i ≠ w := by
    intro i he
    exact hwout (he ▸ Finset.mem_insert_of_mem (hqiT i))
  have hz : z ≠ y ∧ ∀ i, z ≠ q i := by
    constructor
    · intro he
      exact hzout (he.symm ▸ hyT)
    · intro i he
      exact hzout (he.symm ▸ hqiT i)
  obtain ⟨d⟩ := TaskH.critical_colorable_deletedVertex hcrit w
  exact five_clique_three_hooks_outside_small_coloring hr w d q hq hclique y hy
    a b c hab hac hbc hya hyb hyc hqw hyw z hzw hz

end TaskH.Six

#print axioms TaskH.Six.exists_five_pair_reindex
#print axioms TaskH.Six.actual_five_clique_pair_coloring_constraint
#print axioms TaskH.Six.five_clique_three_hooks_outside_small_coloring
#print axioms TaskH.Six.critical_five_clique_three_hooks_outside_small
