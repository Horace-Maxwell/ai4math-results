import Research.TaskH.Seven.SevenPairInsertion

/-! The original degree-eleven branch is impossible. Its three singleton
centers and actual two-point fibers are derived, then first-step and insertion
are applied in one fixed deleted-root coloring. -/

set_option autoImplicit false
universe u
namespace TaskH.Seven
open SimpleGraph _root_.TaskH.Challenge
open scoped Classical
variable {V : Type u} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem critical_three_singleton_two_pairs_false
    (hcrit : IsCriticalPlus 7 G) (hs : ShortSevenCycles G) (hr : RainbowSevenCycles G)
    (hfree : G.CliqueFree 5) (v : V)
    (c : (G.induce {x | x ≠ v}).Coloring (Fin 7))
    (hS : (singletonNeighborColors v c).card = 3)
    (eta gamma : Fin 7) (heg : eta ≠ gamma)
    (heta : eta ∉ singletonNeighborColors v c) (hgamma : gamma ∉ singletonNeighborColors v c)
    (hEta : (neighborColorFiber v c eta).card = 2)
    (hGamma : (neighborColorFiber v c gamma).card = 2) : False := by
  classical
  let S := singletonNeighborColors v c
  let e : Fin 3 ≃ ↥S := (Finset.equivFinOfCardEq hS).symm
  let qN : Fin 3 → G.neighborSet v := fun i => singletonNeighbor v c (e i)
  let Q : Fin 3 → V := fun i => (qN i).val
  have hQ : Function.Injective Q := (singletonNeighbor_val_injective v c).comp e.injective
  have hroot : ∀ i, G.Adj v (Q i) := fun i => (qN i).property
  have hQQ : ∀ i j, i ≠ j → G.Adj (Q i) (Q j) := by
    intro i j hij
    exact singleton_neighbors_adj hcrit hs hr v c (by omega) (e i) (e j) (e.injective.ne hij)
  have hQc : ∀ i, neighborColor v c (qN i) = (e i).val := fun i =>
    singletonNeighbor_color v c (e i)
  obtain ⟨x, y, hxy, hpair⟩ := Finset.card_eq_two.mp hEta
  obtain ⟨z0, z1, _hz01, hzpair⟩ := Finset.card_eq_two.mp hGamma
  have hx : neighborColor v c x = eta := by
    apply (mem_neighborColorFiber v c eta x).mp
    rw [hpair]
    exact Finset.mem_insert_self _ _
  have hy : neighborColor v c y = eta := by
    apply (mem_neighborColorFiber v c eta y).mp
    rw [hpair]
    exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  have hz0 : neighborColor v c z0 = gamma := by
    apply (mem_neighborColorFiber v c gamma z0).mp
    rw [hzpair]
    exact Finset.mem_insert_self _ _
  have hz1 : neighborColor v c z1 = gamma := by
    apply (mem_neighborColorFiber v c gamma z1).mp
    rw [hzpair]
    exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  have hout : ∀ (z : G.neighborSet v) (tau : Fin 7), neighborColor v c z = tau →
      tau ∉ S → ∀ i, z.val ≠ Q i := by
    intro z tau hz htau i he
    have hsub : z = qN i := Subtype.ext he
    have hc : tau = (e i).val := hz.symm.trans
      ((congrArg (neighborColor v c) hsub).trans (hQc i))
    exact htau (hc.symm ▸ (e i).property)
  have hcover : ∀ (tau : Fin 7), tau ∉ S → ∀ (a b : G.neighborSet v),
      neighborColorFiber v c tau = {a, b} →
      centerLabels G Q a.val ∪ centerLabels G Q b.val = Finset.univ := by
    intro tau htau a b hab
    have hlabels (z : V) : centerLabels G Q z =
        (Finset.univ : Finset (Fin 3)).filter (fun i => G.Adj z (Q i)) :=
      Finset.filter_congr_decidable _ _ _
    rw [hlabels a.val, hlabels b.val]
    ext i
    constructor
    · intro _hi
      exact Finset.mem_univ i
    · intro _hi
      obtain ⟨z, hzc, hzadj⟩ := singleton_meets_nonsingleton_color hcrit hs hr v c
        (by omega) (e i) tau htau
      have hm := (mem_neighborColorFiber v c tau z).mpr hzc
      rw [hab] at hm
      rcases Finset.mem_insert.mp hm with hza | hzb
      · subst z
        exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hzadj⟩)
      · have hzb' : z = b := Finset.mem_singleton.mp hzb
        subst z
        exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hzadj⟩)
  have hcoverEta := hcover eta heta x y hpair
  have hcoverGamma := hcover gamma hgamma z0 z1 hzpair
  have hA := cliqueFree_five_center_label_proper hfree v x.val Q hQ x.property hroot
    (hout x eta hx heta) hQQ
  have hB := cliqueFree_five_center_label_proper hfree v y.val Q hQ y.property hroot
    (hout y eta hy heta) hQQ
  have hZ : 2 ≤ (centerLabels G Q z0.val).card ∨
      2 ≤ (centerLabels G Q z1.val).card := by
    have hh := Finset.card_union_le (centerLabels G Q z0.val) (centerLabels G Q z1.val)
    rw [hcoverGamma, Finset.card_univ, Fintype.card_fin] at hh
    omega
  have hins : ∀ (z : G.neighborSet v), neighborColor v c z = gamma →
      2 ≤ (centerLabels G Q z.val).card → False := by
    intro z hz hZ'
    have hxz : x.val ≠ z.val := by
      intro he
      have he' : x = z := Subtype.ext he
      exact heg (hx.symm.trans ((congrArg (neighborColor v c) he').trans hz))
    have hyz : y.val ≠ z.val := by
      intro he
      have he' : y = z := Subtype.ext he
      exact heg (hy.symm.trans ((congrArg (neighborColor v c) he').trans hz))
    exact center_pair_insertion_false hr v c Q hQ hQQ hroot x y z hxy hxz hyz
      (hout x eta hx heta) (hout y eta hy heta) (hout z gamma hz hgamma)
      (hx.trans hy.symm) hcoverEta hA hB hZ'
  exact hZ.elim (hins z0 hz0) (hins z1 hz1)

theorem critical_degree_eleven_false
    (hcrit : IsCriticalPlus 7 G) (hs : ShortSevenCycles G) (hr : RainbowSevenCycles G)
    (hfree : G.CliqueFree 5) (v : V) (hv : G.degree v = 11) : False := by
  obtain ⟨c⟩ := critical_colorable_deletedVertex hcrit v
  obtain ⟨hS, _hpoint⟩ := degree_eleven_fiber_pattern hcrit hs hr hfree v c hv
  obtain ⟨eta, gamma, heg, heta, hgamma, hEta, hGamma⟩ :=
    degree_eleven_two_pair_colors hcrit hs hr hfree v c hv
  exact critical_three_singleton_two_pairs_false hcrit hs hr hfree v c hS
    eta gamma heg heta hgamma hEta hGamma

theorem equality_noncomplete_degree_ge_twelve
    (hcrit : IsCriticalPlus 7 G) (hc : modCycleCount 7 G = 2880)
    (hnot : ¬ IsCompleteOfOrder G 8) (v : V) : 12 ≤ G.degree v := by
  have h11 := equality_noncomplete_degree_ge_eleven hcrit hc hnot v
  by_contra hlt
  have hv : G.degree v = 11 := by omega
  exact critical_degree_eleven_false hcrit (equality_shortSevenCycles hcrit hc)
    (equality_rainbowSevenCycles hcrit hc) (equality_cliqueFree_five hcrit hc hnot) v hv

end TaskH.Seven
#print axioms TaskH.Seven.critical_three_singleton_two_pairs_false
#print axioms TaskH.Seven.critical_degree_eleven_false
#print axioms TaskH.Seven.equality_noncomplete_degree_ge_twelve
