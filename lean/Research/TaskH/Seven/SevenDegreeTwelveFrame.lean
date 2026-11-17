import Research.TaskH.Seven.SevenMinimumTwelve

/-! Every actual degree-twelve deleted coloring has exactly two singleton
neighbor colors and five two-point fibers. Three singletons are excluded by
the already written actual two-pair insertion transport. -/

set_option autoImplicit false
universe u
namespace TaskH.Seven
open SimpleGraph _root_.TaskH.Challenge
open scoped Classical
variable {V : Type u} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem seven_positive_sum_twelve_three_ones_pairs
    (n : Fin 7 → ℕ) (hpos : ∀ i, 0 < n i) (hsum : (∑ i : Fin 7, n i) = 12)
    (hones : ((Finset.univ : Finset (Fin 7)).filter (fun i => n i = 1)).card = 3) :
    2 ≤ ((Finset.univ : Finset (Fin 7)).filter (fun i => n i = 2)).card := by
  classical
  have hrow : ∀ i : Fin 7, 3 ≤ n i + 2 * (if n i = 1 then 1 else 0) +
      (if n i = 2 then 1 else 0) := by
    intro i
    have hp := hpos i
    split_ifs <;> omega
  have hh : 21 ≤ (∑ i : Fin 7, n i) +
      2 * ((Finset.univ : Finset (Fin 7)).filter (fun i => n i = 1)).card +
      ((Finset.univ : Finset (Fin 7)).filter (fun i => n i = 2)).card := by
    calc
      21 = ∑ _i : Fin 7, 3 := by norm_num
      _ ≤ ∑ i : Fin 7, (n i + 2 * (if n i = 1 then 1 else 0) +
          (if n i = 2 then 1 else 0)) := Finset.sum_le_sum (fun i _ => hrow i)
      _ = _ := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
          Finset.sum_boole, Finset.sum_boole]
        simp only [Nat.cast_id]
  rw [hsum, hones] at hh
  omega

theorem degree_twelve_three_singletons_false
    (hcrit : IsCriticalPlus 7 G) (hs : ShortSevenCycles G) (hr : RainbowSevenCycles G)
    (hfree : G.CliqueFree 5) (v : V)
    (c : (G.induce {x | x ≠ v}).Coloring (Fin 7)) (hv : G.degree v = 12)
    (hS : (singletonNeighborColors v c).card = 3) : False := by
  classical
  let n : Fin 7 → ℕ := fun i => (neighborColorFiber v c i).card
  have hpos : ∀ i, 0 < n i := by
    intro i
    obtain ⟨z, hz⟩ := critical_neighborColor_surjective hcrit v c i
    exact Finset.card_pos.mpr ⟨z, (mem_neighborColorFiber v c i z).mpr hz⟩
  have hsum : (∑ i : Fin 7, n i) = 12 := by
    have hh := sum_neighborColorFiber_card v c
    rw [G.card_neighborSet_eq_degree, hv] at hh
    exact hh
  have hones : ((Finset.univ : Finset (Fin 7)).filter (fun i => n i = 1)).card = 3 := hS
  have hpairs := seven_positive_sum_twelve_three_ones_pairs n hpos hsum hones
  let P := (Finset.univ : Finset (Fin 7)).filter (fun i => n i = 2)
  change 2 ≤ P.card at hpairs
  obtain ⟨eta, he, gamma, hg, heg⟩ := Finset.one_lt_card.mp (by omega : 1 < P.card)
  have heta2 : (neighborColorFiber v c eta).card = 2 := (Finset.mem_filter.mp he).2
  have hgamma2 : (neighborColorFiber v c gamma).card = 2 := (Finset.mem_filter.mp hg).2
  have heta : eta ∉ singletonNeighborColors v c := by
    intro hm
    have hh := (mem_singletonNeighborColors v c eta).mp hm
    omega
  have hgamma : gamma ∉ singletonNeighborColors v c := by
    intro hm
    have hh := (mem_singletonNeighborColors v c gamma).mp hm
    omega
  exact critical_three_singleton_two_pairs_false hcrit hs hr hfree v c hS eta gamma
    heg heta hgamma heta2 hgamma2

theorem degree_twelve_fiber_pattern
    (hcrit : IsCriticalPlus 7 G) (hs : ShortSevenCycles G) (hr : RainbowSevenCycles G)
    (hfree : G.CliqueFree 5) (v : V)
    (c : (G.induce {x | x ≠ v}).Coloring (Fin 7)) (hv : G.degree v = 12) :
    (singletonNeighborColors v c).card = 2 ∧
      ∀ i : Fin 7, (neighborColorFiber v c i).card =
        if i ∈ singletonNeighborColors v c then 1 else 2 := by
  classical
  let S := singletonNeighborColors v c
  have hlow := singletonNeighborColors_card_ge hcrit v c
  have hhigh := singleton_colors_card_lt_four_of_cliqueFree_five hcrit hs hr hfree v c
  have hS : S.card = 2 := by
    rw [hv] at hlow
    change 14 - 12 ≤ S.card at hlow
    change S.card < 4 at hhigh
    by_contra hnot
    have hthree : S.card = 3 := by omega
    exact degree_twelve_three_singletons_false hcrit hs hr hfree v c hv hthree
  have hpos : ∀ i : Fin 7, 0 < (neighborColorFiber v c i).card := by
    intro i
    obtain ⟨z, hz⟩ := critical_neighborColor_surjective hcrit v c i
    exact Finset.card_pos.mpr ⟨z, (mem_neighborColorFiber v c i z).mpr hz⟩
  have hstep : ∀ i ∈ (Finset.univ : Finset (Fin 7)),
      (if i ∈ S then 1 else 2 : ℕ) ≤ (neighborColorFiber v c i).card := by
    intro i _hi
    by_cases hi : i ∈ S
    · rw [ite_eq_left hi]
      exact ((mem_singletonNeighborColors v c i).mp hi).symm.le
    · rw [ite_eq_right hi]
      have hn : (neighborColorFiber v c i).card ≠ 1 := by
        intro he
        exact hi ((mem_singletonNeighborColors v c i).mpr he)
      have hp := hpos i
      omega
  have hsingle : (∑ i : Fin 7, if i ∈ S then 1 else 0 : ℕ) = S.card := by
    have he : (Finset.univ.filter (fun i : Fin 7 => i ∈ S)) = S := by ext i; simp
    calc
      _ = (Finset.univ.filter (fun i : Fin 7 => i ∈ S)).card := Finset.sum_boole _ _
      _ = _ := congrArg Finset.card he
  have htwo : ∀ i : Fin 7,
      (if i ∈ S then 1 else 2 : ℕ) + (if i ∈ S then 1 else 0 : ℕ) = 2 := by
    intro i
    split_ifs <;> rfl
  have hw : (∑ i : Fin 7, if i ∈ S then 1 else 2 : ℕ) = 12 := by
    have hh : (∑ i : Fin 7, if i ∈ S then 1 else 2 : ℕ) + S.card = 14 := by
      rw [← hsingle, ← Finset.sum_add_distrib]
      norm_num [htwo]
    omega
  have hsum := sum_neighborColorFiber_card v c
  rw [G.card_neighborSet_eq_degree, hv] at hsum
  have heq : (∑ i : Fin 7, if i ∈ S then 1 else 2 : ℕ) =
      ∑ i : Fin 7, (neighborColorFiber v c i).card := hw.trans hsum.symm
  have hpoint := (Finset.sum_eq_sum_iff_of_le hstep).mp heq
  refine ⟨hS, ?_⟩
  intro i
  exact (hpoint i (Finset.mem_univ i)).symm

theorem equality_degree_twelve_fiber_pattern
    (hcrit : IsCriticalPlus 7 G) (hc : modCycleCount 7 G = 2880)
    (hnot : ¬ IsCompleteOfOrder G 8) (v : V)
    (c : (G.induce {x | x ≠ v}).Coloring (Fin 7)) (hv : G.degree v = 12) :
    (singletonNeighborColors v c).card = 2 ∧
      ∀ i : Fin 7, (neighborColorFiber v c i).card =
        if i ∈ singletonNeighborColors v c then 1 else 2 :=
  degree_twelve_fiber_pattern hcrit (equality_shortSevenCycles hcrit hc)
    (equality_rainbowSevenCycles hcrit hc) (equality_cliqueFree_five hcrit hc hnot) v c hv


/-- Each actual singleton center touches a point in every other neighbor
color, including each of the five two-point fibers. -/
theorem equality_degree_twelve_singleton_meets_pair
    (hcrit : IsCriticalPlus 7 G) (hc : modCycleCount 7 G = 2880)
    (hnot : ¬ IsCompleteOfOrder G 8) (v : V)
    (c : (G.induce {x | x ≠ v}).Coloring (Fin 7)) (hv : G.degree v = 12)
    (j : ↥(singletonNeighborColors v c)) (eta : Fin 7)
    (heta : eta ∉ singletonNeighborColors v c) :
    ∃ z : G.neighborSet v, neighborColor v c z = eta ∧
      G.Adj z.val (singletonNeighbor v c j).val := by
  classical
  have hS := (equality_degree_twelve_fiber_pattern hcrit hc hnot v c hv).1
  obtain ⟨i, hi, hij⟩ := Finset.exists_mem_ne (by omega :
    1 < (singletonNeighborColors v c).card) j.val
  have hie : i ≠ eta := by
    intro he
    exact heta (he ▸ hi)
  have hej : eta ≠ j.val := by
    intro he
    exact heta (he.symm ▸ j.property)
  exact singleton_following_first_step hcrit (equality_shortSevenCycles hcrit hc)
    (equality_rainbowSevenCycles hcrit hc) v c ⟨i, hi⟩ j
    (fun he => hij (congrArg Subtype.val he)) eta hie hej

end TaskH.Seven
#print axioms TaskH.Seven.seven_positive_sum_twelve_three_ones_pairs
#print axioms TaskH.Seven.degree_twelve_three_singletons_false
#print axioms TaskH.Seven.degree_twelve_fiber_pattern
#print axioms TaskH.Seven.equality_degree_twelve_fiber_pattern

#print axioms TaskH.Seven.equality_degree_twelve_singleton_meets_pair
