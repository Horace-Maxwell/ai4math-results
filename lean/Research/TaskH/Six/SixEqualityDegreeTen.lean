import Research.TaskH.Six.SixDegreeNineExclusion
import Research.TaskH.Six.TraceSixGraphBound

/-! Original equality hypotheses internally produce the actual degree-ten branch. -/

set_option autoImplicit false

universe u

namespace TaskH.Six

open SimpleGraph Challenge

variable {V : Type u} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem equality_exists_degree_ten (hcrit : IsCriticalPlus 6 G)
    (hc : modCycleCount 6 G = 420) (hnot : ¬ IsCompleteOfOrder G 7) :
    ∃ v : V, G.degree v = 10 := by
  classical
  have hr : RainbowSixCycles G := equality_rainbowSixCycles hcrit hc
  have hb := equality_noncomplete_bounds hcrit hc hnot
  have hmin := equality_degree_ge_ten hcrit hc hnot
  let : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  by_contra hne
  have h11 : ∀ x : V, 11 ≤ G.degree x := by
    intro x
    have hd := hmin x
    have hnx : G.degree x ≠ 10 := fun he => hne ⟨x, he⟩
    omega
  have hfree := degree_eleven_cliqueFree_four hcrit hr hb.1 hb.2.1 h11
  have hlarge := trace_mod_six_cycle_count_lower hfree hb.2.1 h11
    (fun x => (hb.2.2 x).2.1)
  rw [hc] at hlarge
  omega

theorem equality_degree_ten_card_le_thirty_six (hcrit : IsCriticalPlus 6 G)
    (hc : modCycleCount 6 G = 420) (hnot : ¬ IsCompleteOfOrder G 7)
    (v : V) (hv : G.degree v = 10) : Fintype.card V ≤ 36 := by
  have hs : ShortSixCycles G := equality_shortSixCycles hcrit hc
  have hr : RainbowSixCycles G := equality_rainbowSixCycles hcrit hc
  have hn8 := (equality_noncomplete_bounds hcrit hc hnot).1
  have h120 : 120 ≤ cycleDegree G v := by
    have hh := critical_singleton_cycle_bound hcrit hs v
    rw [← cycleDegree_eq_ncard, hv] at hh
    norm_num at hh
    exact hh
  have hinc := critical_cycleDegree_root_incidence hcrit hs hr hn8 hc v 120 h120
  exact degree_ten_card_le_thirty_six (Fintype.card V) (by omega) hinc

theorem equality_degree_ten_cliqueFree_four (hcrit : IsCriticalPlus 6 G)
    (hc : modCycleCount 6 G = 420) (hnot : ¬ IsCompleteOfOrder G 7)
    (v : V) (hv : G.degree v = 10) : G.CliqueFree 4 := by
  have hr : RainbowSixCycles G := equality_rainbowSixCycles hcrit hc
  have hn8 := (equality_noncomplete_bounds hcrit hc hnot).1
  have hn36 := equality_degree_ten_card_le_thirty_six hcrit hc hnot v hv
  exact degree_ten_cliqueFree_four hcrit hr hn8 hn36 (equality_degree_ge_ten hcrit hc hnot)

end TaskH.Six

#print axioms TaskH.Six.equality_exists_degree_ten
#print axioms TaskH.Six.equality_degree_ten_card_le_thirty_six
#print axioms TaskH.Six.equality_degree_ten_cliqueFree_four
