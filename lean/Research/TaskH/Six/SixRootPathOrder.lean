import Research.TaskH.Six.SixRootPathClosing

/-!
The root-path surplus is impossible in the actual critical equality graph.
This derives the degree-sum and lower-order bounds used when choosing extra
deleted vertices in later clique arguments.
-/

set_option autoImplicit false

universe u

namespace TaskH.Six

open SimpleGraph _root_.TaskH.Challenge

variable {V : Type u} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem root_path_degree_sum_le_card_add_three (δ : ℕ) (hδ : 8 ≤ δ)
    (hmin : ∀ x : V, δ ≤ G.degree x) (hcycle : ∀ x : V, cycleDegree G x ≤ 420)
    (v : V) : G.degree v + δ ≤ Fintype.card V + 3 := by
  by_contra hbad
  have hsum : Fintype.card V + 4 ≤ G.degree v + δ := by omega
  have hlo := rootFourPaths_card_ge δ hmin v
  have hhi := rootFourPaths_card_le_two_cycleDegree δ hmin v hsum
  have hd : 8 ≤ G.degree v := hδ.trans (hmin v)
  have h1 : 7 ≤ δ - 1 := by omega
  have h2 : 6 ≤ δ - 2 := by omega
  have h3 : 5 ≤ δ - 3 := by omega
  have hprod : 1680 ≤ G.degree v * (δ - 1) * (δ - 2) * (δ - 3) := by
    exact Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul hd h1) h2) h3
  have hc := hcycle v
  omega

theorem critical_degree_sum_le_card_add_three (hcrit : IsCriticalPlus 6 G)
    (hs : ShortSixCycles G) (hr : RainbowSixCycles G)
    (hc : modCycleCount 6 G = 420) (hnot : ¬ IsCompleteOfOrder G 7) :
    G.minDegree + G.maxDegree ≤ Fintype.card V + 3 := by
  classical
  have hb := critical_noncomplete_bounds hcrit hs hr hc hnot
  let : Nonempty V := Fintype.card_pos_iff.mp (by have hn := hb.1; omega)
  have hmin : ∀ x : V, 8 ≤ G.degree x := fun x => (hb.2.2 x).1
  have hδ : 8 ≤ G.minDegree := G.le_minDegree_of_forall_le_degree 8 hmin
  obtain ⟨v, hv⟩ := G.exists_maximal_degree_vertex
  have hh := root_path_degree_sum_le_card_add_three G.minDegree hδ
    (fun x => G.minDegree_le_degree x)
    (fun x => (critical_cycleDegree_and_degree_bounds hcrit hs hr hb.1 hc x).2.2) v
  rw [← hv] at hh
  omega

theorem critical_card_ge_thirteen (hcrit : IsCriticalPlus 6 G)
    (hs : ShortSixCycles G) (hr : RainbowSixCycles G)
    (hc : modCycleCount 6 G = 420) (hnot : ¬ IsCompleteOfOrder G 7) :
    13 ≤ Fintype.card V := by
  classical
  have hb := critical_noncomplete_bounds hcrit hs hr hc hnot
  let : Nonempty V := Fintype.card_pos_iff.mp (by have hn := hb.1; omega)
  have hδ : 8 ≤ G.minDegree :=
    G.le_minDegree_of_forall_le_degree 8 (fun x => (hb.2.2 x).1)
  have hmax := G.minDegree_le_maxDegree
  have hsum := critical_degree_sum_le_card_add_three hcrit hs hr hc hnot
  omega

theorem equality_degree_sum_le_card_add_three (hcrit : IsCriticalPlus 6 G)
    (hc : modCycleCount 6 G = 420) (hnot : ¬ IsCompleteOfOrder G 7) :
    G.minDegree + G.maxDegree ≤ Fintype.card V + 3 :=
  critical_degree_sum_le_card_add_three hcrit (equality_shortSixCycles hcrit hc)
    (equality_rainbowSixCycles hcrit hc) hc hnot

theorem equality_card_ge_thirteen (hcrit : IsCriticalPlus 6 G)
    (hc : modCycleCount 6 G = 420) (hnot : ¬ IsCompleteOfOrder G 7) :
    13 ≤ Fintype.card V :=
  critical_card_ge_thirteen hcrit (equality_shortSixCycles hcrit hc)
    (equality_rainbowSixCycles hcrit hc) hc hnot

end TaskH.Six

#print axioms TaskH.Six.root_path_degree_sum_le_card_add_three
#print axioms TaskH.Six.critical_degree_sum_le_card_add_three
#print axioms TaskH.Six.critical_card_ge_thirteen
#print axioms TaskH.Six.equality_degree_sum_le_card_add_three
#print axioms TaskH.Six.equality_card_ge_thirteen
