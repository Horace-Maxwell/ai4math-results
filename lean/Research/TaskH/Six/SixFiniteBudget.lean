import Mathlib

/-!
Finite arithmetic bounds for the six-cycle proof. These are conditional
arithmetic helpers only. Actual graph transports must supply every numerical
premise from the original equality-case hypotheses before any use in CaseSix.
-/

set_option autoImplicit false

namespace TaskH.Six

theorem degree_le_seventeen_of_avoiding_budget (d c : ℕ)
    (hc : 61 ≤ c) (hbudget : 60 * d ≤ 3 * (420 - c)) : d ≤ 17 := by
  omega

theorem cycle_degree_ge_sixty_eight (d c : ℕ)
    (hc : 61 ≤ c) (hd : d ≤ 17)
    (hbudget : 2 * c ≤ d * (c - 60)) : 68 ≤ c := by
  have hm := Nat.mul_le_mul_right (c - 60) hd
  omega

theorem card_le_thirty_seven_of_incidence (n : ℕ)
    (hbudget : 68 * n ≤ 2520) : n ≤ 37 := by
  omega

theorem degree_seven_incompatible (c : ℕ)
    (hsingle : 300 ≤ c) (havoid : 420 ≤ 3 * (420 - c)) : False := by
  omega

theorem six_point_sparse_incidence_incompatible (n : ℕ)
    (hn : 7 ≤ n) (hbudget : 2514 + n ≤ 2520) : False := by
  omega

theorem clone_count_le_three (n r : ℕ)
    (hn : n ≤ 37) (hbudget : 12 + 7 * r ≤ n) : r ≤ 3 := by
  omega

theorem six_point_clone_incidence_incompatible (n r : ℕ)
    (hr : r ≤ 3) (hbudget : 2874 + n ≤ 2520 + 60 * r) : False := by
  omega

theorem five_group_closed_neighborhood_incompatible (n : ℕ)
    (hn : n ≤ 37) (hpack : 45 ≤ n) : False := by
  omega

theorem high_degree_four_clique_packing_incompatible (r p : ℕ)
    (hpack : 7 * r + 10 * p ≤ 33) (hlabels : p = 4 ∨ 8 ≤ r) : False := by
  rcases hlabels with hp | hr <;> omega

theorem degree_nine_four_clique_packing_rigid (r p : ℕ)
    (hpack : 5 * r + 8 * p ≤ 31) (hlabels : p = 4 ∨ 6 ≤ r) :
    r = 6 ∧ p = 0 := by
  rcases hlabels with hp | hr <;> omega

theorem degree_ten_four_clique_packing_incompatible (r p : ℕ)
    (hpack : 6 * r + 9 * p ≤ 32) (hlabels : p = 4 ∨ 7 ≤ r) : False := by
  rcases hlabels with hp | hr <;> omega

theorem degree_nine_card_le_thirty_five (n : ℕ)
    (hn : 1 ≤ n) (hbudget : 180 + 68 * (n - 1) ≤ 2520) : n ≤ 35 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show n ≠ 0 by omega)
  omega

theorem degree_ten_card_le_thirty_six (n : ℕ)
    (hn : 1 ≤ n) (hbudget : 120 + 68 * (n - 1) ≤ 2520) : n ≤ 36 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show n ≠ 0 by omega)
  omega

theorem complete_bipartite_six_cycle_budget_incompatible
    (hbudget : 480 ≤ 420) : False := by
  omega

theorem degree_ten_clone_count_le_three (n r : ℕ)
    (hn : n ≤ 36) (hpack : 9 * r + 2 ≤ n) : r ≤ 3 := by
  omega

theorem degree_ten_split_packing_incompatible (n : ℕ)
    (hn : n ≤ 36) (hpack : 64 ≤ n + 1) : False := by
  omega

theorem degree_ten_common_packing_incompatible (n : ℕ)
    (hn : n ≤ 36) (hpack : 45 ≤ n) : False := by
  omega

end TaskH.Six

#print axioms TaskH.Six.degree_le_seventeen_of_avoiding_budget
#print axioms TaskH.Six.cycle_degree_ge_sixty_eight
#print axioms TaskH.Six.card_le_thirty_seven_of_incidence
#print axioms TaskH.Six.degree_seven_incompatible
#print axioms TaskH.Six.six_point_sparse_incidence_incompatible
#print axioms TaskH.Six.clone_count_le_three
#print axioms TaskH.Six.six_point_clone_incidence_incompatible
#print axioms TaskH.Six.five_group_closed_neighborhood_incompatible
#print axioms TaskH.Six.high_degree_four_clique_packing_incompatible
#print axioms TaskH.Six.degree_nine_four_clique_packing_rigid
#print axioms TaskH.Six.degree_ten_four_clique_packing_incompatible
#print axioms TaskH.Six.degree_nine_card_le_thirty_five
#print axioms TaskH.Six.degree_ten_card_le_thirty_six
#print axioms TaskH.Six.complete_bipartite_six_cycle_budget_incompatible
#print axioms TaskH.Six.degree_ten_clone_count_le_three
#print axioms TaskH.Six.degree_ten_split_packing_incompatible
#print axioms TaskH.Six.degree_ten_common_packing_incompatible
