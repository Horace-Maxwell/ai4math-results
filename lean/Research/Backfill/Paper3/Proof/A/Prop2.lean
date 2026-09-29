import Research.Backfill.Paper3.Proof.A.Lemma1

/-!
# Paper 3, Proposition 2

For `d ≥ 2` and a `d`-regular `G` on `n` vertices,
`N_{≤t*}(G) = 2^n - 1 - n - C(n,2) - n C(d,2) + 2T(G) - Q(G)`, `t* = dn/2 - 3d + 1`.
By Lemma 1, `2^n - N_{≤t*}` counts the sets `S` with `∂(S) ≤ 3d - 2`: all sets of size `≤ 2`, the
3-sets with at least two edges (counted through cherries: `∑_{|S|=3} #apexes(S) = n C(d,2)`), the
sets counted by `Q`, and no set of size `≥ 6`.
-/

set_option autoImplicit false

namespace P3A

open Finset SimpleGraph BackfillPaper3.Challenge

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The number of apexes of `S`: vertices of `S` adjacent to all other vertices of `S`. -/
def apexCount (S : Finset V) : ℕ :=
  #(S.filter (fun v => ∀ w ∈ S, w ≠ v → G.Adj v w))

theorem apexCount_triple {a b c : V} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    apexCount G {a, b, c} = (if 2 ≤ edgesIn G {a, b, c} then 1 else 0) +
      2 * (if 3 ≤ edgesIn G {a, b, c} then 1 else 0) := by
  rw [edgesIn_triple G hab hac hbc]
  unfold apexCount
  rw [card_filter, sum_insert (by simp [hab, hac]), sum_pair hbc]
  simp only [mem_insert, mem_singleton, forall_eq_or_imp, forall_eq, ne_eq, not_true_eq_false,
    IsEmpty.forall_iff, true_and, and_true, hab, hac, hbc, Ne.symm hab, Ne.symm hac, Ne.symm hbc,
    not_false_eq_true, forall_const, G.adj_comm b a, G.adj_comm c a, G.adj_comm c b]
  by_cases h1 : G.Adj a b <;> by_cases h2 : G.Adj a c <;> by_cases h3 : G.Adj b c <;>
    simp [h1, h2, h3]

/-- Cherries: `∑_{|S| = 3} #apexes(S) = n C(d, 2)`. -/
theorem sum_apexCount {d : ℕ} (hG : G.IsRegularOfDegree d) :
    ∑ S ∈ (univ : Finset (Finset V)).filter (fun S => #S = 3), apexCount G S =
      Fintype.card V * d.choose 2 := by
  have key := sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
    (fun (S : Finset V) (v : V) => v ∈ S ∧ ∀ w ∈ S, w ≠ v → G.Adj v w)
    (s := (univ : Finset (Finset V)).filter (fun S => #S = 3)) (t := (univ : Finset V))
  simp only [bipartiteAbove, bipartiteBelow] at key
  have h1 : ∀ S ∈ (univ : Finset (Finset V)).filter (fun S => #S = 3),
      #((univ : Finset V).filter (fun v => v ∈ S ∧ ∀ w ∈ S, w ≠ v → G.Adj v w)) =
        apexCount G S := by
    intro S _
    unfold apexCount
    congr 1
    ext v
    simp
  have h2 : ∀ v ∈ (univ : Finset V),
      #(((univ : Finset (Finset V)).filter (fun S => #S = 3)).filter
        (fun S => v ∈ S ∧ ∀ w ∈ S, w ≠ v → G.Adj v w)) = d.choose 2 := by
    intro v _
    rw [← hG.degree_eq v, ← card_neighborFinset_eq_degree, ← card_powersetCard]
    refine card_bij' (fun S _ => S.erase v) (fun P _ => insert v P) ?_ ?_ ?_ ?_
    · intro S hS
      simp only [mem_filter, mem_univ, true_and] at hS
      obtain ⟨hS3, hvS, hadj⟩ := hS
      rw [mem_powersetCard]
      refine ⟨fun w hw => ?_, by rw [card_erase_of_mem hvS, hS3]⟩
      rw [mem_erase] at hw
      rw [mem_neighborFinset]
      exact hadj w hw.2 hw.1
    · intro P hP
      rw [mem_powersetCard] at hP
      have hvP : v ∉ P := fun h => by simpa using hP.1 h
      simp only [mem_filter, mem_univ, true_and]
      refine ⟨by rw [card_insert_of_notMem hvP, hP.2], mem_insert_self v P, fun w hw hwv => ?_⟩
      rw [mem_insert] at hw
      rcases hw with rfl | hw
      · exact absurd rfl hwv
      · simpa using hP.1 hw
    · intro S hS
      simp only [mem_filter, mem_univ, true_and] at hS
      exact insert_erase hS.2.1
    · intro P hP
      rw [mem_powersetCard] at hP
      have hvP : v ∉ P := fun h => by simpa using hP.1 h
      exact erase_insert hvP
  rw [sum_congr rfl h1, sum_congr rfl h2, sum_const, card_univ, smul_eq_mul] at key
  exact key

/-- `T(G)` is the number of 3-sets spanning three edges. -/
theorem triangles_eq_card_filter :
    triangles G = #((univ : Finset (Finset V)).filter (fun S => #S = 3 ∧ 3 ≤ edgesIn G S)) := by
  unfold triangles cliqueFinset
  congr 1
  apply filter_congr
  intro S _
  rw [isNClique_iff, isClique_iff_choose_le]
  constructor
  · rintro ⟨h, h3⟩
    rw [h3] at h
    exact ⟨h3, by simpa using h⟩
  · rintro ⟨h3, h⟩
    rw [h3]
    exact ⟨by simpa using h, rfl⟩

/-- The 3-sets with at least two edges: `n C(d,2) - 2 T(G)` of them. -/
theorem card_three_sets_add {d : ℕ} (hG : G.IsRegularOfDegree d) :
    #((univ : Finset (Finset V)).filter (fun S => #S = 3 ∧ 2 ≤ edgesIn G S)) + 2 * triangles G =
      Fintype.card V * d.choose 2 := by
  rw [← sum_apexCount G hG, triangles_eq_card_filter]
  have h1 : ∀ S ∈ (univ : Finset (Finset V)).filter (fun S => #S = 3),
      apexCount G S = (if 2 ≤ edgesIn G S then 1 else 0) + 2 * (if 3 ≤ edgesIn G S then 1 else 0) := by
    intro S hS
    obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := card_eq_three.1 (mem_filter.1 hS).2
    exact apexCount_triple G hab hac hbc
  rw [sum_congr rfl h1, sum_add_distrib, ← mul_sum, ← card_filter, ← card_filter, filter_filter,
    filter_filter]

/-- `2^n - N_{≤t*}` counts the sets with `∂(S) ≤ 3d - 2`, split by size. -/
theorem card_boundary_le_three {d : ℕ} (hd : 2 ≤ d) (hG : G.IsRegularOfDegree d) :
    #((univ : Finset (Finset V)).filter (fun S => (boundary G S : ℤ) ≤ 3 * d - 2)) =
      1 + Fintype.card V + (Fintype.card V).choose 2 +
        #((univ : Finset (Finset V)).filter (fun S => #S = 3 ∧ 2 ≤ edgesIn G S)) +
          Qcount G d := by
  have hsplit : (univ : Finset (Finset V)).filter (fun S => (boundary G S : ℤ) ≤ 3 * d - 2) =
      ((((univ.filter (fun S => #S = 0) ∪ univ.filter (fun S => #S = 1)) ∪
        univ.filter (fun S => #S = 2)) ∪ univ.filter (fun S => #S = 3 ∧ 2 ≤ edgesIn G S)) ∪
          univ.filter (fun S => #S = 4 ∧ d + 2 ≤ edgesIn G S)) ∪
            univ.filter (fun S => #S = 5 ∧ 2 * d + 2 ≤ edgesIn G S) := by
    ext S
    simp only [mem_filter, mem_univ, true_and, mem_union]
    have hb := boundary_add_edgesIn G hG S
    rcases (show #S ≤ 2 ∨ #S = 3 ∨ #S = 4 ∨ #S = 5 ∨ 6 ≤ #S by omega) with h | h | h | h | h
    · have : d * #S ≤ d * 2 := Nat.mul_le_mul_left d h
      omega
    · rw [h] at hb
      omega
    · rw [h] at hb
      omega
    · rw [h] at hb
      omega
    · have he2 := two_mul_edgesIn_le G hG S
      have : 6 * d ≤ d * #S := by nlinarith
      omega
  unfold Qcount
  rw [hsplit]
  repeat rw [card_union_of_disjoint]
  · rw [card_filter_card_eq, card_filter_card_eq, card_filter_card_eq, Nat.choose_zero_right,
      Nat.choose_one_right]
    ring
  all_goals
    rw [Finset.disjoint_left]
    intro S h1 h2
    simp only [mem_union, mem_filter, mem_univ, true_and] at h1 h2
    omega

/-- **Proposition 2.** -/
theorem proposition2 : Proposition2 := by
  intro V _ _ G _ d hd hG
  have h1 := NleZ_eq_compl G (tStar (Fintype.card V) d)
  have hE := two_mul_card_edgeFinset G hG
  have hc : (#G.edgeFinset : ℤ) - tStar (Fintype.card V) d - 1 = 3 * d - 2 := by
    unfold tStar
    omega
  rw [hc, card_boundary_le_three G hd hG] at h1
  have h3 := card_three_sets_add G hG
  rw [h1]
  push_cast
  have h3' : (#((univ : Finset (Finset V)).filter (fun S => #S = 3 ∧ 2 ≤ edgesIn G S)) : ℤ) +
      2 * (triangles G : ℤ) = (Fintype.card V : ℤ) * (d.choose 2 : ℤ) := by
    exact_mod_cast h3
  linarith

end P3A
