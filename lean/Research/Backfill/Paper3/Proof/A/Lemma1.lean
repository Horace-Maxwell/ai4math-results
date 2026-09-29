import Research.Backfill.Paper3.Proof.A.Basic

/-!
# Paper 3, Lemma 1 (complement identity) and the high-threshold tie of §8

`∑_{v ∈ S} deg v = ∂(S) + e(S)` by double counting vertex–edge incidences, hence
`∂(S) + e(S) = d |S|` for `d`-regular graphs; `e(Sᶜ) + ∂(S) = |E|`, and the complement bijection
gives `N_{≤t} = 2^n - #{S : ∂(S) ≤ |E| - t - 1}`. For `d ≥ 3` and `t ≥ dn/2 - 2d` only sets of size
`≤ 2` can have `∂(S) ≤ |E| - t - 1`, and their number depends only on `n`, `d`, `|E|` and `t`.
-/

set_option autoImplicit false

namespace P3A

open Finset SimpleGraph BackfillPaper3.Challenge

section Lemma1

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- `∂(S)` is the number of edges meeting `S`. -/
theorem boundary_eq_card_filter (S : Finset V) :
    boundary G S = #(G.edgeFinset.filter (fun e => ∃ v ∈ S, v ∈ e)) := by
  unfold boundary
  congr 1
  ext e
  simp only [mem_biUnion, incidenceFinset_eq_filter, mem_filter]
  constructor
  · rintro ⟨v, hv, he, hve⟩
    exact ⟨he, v, hv, hve⟩
  · rintro ⟨he, v, hv, hve⟩
    exact ⟨v, hv, he, hve⟩

/-- Double counting of incidences: `∑_{v ∈ S} deg v = ∂(S) + e(S)`. -/
theorem sum_degree_eq_boundary_add_edgesIn (S : Finset V) :
    ∑ v ∈ S, G.degree v = boundary G S + edgesIn G S := by
  have h1 : ∑ v ∈ S, G.degree v = ∑ e ∈ G.edgeFinset, #(S.filter (· ∈ e)) := by
    have key := sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
      (fun (v : V) (e : Sym2 V) => v ∈ e) (s := S) (t := G.edgeFinset)
    simp only [bipartiteAbove, bipartiteBelow] at key
    rw [← key]
    refine sum_congr rfl fun v _ => ?_
    rw [← card_incidenceFinset_eq_degree, incidenceFinset_eq_filter]
  have h2 : ∀ e ∈ G.edgeFinset, #(S.filter (· ∈ e)) =
      (if ∃ v ∈ S, v ∈ e then 1 else 0) + (if e ∈ S.sym2 then 1 else 0) := by
    intro e he
    induction e using Sym2.ind with
    | h x y =>
      have hxy : x ≠ y := (show G.Adj x y by simpa using he).ne
      have hS : S.filter (· ∈ s(x, y)) = ({x, y} : Finset V).filter (· ∈ S) := by
        ext w
        simp only [mem_filter, Sym2.mem_iff, mem_insert, mem_singleton]
        tauto
      have hex : (∃ v ∈ S, v ∈ s(x, y)) ↔ (x ∈ S ∨ y ∈ S) := by
        constructor
        · rintro ⟨v, hv, hvxy⟩
          rcases Sym2.mem_iff.1 hvxy with rfl | rfl
          · exact Or.inl hv
          · exact Or.inr hv
        · rintro (hx | hy)
          · exact ⟨x, hx, Sym2.mem_mk_left x y⟩
          · exact ⟨y, hy, Sym2.mem_mk_right x y⟩
      rw [hS, card_filter_pair _ hxy]
      simp only [hex, Finset.mk_mem_sym2_iff]
      by_cases hx : x ∈ S <;> by_cases hy : y ∈ S <;> simp [hx, hy]
  rw [h1, sum_congr rfl h2, sum_add_distrib, ← card_filter, ← card_filter,
    boundary_eq_card_filter]
  rfl

/-- Lemma 1, first part: `∂(S) + e(S) = d |S|`. -/
theorem boundary_add_edgesIn {d : ℕ} (hG : G.IsRegularOfDegree d) (S : Finset V) :
    boundary G S + edgesIn G S = d * #S := by
  rw [← sum_degree_eq_boundary_add_edgesIn, sum_congr rfl fun v _ => hG.degree_eq v, sum_const,
    smul_eq_mul, mul_comm]

/-- The edges inside `Sᶜ` are the edges not meeting `S`. -/
theorem edgesIn_compl_add_boundary (S : Finset V) :
    edgesIn G Sᶜ + boundary G S = #G.edgeFinset := by
  have h : G.edgeFinset.filter (· ∈ Sᶜ.sym2) =
      G.edgeFinset.filter (fun e => ¬ ∃ v ∈ S, v ∈ e) := by
    apply filter_congr
    intro e _
    induction e using Sym2.ind with
    | h x y =>
      simp only [Finset.mk_mem_sym2_iff, mem_compl, Sym2.mem_iff, not_exists, not_and]
      constructor
      · rintro ⟨hx, hy⟩ z hz hzxy
        rcases hzxy with rfl | rfl
        · exact hx hz
        · exact hy hz
      · intro h
        exact ⟨fun hx => h x hx (Or.inl rfl), fun hy => h y hy (Or.inr rfl)⟩
  rw [edgesIn, h, boundary_eq_card_filter, add_comm]
  exact card_filter_add_card_filter_not _

omit [DecidableEq V] in
/-- In a `d`-regular graph, `2 |E| = d n`. -/
theorem two_mul_card_edgeFinset {d : ℕ} (hG : G.IsRegularOfDegree d) :
    2 * #G.edgeFinset = d * Fintype.card V := by
  rw [← sum_degrees_eq_twice_card_edges, sum_congr rfl fun v _ => hG.degree_eq v, sum_const,
    smul_eq_mul, card_univ, mul_comm]

/-- Lemma 1, second part (any graph): `N_{≤t} = 2^n - #{S : ∂(S) ≤ |E| - t - 1}`. -/
theorem NleZ_eq_compl (t : ℤ) : (NleZ G t : ℤ) = 2 ^ Fintype.card V -
    #((univ : Finset (Finset V)).filter
      (fun S => (boundary G S : ℤ) ≤ (#G.edgeFinset : ℤ) - t - 1)) := by
  have h1 : NleZ G t = #((univ : Finset (Finset V)).filter
      (fun S => ¬ (boundary G S : ℤ) ≤ (#G.edgeFinset : ℤ) - t - 1)) := by
    unfold NleZ
    apply card_bij (fun A _ => Aᶜ)
    · intro A hA
      simp only [mem_filter, mem_univ, true_and] at hA ⊢
      have := edgesIn_compl_add_boundary G Aᶜ
      rw [compl_compl] at this
      omega
    · intro A _ B _ h
      exact compl_injective h
    · intro B hB
      refine ⟨Bᶜ, ?_, compl_compl B⟩
      simp only [mem_filter, mem_univ, true_and] at hB ⊢
      have := edgesIn_compl_add_boundary G B
      omega
  have h2 := card_filter_add_card_filter_not (s := (univ : Finset (Finset V)))
    (fun S => (boundary G S : ℤ) ≤ (#G.edgeFinset : ℤ) - t - 1)
  rw [card_univ, Fintype.card_finset] at h2
  have h3 : ((2 ^ Fintype.card V : ℕ) : ℤ) = 2 ^ Fintype.card V := by push_cast; rfl
  rw [h1]
  omega

end Lemma1

section HighThreshold

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The 2-sets spanning an edge are in bijection with the edges. -/
theorem card_pairs_adj :
    #((univ : Finset (Finset V)).filter (fun S => #S = 2 ∧ 1 ≤ edgesIn G S)) =
      #G.edgeFinset := by
  have key := sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
    (fun (S : Finset V) (e : Sym2 V) => e ∈ S.sym2)
    (s := (univ : Finset (Finset V)).filter (fun S => #S = 2)) (t := G.edgeFinset)
  simp only [bipartiteAbove, bipartiteBelow] at key
  have h1 : ∀ S ∈ (univ : Finset (Finset V)).filter (fun S => #S = 2),
      #(G.edgeFinset.filter (fun e => e ∈ S.sym2)) = if 1 ≤ edgesIn G S then 1 else 0 := by
    intro S hS
    have hS2 : #S = 2 := (mem_filter.1 hS).2
    have := edgesIn_le_choose G S
    rw [hS2] at this
    norm_num at this
    change edgesIn G S = _
    split_ifs <;> omega
  have h2 : ∀ e ∈ G.edgeFinset,
      #(((univ : Finset (Finset V)).filter (fun S => #S = 2)).filter
        (fun S => e ∈ S.sym2)) = 1 := by
    intro e he
    induction e using Sym2.ind with
    | h x y =>
      have hxy : x ≠ y := (show G.Adj x y by simpa using he).ne
      rw [card_eq_one]
      refine ⟨{x, y}, ?_⟩
      ext S
      simp only [mem_filter, mem_univ, true_and, Finset.mk_mem_sym2_iff, mem_singleton]
      constructor
      · rintro ⟨hS, hx, hy⟩
        symm
        apply eq_of_subset_of_card_le
        · intro w hw
          rw [mem_insert, mem_singleton] at hw
          rcases hw with rfl | rfl
          · exact hx
          · exact hy
        · simp [hS, card_pair hxy]
      · rintro rfl
        exact ⟨card_pair hxy, by simp, by simp⟩
  rw [sum_congr rfl h1, sum_congr rfl h2, ← card_filter, filter_filter, sum_const, smul_eq_mul,
    mul_one] at key
  exact key

omit [DecidableEq V] in
theorem card_filter_card_and_const (k : ℕ) (p : Prop) [Decidable p] :
    #((univ : Finset (Finset V)).filter (fun S => #S = k ∧ p)) =
      if p then (Fintype.card V).choose k else 0 := by
  by_cases hp : p
  · simp only [hp, and_true, ite_true]
    exact card_filter_card_eq k
  · simp [hp]

/-- For `d ≥ 3` and `c ≤ 2d - 1`, the sets with `∂(S) ≤ c` are: `∅` (if `c ≥ 0`), the singletons
(if `c ≥ d`) and the 2-sets spanning an edge (if `c ≥ 2d - 1`). -/
theorem card_boundary_le_small {d : ℕ} (hd : 3 ≤ d) (hG : G.IsRegularOfDegree d) (c : ℤ)
    (hc : c ≤ 2 * d - 1) :
    #((univ : Finset (Finset V)).filter (fun S => (boundary G S : ℤ) ≤ c)) =
      (if 0 ≤ c then 1 else 0) + (if (d : ℤ) ≤ c then Fintype.card V else 0) +
        (if 2 * (d : ℤ) - 1 ≤ c then #G.edgeFinset else 0) := by
  have hsplit : (univ : Finset (Finset V)).filter (fun S => (boundary G S : ℤ) ≤ c) =
      ((univ.filter (fun S => #S = 0 ∧ 0 ≤ c)) ∪ (univ.filter (fun S => #S = 1 ∧ (d : ℤ) ≤ c))) ∪
        ((univ.filter (fun S => #S = 2 ∧ 1 ≤ edgesIn G S)).filter
          (fun _ => 2 * (d : ℤ) - 1 ≤ c)) := by
    ext S
    simp only [mem_filter, mem_univ, true_and, mem_union]
    have hb := boundary_add_edgesIn G hG S
    have he := edgesIn_le_choose G S
    have he2 := two_mul_edgesIn_le G hG S
    rcases (show #S = 0 ∨ #S = 1 ∨ #S = 2 ∨ #S = 3 ∨ 4 ≤ #S by omega) with h | h | h | h | h
    · rw [h] at hb
      omega
    · rw [h] at hb he
      norm_num at he
      omega
    · rw [h] at hb he
      norm_num at he
      omega
    · rw [h] at hb he
      norm_num at he
      omega
    · have h4 : 4 * d ≤ d * #S := by nlinarith
      omega
  rw [hsplit, card_union_of_disjoint, card_union_of_disjoint, card_filter_card_and_const,
    card_filter_card_and_const]
  · congr 1
    · simp
    · by_cases h : 2 * (d : ℤ) - 1 ≤ c
      · rw [filter_true_of_mem (fun _ _ => h), card_pairs_adj, ite_eq_left h]
      · rw [filter_false_of_mem (fun _ _ => h), card_empty, ite_eq_right h]
  · rw [Finset.disjoint_left]
    intro S h1 h2
    rw [mem_filter] at h1 h2
    omega
  · rw [Finset.disjoint_left]
    intro S h1 h2
    simp only [mem_union, mem_filter, mem_univ, true_and] at h1 h2
    omega

end HighThreshold

/-- **Lemma 1.** -/
theorem lemma1 : Lemma1 := by
  intro V _ _ G _ d hG
  exact ⟨boundary_add_edgesIn G hG, NleZ_eq_compl G⟩

/-- §8: for `d ≥ 3` all `d`-regular graphs on `n` vertices have the same `N_{≤t}` when
`t ≥ dn/2 - 2d`. -/
theorem highThresholdTie : HighThresholdTie := by
  intro d n hd t ht V W _ _ _ _ G H _ _ hV hW hG hH
  have EG := two_mul_card_edgeFinset G hG
  have EH := two_mul_card_edgeFinset H hH
  rw [hV] at EG
  rw [hW] at EH
  have hEE : #G.edgeFinset = #H.edgeFinset := by omega
  have eG := NleZ_eq_compl G t
  have eH := NleZ_eq_compl H t
  rw [card_boundary_le_small G hd hG _ (by omega)] at eG
  rw [card_boundary_le_small H hd hH _ (by omega)] at eH
  rw [hEE, hV] at eG
  rw [hW] at eH
  have : (NleZ G t : ℤ) = NleZ H t := by rw [eG, eH]
  exact_mod_cast this

end P3A
