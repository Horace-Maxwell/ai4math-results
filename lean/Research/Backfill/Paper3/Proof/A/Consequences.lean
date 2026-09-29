import Research.Backfill.Paper3.Proof.A.TheoremA

/-!
# Paper 3: consequences of Theorem A

The competitors (`(K_d □ K_2) ∪ (m-1) K_{d,d}` for `d ≥ 3`, `C_n` for `d = 2`), the negative
answer for every admissible pair except the trivial ones, the scope of `γ*`, the two numbered
negative instances, the trivial cases `d = 1` and `(n, d) = (4, 2)`, and connectivity of
`d`-regular graphs on `2d` vertices.
-/

set_option autoImplicit false

namespace P3A

open Finset SimpleGraph BackfillPaper3.Challenge Filter Topology

/-- `K_d □ K_2` is `d`-regular (`d ≥ 1`). -/
theorem prism_regular {d : ℕ} (hd : 1 ≤ d)
    [LocallyFinite ((⊤ : SimpleGraph (Fin d)) □ (⊤ : SimpleGraph (Fin 2)))] :
    ((⊤ : SimpleGraph (Fin d)) □ (⊤ : SimpleGraph (Fin 2))).IsRegularOfDegree d := by
  rintro ⟨a, b⟩
  rw [degree_eq_card_of_adj_iff _ _ (((univ.erase a) ×ˢ {b}) ∪ ({a} ×ˢ (univ.erase b)))]
  · rw [card_union_of_disjoint, card_product, card_product, card_erase_of_mem (mem_univ _),
      card_erase_of_mem (mem_univ _), card_singleton, card_singleton, card_univ, card_univ,
      Fintype.card_fin, Fintype.card_fin]
    · omega
    · rw [Finset.disjoint_left]
      rintro ⟨x, y⟩ h1 h2
      simp only [mem_product, mem_erase, mem_singleton, mem_univ, and_true] at h1 h2
      exact h1.1 h2.1
  · rintro ⟨x, y⟩
    simp only [boxProd_adj, top_adj, mem_union, mem_product, mem_erase, mem_singleton, mem_univ,
      and_true]
    constructor
    · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
      · exact Or.inl ⟨Ne.symm h1, h2.symm⟩
      · exact Or.inr ⟨h2.symm, Ne.symm h1⟩
    · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
      · exact Or.inl ⟨Ne.symm h1, h2.symm⟩
      · exact Or.inr ⟨Ne.symm h2, h1.symm⟩

/-- §1: the competitors exist. -/
theorem competitorFacts : CompetitorFacts := by
  refine ⟨fun d m hd hm => ⟨?_, ?_, ?_⟩, fun n hn h4 => ⟨?_, ?_⟩, ⟨cycleFourIsoKdd⟩⟩
  · obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
    simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin, Nat.add_sub_cancel]
    ring
  · exact isRegularOfDegree_of_inst (isRegularOfDegree_sum
      (isRegularOfDegree_of_inst (prism_regular (by omega)))
      (isRegularOfDegree_of_inst (kddUnion_regular (m - 1) d)))
  · intro hcf
    have h01 : (prismUnion d m).Adj (.inl (⟨0, by omega⟩, 0)) (.inl (⟨1, by omega⟩, 0)) := by
      simp [Fin.ext_iff]
    have h02 : (prismUnion d m).Adj (.inl (⟨0, by omega⟩, 0)) (.inl (⟨2, by omega⟩, 0)) := by
      simp [Fin.ext_iff]
    have h12 : (prismUnion d m).Adj (.inl (⟨1, by omega⟩, 0)) (.inl (⟨2, by omega⟩, 0)) := by
      simp [Fin.ext_iff]
    exact (is3Clique_triple_iff.2 ⟨h01, h02, h12⟩).not_cliqueFree hcf
  · obtain ⟨k, rfl⟩ : ∃ k, n = k + 3 := ⟨n - 3, by omega⟩
    intro v
    convert cycleGraph_degree_three_le (n := k) (v := v)
  · constructor
    intro φ
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    have hK := (Iso.connected_iff φ).1 cycleGraph_connected
    have hr := hK.preconnected ((⟨0, by omega⟩ : Fin ((k + 1) / 4)), (.inl 0 : Fin 2 ⊕ Fin 2))
      (⟨1, by omega⟩, .inl 0)
    rw [reachable_boxProd, reachable_bot] at hr
    simp [Fin.ext_iff] at hr

theorem gammaStar_pos_lt {n d : ℕ} (hd : 2 ≤ d) (hn : 0 < n) (hdn : 2 * d ∣ n)
    (hne : (n, d) ≠ (4, 2)) : 0 < gammaStar n d ∧ gammaStar n d < 1 / 2 := by
  obtain ⟨h1, h2, -, -⟩ := theoremA n d hd hn hdn hne
  constructor
  · unfold gammaStar
    apply div_pos
    · exact_mod_cast (show (0 : ℤ) < tStar n d by omega)
    · positivity
  · rw [h2]
    have : 0 < (3 * (d : ℝ) - 1) / ((d : ℝ) * n) := by
      apply div_pos
      · have : (2 : ℝ) ≤ d := by exact_mod_cast hd
        linarith
      · positivity
    linarith

/-- The answer is negative for every admissible `(n, d)` with `d ≥ 2`, `(n, d) ≠ (4, 2)`. -/
theorem negativeEveryAdmissible : NegativeEveryAdmissible := by
  intro n d hadm hd hne
  obtain ⟨_, hn1, hdn⟩ := hadm
  obtain ⟨hpos, hlt⟩ := gammaStar_pos_lt hd hn1 hdn hne
  refine ⟨hpos, hlt, fun hCQ => ?_⟩
  obtain ⟨_, _, h3, h4⟩ := theoremA n d hd hn1 hdn hne
  rcases (show d = 2 ∨ 3 ≤ d by omega) with rfl | hd3
  · have hn4 : n ≠ 4 := fun h => hne (by rw [h])
    have hn8 : 8 ≤ n := by omega
    obtain ⟨hreg, hiso⟩ := competitorFacts.2.1 n hn8 (by omega)
    have hlt' := h4 rfl (Fin n) (cycleGraph n) (Fintype.card_fin n)
      (isRegularOfDegree_of_inst hreg) hiso
    have hle := hCQ (Fin n) (cycleGraph n) (Fintype.card_fin n) (isRegularOfDegree_of_inst hreg)
    rw [show n / (2 * 2) = n / 4 by norm_num] at hle
    exact absurd hle (not_le.2 hlt')
  · obtain ⟨m, rfl⟩ := hdn
    have hm : 1 ≤ m := by
      rcases Nat.eq_zero_or_pos m with h | h
      · subst h
        simp at hn1
      · exact h
    obtain ⟨hcard, hreg, hnot⟩ := competitorFacts.1 d m hd3 hm
    obtain ⟨hineq, hiff⟩ := h3 hd3 _ (prismUnion d m) hcard (isRegularOfDegree_of_inst hreg)
    have hle := hCQ _ (prismUnion d m) hcard (isRegularOfDegree_of_inst hreg)
    have hT : (0 : ℝ) ≤ triangles (prismUnion d m) := by positivity
    have hge : (iGamma (KddUnion (2 * d * m / (2 * d)) d) d (gammaStar (2 * d * m) d) : ℝ) ≤
        iGamma (prismUnion d m) d (gammaStar (2 * d * m) d) := by linarith
    exact hnot (hiff.1 (le_antisymm hle (by exact_mod_cast hge)))

/-- §1, "Scope": `γ* > 1/8` unless `(n, d) ∈ {(4, 2), (6, 3)}`, `γ* → 1/2`, and the values at
`(6, 3)`. -/
theorem gammaStarScope : GammaStarScope := by
  refine ⟨?_, ?_, by decide, by norm_num [gammaStar, tStar]⟩
  · intro n d hadm hd hne hne6
    obtain ⟨_, hn1, hdn⟩ := hadm
    obtain ⟨-, h2, -, -⟩ := theoremA n d hd hn1 hdn hne
    rw [h2]
    obtain ⟨m, rfl⟩ := hdn
    have hm : 1 ≤ m := by
      rcases Nat.eq_zero_or_pos m with h | h
      · subst h
        simp at hn1
      · exact h
    have hpos : (0 : ℝ) < d * ((2 * d * m : ℕ) : ℝ) := by positivity
    suffices h : (3 * (d : ℝ) - 1) / (d * ((2 * d * m : ℕ) : ℝ)) < 3 / 8 by linarith
    rw [div_lt_iff₀ hpos]
    push_cast
    have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
    rcases (show d = 2 ∨ d = 3 ∨ 4 ≤ d by omega) with rfl | rfl | hd4
    · have hm2 : 2 ≤ m := by
        by_contra h
        have h1 : m = 1 := by omega
        subst h1
        exact hne rfl
      have hm2R : (2 : ℝ) ≤ m := by exact_mod_cast hm2
      nlinarith
    · have hm2 : 2 ≤ m := by
        by_contra h
        have h1 : m = 1 := by omega
        subst h1
        exact hne6 rfl
      have hm2R : (2 : ℝ) ≤ m := by exact_mod_cast hm2
      nlinarith
    · have hd4R : (4 : ℝ) ≤ d := by exact_mod_cast hd4
      have h1 : (d : ℝ) * d * m ≥ d * d := by nlinarith
      nlinarith
  · intro d hd
    have hdR : (0 : ℝ) < d := by exact_mod_cast hd
    have hd0 : (d : ℝ) ≠ 0 := hdR.ne'
    have key : ∀ m : ℕ, 1 ≤ m →
        gammaStar (2 * d * m) d = 1 / 2 - ((3 * d - 1) / (2 * d ^ 2)) / m := by
      intro m hm
      have hmR : (0 : ℝ) < m := by exact_mod_cast hm
      have hm0 : (m : ℝ) ≠ 0 := hmR.ne'
      unfold gammaStar
      rw [tStar_eq]
      push_cast
      field_simp
      ring
    have hlim : Tendsto (fun m : ℕ => (1 : ℝ) / 2 - ((3 * d - 1) / (2 * d ^ 2)) / m) atTop
        (𝓝 (1 / 2)) := by
      have := (tendsto_const_nhds (x := (1 : ℝ) / 2)).sub
        (tendsto_const_div_atTop_nhds_zero_nat ((3 * (d : ℝ) - 1) / (2 * d ^ 2)))
      simpa using this
    refine hlim.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with m hm
    exact (key m hm).symm

/-- Table 4: `(6, 3, 1/18)`. -/
theorem neg_6_3 : Neg_6_3 := by
  have h := (negativeEveryAdmissible 6 3 ⟨by norm_num, by norm_num, by norm_num⟩ (by norm_num)
    (by decide)).2.2
  have hg : gammaStar 6 3 = 1 / 18 := by norm_num [gammaStar, tStar]
  rwa [hg] at h

/-- Table 4: `(12, 3, 5/18)`. -/
theorem neg_12_3_top : Neg_12_3_top := by
  have h := (negativeEveryAdmissible 12 3 ⟨by norm_num, by norm_num, by norm_num⟩ (by norm_num)
    (by decide)).2.2
  have hg : gammaStar 12 3 = 5 / 18 := by norm_num [gammaStar, tStar]
  rwa [hg] at h

/-- The answer to Question 1.3 is negative. -/
theorem answerNegative : AnswerNegative := fun h =>
  neg_6_3 (h 6 3 (by norm_num) (by norm_num) (1 / 18) (by norm_num))

/-- The trivial cases: `d = 1` and `(n, d) = (4, 2)`. -/
theorem trivialCasesUnique : TrivialCasesUnique := by
  refine ⟨fun n _ _ V _ _ G _ hV hG => ?_, fun V _ _ G _ hV hG => ?_⟩
  · have h := iso_kddUnion_one G hG
    rwa [hV] at h
  · obtain ⟨φ⟩ := nonempty_iso_kdd_two G hV hG
    exact ⟨φ.trans (copiesOneIso (Kdd 2)).symm⟩

/-- In the trivial cases the question holds for every `γ`. -/
theorem trivialCasesTrue : TrivialCasesTrue := by
  intro n d _ hcase γ V _ _ G _ hV hG
  rcases hcase with rfl | ⟨rfl, rfl⟩
  · have h := iso_kddUnion_one G hG
    rw [hV, show n / 2 = n / (2 * 1) by norm_num] at h
    obtain ⟨φ⟩ := h
    exact le_of_eq (iGamma_iso_all φ 1 γ)
  · obtain ⟨φ⟩ := nonempty_iso_kdd_two G hV hG
    rw [show (4 : ℕ) / (2 * 2) = 1 by norm_num]
    exact le_of_eq (iGamma_iso_all (φ.trans (copiesOneIso (Kdd 2)).symm) 2 γ)

/-- §8: every `d`-regular graph on `2d` vertices is connected. -/
theorem regularOn2dConnected : RegularOn2dConnected := by
  intro d hd V _ _ G _ hV hG
  rw [connected_iff_exists_forall_reachable]
  have hne : Nonempty V := by
    rw [← Fintype.card_pos_iff, hV]
    omega
  obtain ⟨u⟩ := hne
  refine ⟨u, fun v => ?_⟩
  by_contra hr
  have hdisj : Disjoint (insert u (G.neighborFinset u)) (insert v (G.neighborFinset v)) := by
    rw [Finset.disjoint_left]
    intro w hwu hwv
    apply hr
    have h1 : G.Reachable u w := by
      rcases mem_insert.1 hwu with rfl | h
      · exact Reachable.refl _
      · exact ((G.mem_neighborFinset u w).1 h).reachable
    have h2 : G.Reachable w v := by
      rcases mem_insert.1 hwv with rfl | h
      · exact Reachable.refl _
      · exact ((G.mem_neighborFinset v w).1 h).reachable.symm
    exact h1.trans h2
  have hc := card_le_univ (insert u (G.neighborFinset u) ∪ insert v (G.neighborFinset v))
  rw [card_union_of_disjoint hdisj, card_insert_of_notMem (by simp),
    card_insert_of_notMem (by simp), card_neighborFinset_eq_degree,
    card_neighborFinset_eq_degree, hG.degree_eq, hG.degree_eq, hV] at hc
  omega

end P3A
