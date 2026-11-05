import Research.Backfill.Paper7.IntroFourCycleColumnStarWeights

/-! The two real erased neighbor sets and a real filter cardinality yield the
parity contradiction. The column and complete star families are explicit
intermediate hypotheses; their original-graph transport remains separate. -/
set_option autoImplicit false
noncomputable section
open scoped Classical Matrix BigOperators

namespace Paper7IntroFourCycleWeights
open SimpleGraph Matrix

theorem four_cycle_column_star_parity_contradiction
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (eps f : V → ℝ) (hflip : ∀ v t, G.Adj v t → eps v = -eps t)
    (hf : ∀ v, 0 < f v) (hAf : G.adjMatrix ℝ *ᵥ f = (3 : ℝ) • f)
    (c u w z : V) (huz : u ≠ z)
    (hcu : G.Adj c u) (hcz : G.Adj c z) (hwu : G.Adj w u) (hwz : G.Adj w z)
    (hdc : G.degree c = 6) (hfc : f c = 5) (hfw : f w = 2)
    (hcommon : ∀ x, G.Adj c x → G.Adj w x → x = u ∨ x = z)
    (hcol : ∀ v, eps v = eps c → v ≠ c → ((G.adjMatrix ℝ) ^ 2) v c = f v)
    (hstarsC : ∀ x, G.Adj c x → x ≠ u → x ≠ z →
      ∃ Y : Finset V, c ∉ Y ∧ G.neighborFinset x = insert c Y ∧
        ∀ y ∈ Y, ∀ v, G.Adj y v ↔ v = x)
    (hstarsW : ∀ x, G.Adj w x → x ≠ u → x ≠ z →
      ∃ Y : Finset V, w ∉ Y ∧ G.neighborFinset x = insert w Y ∧
        ∀ y ∈ Y, ∀ v, G.Adj y v ↔ v = x) : False := by
  let Rc := ((G.neighborFinset c).erase u).erase z
  let Rw := ((G.neighborFinset w).erase u).erase z
  have hsignw : eps w = eps c := by linarith only [hflip c u hcu, hflip w u hwu]
  have hCweights : ∀ x ∈ Rc, f x = 3 ∨ f x = 5 / 3 := by
    intro x hx
    have hz := (Finset.mem_erase.mp hx).1
    have hi := Finset.mem_erase.mp (Finset.mem_erase.mp hx).2
    have hcx := (G.mem_neighborFinset c x).mp hi.2
    obtain ⟨Y, hcY, hNx, hNy⟩ := hstarsC x hcx hi.1 hz
    rcases pure_star_column_at_c G eps f hflip hAf c x Y hcY hNx hNy hfc hcol with h | h
    · exact Or.inr h.2
    · exact Or.inl h.2
  have hWweights : ∀ x ∈ Rw, f x = 2 / 3 := by
    intro x hx
    have hz := (Finset.mem_erase.mp hx).1
    have hi := Finset.mem_erase.mp (Finset.mem_erase.mp hx).2
    have hwx := (G.mem_neighborFinset w x).mp hi.2
    obtain ⟨Y, _hwY, hNx, hNy⟩ := hstarsW x hwx hi.1 hz
    have hxc : ¬ G.Adj x c := by
      intro hxc
      rcases hcommon x hxc.symm hwx with hxu | hxz
      · exact hi.1 hxu
      · exact hz hxz
    exact (pure_star_column_at_opposite G eps f hflip hf hAf c w x Y
      hsignw (by omega) hNx hNy hxc hfw hcol).2
  have hcuN : u ∈ G.neighborFinset c := (G.mem_neighborFinset c u).mpr hcu
  have hczN : z ∈ (G.neighborFinset c).erase u :=
    Finset.mem_erase.mpr ⟨huz.symm, (G.mem_neighborFinset c z).mpr hcz⟩
  have hRcCard : Rc.card = 4 := by
    simp only [Rc, Finset.card_erase_of_mem hczN, Finset.card_erase_of_mem hcuN,
      G.card_neighborFinset_eq_degree, hdc]
  have hrowerase (v : V) (hvu : G.Adj v u) (hvz : G.Adj v z) :
      (∑ x ∈ ((G.neighborFinset v).erase u).erase z, f x) + f z + f u = 3 * f v := by
    have huN : u ∈ G.neighborFinset v := (G.mem_neighborFinset v u).mpr hvu
    have hzN : z ∈ (G.neighborFinset v).erase u :=
      Finset.mem_erase.mpr ⟨huz.symm, (G.mem_neighborFinset v z).mpr hvz⟩
    have h1 := Finset.sum_erase_add (G.neighborFinset v) f huN
    have h2 := Finset.sum_erase_add ((G.neighborFinset v).erase u) f hzN
    have hrow : ∑ x ∈ G.neighborFinset v, f x = 3 * f v := by
      simpa only [G.adjMatrix_mulVec_apply, Pi.smul_apply, smul_eq_mul] using congrFun hAf v
    linarith only [h1, h2, hrow]
  have hrowC : (∑ x ∈ Rc, f x) + f z + f u = 15 := by
    have he := hrowerase c hcu hcz
    rw [hfc] at he
    norm_num at he
    exact he
  have hrowW : (∑ x ∈ Rw, f x) + f z + f u = 6 := by
    have he := hrowerase w hwu hwz
    rw [hfw] at he
    norm_num at he
    exact he
  let H := Rc.filter (fun x => f x = 3)
  let J := Rc \ H
  have hHsub : H ⊆ Rc := Finset.filter_subset _ _
  have hHsum : ∑ x ∈ H, f x = (H.card : ℝ) * 3 := by
    calc
      _ = ∑ _x ∈ H, (3 : ℝ) := by
        apply Finset.sum_congr rfl
        intro x hx
        exact (Finset.mem_filter.mp hx).2
      _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]
  have hJsum : ∑ x ∈ J, f x = (J.card : ℝ) * (5 / 3) := by
    calc
      _ = ∑ _x ∈ J, (5 / 3 : ℝ) := by
        apply Finset.sum_congr rfl
        intro x hx
        have hi := Finset.mem_sdiff.mp hx
        have hne : f x ≠ 3 := fun he => hi.2 (Finset.mem_filter.mpr ⟨hi.1, he⟩)
        exact (hCweights x hi.1).resolve_left hne
      _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]
  have hWsum : ∑ x ∈ Rw, f x = (Rw.card : ℝ) * (2 / 3) := by
    calc
      _ = ∑ _x ∈ Rw, (2 / 3 : ℝ) := Finset.sum_congr rfl (fun x hx => hWweights x hx)
      _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]
  have hsplit : (∑ x ∈ J, f x) + (∑ x ∈ H, f x) = ∑ x ∈ Rc, f x :=
    Finset.sum_sdiff hHsub
  have hcard : J.card + H.card = 4 := by
    have he := Finset.card_sdiff_add_card_eq_card hHsub
    change J.card + H.card = Rc.card at he
    rw [hRcCard] at he
    exact he
  have hcardR : (J.card : ℝ) + (H.card : ℝ) = 4 := by exact_mod_cast hcard
  have hparityR : 2 * (Rw.card : ℝ) + 7 = 4 * (H.card : ℝ) := by
    nlinarith only [hrowC, hrowW, hHsum, hJsum, hWsum, hsplit, hcardR]
  have hparity : 2 * Rw.card + 7 = 4 * H.card := by exact_mod_cast hparityR
  omega
#print axioms Paper7IntroFourCycleWeights.four_cycle_column_star_parity_contradiction

end Paper7IntroFourCycleWeights
