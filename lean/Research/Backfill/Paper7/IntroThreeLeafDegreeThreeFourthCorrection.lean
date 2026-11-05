import Research.Backfill.Paper7.IntroUnicyclicExactFourthMoment
import Research.Backfill.Paper7.IntroThreeLeafDegreeThreeSuccessorRows
import Research.Backfill.Paper7.IntroPureLeafStarCycleFourthConstraint

/-! The same original integer Perron witness yields the exact external-leaf
count. The cycle correction comes from actual two-step fibres, not a new
matrix, coverage, integrality, or square-budget assumption. -/
set_option autoImplicit false
noncomputable section
open scoped Classical Matrix BigOperators

namespace Paper7IntroThreeLeafFourthCorrection
open SimpleGraph Matrix BackfillPaper7.Challenge Paper7OddIntegral
open BackfillPaper7.Challenge.Legacy.Algebra
open Paper7IntroProjectors Paper7IntroThreeLeafSuccessors
open Paper7IntroPureLeafConstraints Paper7IntroUnicyclicExactFourth Paper7IntroFour

theorem intro21_even_three_leaf_degree_three_fourth_correction
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (b : ℕ)
    (hG : IsUnicyclicWithCycle G b) (hI : IsIntegralGraph G)
    (hn : Fintype.card V ≤ 21) (hb : Even b)
    (r : V) (w : G.Walk r r) (hw : w.IsCycle) (hlen : w.length = b)
    (C : (deleteVertices G {q | q ∈ w.support}).ConnectedComponent)
    (a : C.supp) (c : {q : V // q ∈ w.support}) (hac : G.Adj a.val.val c.val)
    (hm : ((G.neighborFinset a.val.val).erase c.val).card = 3)
    (hd : G.degree c.val = 3) :
    ∃ (Y : Finset V) (i₀ : Y) (eps f : V → ℝ) (z : V → ℤ),
      Y = (G.neighborFinset a.val.val).erase c.val ∧ Y.card = 3 ∧
      G.degree a.val.val = Y.card + 1 ∧ a.val.val ≠ c.val ∧
      (∀ i : Y, (∃ x : C.supp, x.val.val = i.val) ∧
        G.degree i.val = 1 ∧ i.val ≠ a.val.val ∧ i.val ≠ c.val) ∧
      (∀ x : C.supp, x = a ∨ ∃ i : Y, x.val.val = i.val) ∧
      (∀ t : V, G.Adj a.val.val t ↔ t = c.val ∨ ∃ i : Y, t = i.val) ∧
      (∀ (i : Y) (t : V), G.Adj i.val t ↔ t = a.val.val) ∧
      (∀ v, eps v = 1 ∨ eps v = -1) ∧
      (∀ u v, G.Adj u v → eps u = -eps v) ∧
      (∀ v, 0 < f v) ∧ G.adjMatrix ℝ *ᵥ f = (3 : ℝ) • f ∧
      f i₀.val = 1 ∧ (∀ i : Y, f i.val = 1) ∧
      f a.val.val = 3 ∧ f c.val = 6 ∧
      (∀ i : Y, eps i.val = -eps a.val.val) ∧ eps c.val = -eps a.val.val ∧
      (∀ u v, radiusThreeS (G.adjMatrix ℝ) u v =
          (360 / (f ⬝ᵥ f)) * f u * f v * (1 + eps u * eps v) ∧
        radiusThreeT (G.adjMatrix ℝ) u v =
          (120 / (f ⬝ᵥ f)) * f u * f v * (1 - eps u * eps v)) ∧
      (f ⬝ᵥ f) = 360 ∧ (∀ v, 0 < z v) ∧
      (∀ v, eps v = eps i₀.val → f v = (z v : ℝ)) ∧
      (∀ v, eps v = -eps i₀.val → f v = 3 * (z v : ℝ)) ∧
      (∑ v, if eps v = eps i₀.val then z v ^ 2 else 0) = 180 ∧
      (∑ v, if eps v = -eps i₀.val then z v ^ 2 else 0) = 20 ∧
      (∀ v, v ∈ w.support → eps v = -eps i₀.val →
        ∀ x, x ∉ w.support → G.Adj x v →
          (G.neighborFinset x).erase v = ∅ ∧ G.neighborFinset x = {v} ∧
          (∀ t, G.Adj x t ↔ t = v) ∧ G.degree x = 1 ∧ f x = (z v : ℝ)) ∧
      ∃ (u v s t : V) (K J : Finset V),
        u ∈ w.support ∧ v ∈ w.support ∧ u ≠ v ∧
        G.Adj c.val u ∧ G.Adj c.val v ∧
        G.neighborFinset c.val = {a.val.val, u, v} ∧
        (∀ q, q ∈ w.support → (G.Adj c.val q ↔ q = u ∨ q = v)) ∧
        eps u = -eps i₀.val ∧ eps v = -eps i₀.val ∧ z u + z v = 5 ∧
        s ∈ w.support ∧ s ≠ c.val ∧ G.Adj u s ∧
        (∀ q, q ∈ w.support → (G.Adj u q ↔ q = c.val ∨ q = s)) ∧
        t ∈ w.support ∧ t ≠ c.val ∧ G.Adj v t ∧
        (∀ q, q ∈ w.support → (G.Adj v q ↔ q = c.val ∨ q = t)) ∧
        K = ((G.neighborFinset u).erase c.val).erase s ∧
        J = ((G.neighborFinset v).erase c.val).erase t ∧
        (∀ x, x ∈ K ↔ G.Adj u x ∧ x ∉ w.support) ∧
        (∀ x, x ∈ J ↔ G.Adj v x ∧ x ∉ w.support) ∧
        G.neighborFinset u = insert c.val (insert s K) ∧
        G.neighborFinset v = insert c.val (insert t J) ∧
        (∀ x ∈ K, G.neighborFinset x = {u} ∧
          (∀ q, G.Adj x q ↔ q = u) ∧ G.degree x = 1 ∧ f x = (z u : ℝ)) ∧
        (∀ x ∈ J, G.neighborFinset x = {v} ∧
          (∀ q, G.Adj x q ↔ q = v) ∧ G.degree x = 1 ∧ f x = (z v : ℝ)) ∧
        (∑ x ∈ K, f x) = (K.card : ℝ) * (z u : ℝ) ∧
        (∑ x ∈ J, f x) = (J.card : ℝ) * (z v : ℝ) ∧
        f s = (9 - (K.card : ℝ)) * (z u : ℝ) - 6 ∧
        f t = (9 - (J.card : ℝ)) * (z v : ℝ) - 6 ∧
        ((G.adjMatrix ℝ) ^ 4) c.val c.val = 20 ∧
        K.card + J.card = if b = 4 then 4 else 6 := by
  obtain ⟨Y, i₀, eps, f, z, hY, hmY, hda, hne, hdata, hcover, hNa, hNl,
    hs, hflip, hf, hAf, h₀, hweights, ha, hc, hsgn, hcs, hproj, hN, hz,
    hsame, hopp, hsumU, hsumW, hexternal,
    u, v, s, t, K, J, hu, hv, huv, hcu, hcv, hNc, hfullc, huW, hvW, hsumZ,
    hsC, hsc, hus, hfullu, htC, htc, hvt, hfullv, hK, hJ, hKmem, hJmem,
    hNu, hNv, hKleaf, hJleaf, hKsum, hJsum, hfs, hft⟩ :=
    intro21_even_three_leaf_degree_three_successor_rows G b hG hI hn hb
      r w hw hlen C a c hac hm hd
  have hcY : c.val ∉ Y := by rw [hY]; exact Finset.notMem_erase c.val _
  have hNa' : G.neighborFinset a.val.val = insert c.val Y := by
    ext q
    simp only [SimpleGraph.mem_neighborFinset, Finset.mem_insert]
    rw [hNa q]
    constructor
    · rintro (hqc | ⟨i, hqi⟩)
      · exact Or.inl hqc
      · exact Or.inr (hqi.symm ▸ i.property)
    · rintro (hqc | hqY)
      · exact Or.inl hqc
      · exact Or.inr ⟨⟨q, hqY⟩, rfl⟩
  have hNl' : ∀ y ∈ Y, ∀ q, G.Adj y q ↔ q = a.val.val := by
    intro y hy q
    exact hNl ⟨y, hy⟩ q
  have hbound := intro21_even_spectrum_abs_le_three G b hG hI hn hb
  have hmoment := pure_leaf_star_cycle_fourth_constraint G hI hbound
    a.val.val c.val Y hcY hNa' hNl' i₀.val i₀.property
  have hm4 : ((G.adjMatrix ℝ) ^ 4) c.val c.val = 20 := by
    norm_num [hmY, hd] at hmoment
    exact hmoment
  have hda4 : G.degree a.val.val = 4 := by omega
  have hcK : c.val ∉ K := fun h => ((hKmem c.val).mp h).2 c.property
  have hsK : s ∉ K := fun h => ((hKmem s).mp h).2 hsC
  have hcJ : c.val ∉ J := fun h => ((hJmem c.val).mp h).2 c.property
  have htJ : t ∉ J := fun h => ((hJmem t).mp h).2 htC
  have hcSK : c.val ∉ insert s K := by
    simp only [Finset.mem_insert, not_or]
    exact ⟨hsc.symm, hcK⟩
  have hcTJ : c.val ∉ insert t J := by
    simp only [Finset.mem_insert, not_or]
    exact ⟨htc.symm, hcJ⟩
  have hdu : G.degree u = K.card + 2 := by
    rw [← G.card_neighborFinset_eq_degree, hNu,
      Finset.card_insert_of_notMem hcSK, Finset.card_insert_of_notMem hsK]
  have hdv : G.degree v = J.card + 2 := by
    rw [← G.card_neighborFinset_eq_degree, hNv,
      Finset.card_insert_of_notMem hcTJ, Finset.card_insert_of_notMem htJ]
  have hau : a.val.val ≠ u := by
    intro h
    apply a.val.property
    rw [h]
    exact hu
  have hav : a.val.val ≠ v := by
    intro h
    apply a.val.property
    rw [h]
    exact hv
  have haUV : a.val.val ∉ ({u, v} : Finset V) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨hau, hav⟩
  have hsum : (∑ q ∈ G.neighborFinset c.val, ((G.degree q : ℝ) - 1)) =
      5 + (K.card : ℝ) + (J.card : ℝ) := by
    rw [hNc, Finset.sum_insert haUV, Finset.sum_pair huv, hda4, hdu, hdv]
    push_cast
    ring
  have hcount : K.card + J.card = if b = 4 then 4 else 6 := by
    by_cases hb4 : b = 4
    · have he := unicyclic_four_fourth_moment_exact G b hG r w hw hlen hb4
        c.val c.property
      rw [hm4, hd, hsum] at he
      norm_num only [Nat.cast_ofNat] at he
      have heR : (K.card : ℝ) + (J.card : ℝ) = 4 := by nlinarith only [he]
      rw [ite_eq_left hb4]
      exact_mod_cast heR
    · have he := unicyclic_nonfour_fourth_moment_exact G b hG r w hw hlen hb4 c.val
      rw [hm4, hd, hsum] at he
      norm_num only [Nat.cast_ofNat] at he
      have heR : (K.card : ℝ) + (J.card : ℝ) = 6 := by nlinarith only [he]
      rw [ite_eq_right hb4]
      exact_mod_cast heR
  exact ⟨Y, i₀, eps, f, z, hY, hmY, hda, hne, hdata, hcover, hNa, hNl,
    hs, hflip, hf, hAf, h₀, hweights, ha, hc, hsgn, hcs, hproj, hN, hz,
    hsame, hopp, hsumU, hsumW, hexternal,
    u, v, s, t, K, J, hu, hv, huv, hcu, hcv, hNc, hfullc, huW, hvW, hsumZ,
    hsC, hsc, hus, hfullu, htC, htc, hvt, hfullv, hK, hJ, hKmem, hJmem,
    hNu, hNv, hKleaf, hJleaf, hKsum, hJsum, hfs, hft, hm4, hcount⟩
#print axioms Paper7IntroThreeLeafFourthCorrection.intro21_even_three_leaf_degree_three_fourth_correction

end Paper7IntroThreeLeafFourthCorrection
