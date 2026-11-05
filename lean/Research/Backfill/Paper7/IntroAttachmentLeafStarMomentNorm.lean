import Research.Backfill.Paper7.IntroAttachmentLeafStarWeights
import Research.Backfill.Paper7.IntroPureLeafStarLocalMoments

/-! Join genuine local leaf moments and the spectral diagonal on the
same canonical leaf-star and the same normalized Perron vector. The graph
wrapper has no extra local-moment, norm, or equality-of-witnesses premise. -/
set_option autoImplicit false
noncomputable section
open scoped Classical Matrix BigOperators

namespace Paper7IntroLeafStarWeights
open SimpleGraph Matrix BackfillPaper7.Challenge Paper7OddIntegral
open BackfillPaper7.Challenge.Legacy.Algebra
open Paper7IntroProjectors Paper7IntroPureLeafMoments

theorem intro21_even_actual_leaf_star_moment_norm
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (b : ℕ)
    (hG : IsUnicyclicWithCycle G b) (hI : IsIntegralGraph G)
    (hn : Fintype.card V ≤ 21) (hb : Even b)
    (r : V) (w : G.Walk r r) (hw : w.IsCycle) (hlen : w.length = b)
    (C : (deleteVertices G {q | q ∈ w.support}).ConnectedComponent)
    (a : C.supp) (c : {q : V // q ∈ w.support}) (hac : G.Adj a.val.val c.val)
    (hleaves : ((G.neighborFinset a.val.val).erase c.val).Nonempty) :
    ∃ (Y : Finset V) (i₀ : Y) (eps f : V → ℝ),
      Y = (G.neighborFinset a.val.val).erase c.val ∧
      1 ≤ Y.card ∧ Y.card ≤ 7 ∧ Y.card < 9 ∧
      G.degree a.val.val = Y.card + 1 ∧ a.val.val ≠ c.val ∧
      Function.Injective (fun i : Y => i.val) ∧
      (∀ i : Y, (∃ x : C.supp, x.val.val = i.val) ∧
        G.degree i.val = 1 ∧ i.val ≠ a.val.val ∧ i.val ≠ c.val) ∧
      (∀ x : C.supp, x = a ∨ ∃ i : Y, x.val.val = i.val) ∧
      (∀ z : V, G.Adj a.val.val z ↔ z = c.val ∨ ∃ i : Y, z = i.val) ∧
      (∀ (i : Y) (z : V), G.Adj i.val z ↔ z = a.val.val) ∧
      (integerSpectrum G).count 3 = 1 ∧
      (∀ v, eps v = 1 ∨ eps v = -1) ∧
      (∀ u v, G.Adj u v → eps u = -eps v) ∧
      (∀ v, 0 < f v) ∧ G.adjMatrix ℝ *ᵥ f = (3 : ℝ) • f ∧
      f i₀.val = 1 ∧ (∀ i : Y, f i.val = 1) ∧
      f a.val.val = 3 ∧ f c.val = 9 - (Y.card : ℝ) ∧
      (∀ i : Y, eps i.val = -eps a.val.val) ∧ eps c.val = -eps a.val.val ∧
      (∀ u v, radiusThreeS (G.adjMatrix ℝ) u v =
          (360 / (f ⬝ᵥ f)) * f u * f v * (1 + eps u * eps v) ∧
        radiusThreeT (G.adjMatrix ℝ) u v =
          (120 / (f ⬝ᵥ f)) * f u * f v * (1 - eps u * eps v)) ∧
      (∑ v, if eps v = 1 then f v ^ 2 else 0) = (f ⬝ᵥ f) / 2 ∧
      (∑ v, if eps v = -1 then f v ^ 2 else 0) = (f ⬝ᵥ f) / 2 ∧
      (∀ i : Y, ((G.adjMatrix ℝ) ^ 2) i.val i.val = 1 ∧
        ((G.adjMatrix ℝ) ^ 4) i.val i.val = (Y.card : ℝ) + 1 ∧
        ((G.adjMatrix ℝ) ^ 6) i.val i.val =
          (G.degree c.val : ℝ) + (Y.card : ℝ) ^ 2 + 2 * (Y.card : ℝ) ∧
        radiusThreeS (G.adjMatrix ℝ) i.val i.val =
          (G.degree c.val : ℝ) + (Y.card : ℝ) ^ 2 - 3 * (Y.card : ℝ) - 1) ∧
      0 < f ⬝ᵥ f ∧
      0 < (G.degree c.val : ℝ) + (Y.card : ℝ) ^ 2 - 3 * (Y.card : ℝ) - 1 ∧
      (f ⬝ᵥ f) = 720 /
        ((G.degree c.val : ℝ) + (Y.card : ℝ) ^ 2 - 3 * (Y.card : ℝ) - 1) := by
  obtain ⟨Y, i₀, eps, f, hY, hmpos, hm7, hlt, hda, hne, hinj, hdata,
    hcover, hNa, hNl, hthree, hs, hflip, hf, hAf, h₀, hweights, ha, hc,
    hsgn, hcs, hproj, hp, hnrm⟩ :=
    intro21_even_actual_leaf_star_perron_weights G b hG hI hn hb r w hw hlen C a c hac hleaves
  have hcY : c.val ∉ Y := by rw [hY]; exact Finset.notMem_erase c.val _
  have hNa' : G.neighborFinset a.val.val = insert c.val Y := by
    ext z
    simp only [SimpleGraph.mem_neighborFinset, Finset.mem_insert]
    rw [hNa z]
    constructor
    · rintro (hzc | ⟨i, hzi⟩)
      · exact Or.inl hzc
      · exact Or.inr (hzi.symm ▸ i.property)
    · rintro (hzc | hzY)
      · exact Or.inl hzc
      · exact Or.inr ⟨⟨z, hzY⟩, rfl⟩
  have hNl' : ∀ y ∈ Y, ∀ z, G.Adj y z ↔ z = a.val.val := by
    intro y hy z
    exact hNl ⟨y, hy⟩ z
  have hmom : ∀ i : Y, ((G.adjMatrix ℝ) ^ 2) i.val i.val = 1 ∧
      ((G.adjMatrix ℝ) ^ 4) i.val i.val = (Y.card : ℝ) + 1 ∧
      ((G.adjMatrix ℝ) ^ 6) i.val i.val =
        (G.degree c.val : ℝ) + (Y.card : ℝ) ^ 2 + 2 * (Y.card : ℝ) ∧
      radiusThreeS (G.adjMatrix ℝ) i.val i.val =
        (G.degree c.val : ℝ) + (Y.card : ℝ) ^ 2 - 3 * (Y.card : ℝ) - 1 := by
    intro i
    obtain ⟨h2, h4, h6⟩ := pure_leaf_star_leaf_even_moments
      G a.val.val c.val Y hcY hNa' hNl' i.val i.property
    have hS := pure_leaf_star_leaf_S_diagonal
      G a.val.val c.val Y hcY hNa' hNl' i.val i.property
    exact ⟨h2, h4, h6, hS⟩
  have hsq : eps i₀.val * eps i₀.val = 1 := by
    rcases hs i₀.val with h | h
    · rw [h]; norm_num
    · rw [h]; norm_num
  have hSp : radiusThreeS (G.adjMatrix ℝ) i₀.val i₀.val = 720 / (f ⬝ᵥ f) := by
    rw [(hproj i₀.val i₀.val).1, h₀, hsq]
    ring
  have hratio : 720 / (f ⬝ᵥ f) =
      (G.degree c.val : ℝ) + (Y.card : ℝ) ^ 2 - 3 * (Y.card : ℝ) - 1 :=
    hSp.symm.trans (hmom i₀).2.2.2
  have hNne : f ⬝ᵥ f ≠ 0 := by
    intro hz
    have hzero : f = 0 := dotProduct_self_eq_zero.mp hz
    have hz₀ := congrFun hzero i₀.val
    change f i₀.val = 0 at hz₀
    linarith only [h₀, hz₀]
  have hNnonneg : 0 ≤ f ⬝ᵥ f := by
    change 0 ≤ ∑ v, f v * f v
    exact Finset.sum_nonneg (fun v _hv => mul_self_nonneg (f v))
  have hNpos : 0 < f ⬝ᵥ f := lt_of_le_of_ne hNnonneg (Ne.symm hNne)
  have hqpos : 0 < (G.degree c.val : ℝ) + (Y.card : ℝ) ^ 2 - 3 * (Y.card : ℝ) - 1 := by
    rw [← hratio]
    exact div_pos (by norm_num) hNpos
  have hmul : (720 : ℝ) =
      ((G.degree c.val : ℝ) + (Y.card : ℝ) ^ 2 - 3 * (Y.card : ℝ) - 1) * (f ⬝ᵥ f) :=
    (div_eq_iff hNne).mp hratio
  have hnorm : (f ⬝ᵥ f) = 720 /
      ((G.degree c.val : ℝ) + (Y.card : ℝ) ^ 2 - 3 * (Y.card : ℝ) - 1) := by
    apply (eq_div_iff (ne_of_gt hqpos)).mpr
    calc
      (f ⬝ᵥ f) * ((G.degree c.val : ℝ) + (Y.card : ℝ) ^ 2 - 3 * (Y.card : ℝ) - 1) =
          ((G.degree c.val : ℝ) + (Y.card : ℝ) ^ 2 - 3 * (Y.card : ℝ) - 1) * (f ⬝ᵥ f) := mul_comm _ _
      _ = 720 := hmul.symm
  exact ⟨Y, i₀, eps, f, hY, hmpos, hm7, hlt, hda, hne, hinj, hdata,
    hcover, hNa, hNl, hthree, hs, hflip, hf, hAf, h₀, hweights, ha, hc,
    hsgn, hcs, hproj, hp, hnrm, hmom, hNpos, hqpos, hnorm⟩
#print axioms Paper7IntroLeafStarWeights.intro21_even_actual_leaf_star_moment_norm

end Paper7IntroLeafStarWeights
