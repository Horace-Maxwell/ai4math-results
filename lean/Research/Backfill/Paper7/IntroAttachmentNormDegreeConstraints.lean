import Research.Backfill.Paper7.IntroAttachmentPerronWeights
import Research.Backfill.Paper7.IntroSubdividedArmCubicTransport

/-! Join actual local moments and spectral projector entries on one common
arm witness and one leaf-normalized positive eigenvector. Neither a numerical
norm nor a matrix moment is an input hypothesis. -/
set_option autoImplicit false
noncomputable section
open scoped Classical Matrix BigOperators

namespace Paper7IntroStarConstraints
open SimpleGraph Matrix BackfillPaper7.Challenge Paper7OddIntegral
open BackfillPaper7.Challenge.Legacy.Algebra
open Paper7IntroStarWeights Paper7IntroProjectors Paper7IntroAttachmentMoments
open Paper7IntroEven Paper7IntroFour Paper7UnicyclicAttachment

theorem subdivided_star_norm_degree_constraints
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : G.Connected) (hI : IsIntegralGraph G) (hB : G.Colorable 2)
    (hbound : ∀ t ∈ spec G, |t| ≤ 3)
    (Y : Finset V) (leaf : Y → V) (a c : V) (i₀ : Y)
    (hm : 3 ≤ Y.card) (hdeg : G.degree a = Y.card + 1)
    (hcY : c ∉ Y) (hal : ∀ i, a ≠ leaf i)
    (hNa : ∀ z, G.Adj a z ↔ z = c ∨ ∃ i : Y, z = i.val)
    (hNy : ∀ i : Y, ∀ z, G.Adj i.val z ↔ z = a ∨ z = leaf i)
    (hNl : ∀ i : Y, ∀ z, G.Adj (leaf i) z ↔ z = i.val)
    (hbridge : ∀ v, G.Adj a v → G.IsBridge s(a, v))
    (f : V → ℝ) (hf : ∀ v, 0 < f v)
    (hAf : G.adjMatrix ℝ *ᵥ f = (3 : ℝ) • f)
    (h₀ : f (leaf i₀) = 1) :
    (f ⬝ᵥ f) = 720 / ((Y.card : ℝ) - 2) ∧
    (G.degree c : ℝ) = -(Y.card : ℝ) ^ 2 + 9 * (Y.card : ℝ) - 12 ∧
    3 ≤ Y.card ∧ Y.card < 8 := by
  let : Nonempty V := ⟨a⟩
  obtain ⟨_hweights, _ha, hc, hlt⟩ := subdivided_star_normalized_perron_weights
    G Y leaf a c i₀ hcY hal hNa hNy hNl f hf hAf h₀
  obtain ⟨eps, hs, hflip⟩ := colorable_two_has_real_sign G hB
  have hproj := radius_three_projector_formulas G hG hI hbound eps f hs hflip hf hAf
  obtain ⟨hsgn, hcs⟩ := subdivided_star_bipartite_signs G Y leaf a c hNa hNy eps hflip
  have hsq : eps a * eps a = 1 := by
    rcases hs a with h | h
    · rw [h]; norm_num
    · rw [h]; norm_num
  have hls := (hsgn i₀).1
  have hprod : eps (leaf i₀) * eps c = -1 := by rw [hls, hcs, mul_neg, hsq]
  have hSp : radiusThreeS (G.adjMatrix ℝ) (leaf i₀) (leaf i₀) = 720 / (f ⬝ᵥ f) := by
    rw [(hproj (leaf i₀) (leaf i₀)).1, h₀, hls, hsq]
    ring
  have hTp : radiusThreeT (G.adjMatrix ℝ) (leaf i₀) c =
      (720 / (f ⬝ᵥ f)) * (8 - (Y.card : ℝ)) := by
    rw [(hproj (leaf i₀) c).2, h₀, hc, hprod]
    ring
  have hac : G.Adj a c := (hNa c).mpr (Or.inl rfl)
  have hcy : c ≠ i₀.val := by
    intro h
    exact hcY (h.symm ▸ i₀.property)
  have hS := subdivided_arm_leaf_sixth_gap G a i₀.val (leaf i₀)
    (hal i₀) (hNy i₀) (hNl i₀)
  change radiusThreeS (G.adjMatrix ℝ) (leaf i₀) (leaf i₀) = (G.degree a : ℝ) - 3 at hS
  have hT := subdivided_arm_cycle_odd_gap G a i₀.val (leaf i₀) c
    (hal i₀) hcy hac hbridge (hNy i₀) (hNl i₀)
  change radiusThreeT (G.adjMatrix ℝ) (leaf i₀) c =
    (G.degree a : ℝ) + (G.degree c : ℝ) - 5 at hT
  have hdegR : (G.degree a : ℝ) = (Y.card : ℝ) + 1 := by exact_mod_cast hdeg
  have hratio : 720 / (f ⬝ᵥ f) = (Y.card : ℝ) - 2 := by
    linarith only [hS, hSp, hdegR]
  have hNne : f ⬝ᵥ f ≠ 0 := by
    intro hz
    have hzero : f = 0 := dotProduct_self_eq_zero.mp hz
    have hp := hf a
    simp only [hzero, Pi.zero_apply, lt_self_iff_false] at hp
  have hmR : (3 : ℝ) ≤ (Y.card : ℝ) := by exact_mod_cast hm
  have hmne : (Y.card : ℝ) - 2 ≠ 0 := by linarith
  have hmul : (720 : ℝ) = ((Y.card : ℝ) - 2) * (f ⬝ᵥ f) :=
    (div_eq_iff hNne).mp hratio
  have hnorm : (f ⬝ᵥ f) = 720 / ((Y.card : ℝ) - 2) := by
    apply (eq_div_iff hmne).mpr
    calc
      (f ⬝ᵥ f) * ((Y.card : ℝ) - 2) = ((Y.card : ℝ) - 2) * (f ⬝ᵥ f) := mul_comm _ _
      _ = 720 := hmul.symm
  have hdc : (G.degree c : ℝ) = -(Y.card : ℝ) ^ 2 + 9 * (Y.card : ℝ) - 12 := by
    rw [hratio] at hTp
    nlinarith only [hT, hTp, hdegR]
  exact ⟨hnorm, hdc, hm, hlt⟩
#print axioms Paper7IntroStarConstraints.subdivided_star_norm_degree_constraints

theorem intro21_even_actual_attachment_norm_degree_constraints
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (b : ℕ)
    (hG : IsUnicyclicWithCycle G b) (hI : IsIntegralGraph G)
    (hn : Fintype.card V ≤ 21) (hb : Even b)
    (r : V) (w : G.Walk r r) (hw : w.IsCycle) (hlen : w.length = b)
    (C : (deleteVertices G {q | q ∈ w.support}).ConnectedComponent)
    (a : C.supp) (c : {q : V // q ∈ w.support}) (hac : G.Adj a.val.val c.val)
    (hex : ∃ x : C.supp, x ≠ a ∧ 2 ≤ G.degree x.val.val) :
    ∃ (Y : Finset V) (leaf : Y → V) (i₀ : Y) (f : V → ℝ),
      Y = (G.neighborFinset a.val.val).erase c.val ∧
      3 ≤ Y.card ∧ Y.card < 8 ∧ G.degree a.val.val = Y.card + 1 ∧
      Function.Injective leaf ∧
      (∀ x : C.supp, x = a ∨ ∃ i : Y, x.val.val = i.val ∨ x.val.val = leaf i) ∧
      (∀ z : V, G.Adj a.val.val z ↔ z = c.val ∨ ∃ i : Y, z = i.val) ∧
      (∀ (i : Y) (z : V), G.Adj i.val z ↔ z = a.val.val ∨ z = leaf i) ∧
      (∀ (i : Y) (z : V), G.Adj (leaf i) z ↔ z = i.val) ∧
      (∀ v, 0 < f v) ∧ G.adjMatrix ℝ *ᵥ f = (3 : ℝ) • f ∧
      f (leaf i₀) = 1 ∧ (∀ i : Y, f (leaf i) = 1 ∧ f i.val = 3) ∧
      f a.val.val = 8 ∧ f c.val = 3 * (8 - (Y.card : ℝ)) ∧
      (f ⬝ᵥ f) = 720 / ((Y.card : ℝ) - 2) ∧
      (G.degree c.val : ℝ) = -(Y.card : ℝ) ^ 2 + 9 * (Y.card : ℝ) - 12 := by
  obtain ⟨Y, leaf, _eps, f, hY, hm, hlt, hdeg, hinj, hcover,
    hNa, hNy, hNl, _hs, _hflip, hf, hAf, hweights, ha, hc,
    _hsgn, _hcs, _hproj, _hp, _hnrm, _hentries⟩ :=
    intro21_even_actual_attachment_perron_weights G b hG hI hn hb r w hw hlen C a c hac hex
  have hYpos : Y.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨y, hy⟩ := hYpos
  let i₀ : Y := ⟨y, hy⟩
  have h₀ : f (leaf i₀) = 1 := (hweights i₀).1
  have hcY : c.val ∉ Y := by rw [hY]; exact Finset.notMem_erase c.val _
  have hal : ∀ i : Y, a.val.val ≠ leaf i := by
    intro i he
    have hl := (hweights i).1
    rw [he] at ha
    linarith
  have hbridge : ∀ v, G.Adj a.val.val v → G.IsBridge s(a.val.val, v) := by
    intro v hav
    exact unicyclic_off_cycle_edge_isBridge G b hG r w hw hlen a.val.val v a.val.property hav
  obtain ⟨hN, hd, _hm, _hlt⟩ := subdivided_star_norm_degree_constraints
    G hG.1 hI (even_unicyclic_colorable_two G b hG hb)
    (intro21_even_spectrum_abs_le_three G b hG hI hn hb)
    Y leaf a.val.val c.val i₀ hm hdeg hcY hal hNa hNy hNl hbridge f hf hAf h₀
  exact ⟨Y, leaf, i₀, f, hY, hm, hlt, hdeg, hinj, hcover, hNa, hNy, hNl,
    hf, hAf, h₀, hweights, ha, hc, hN, hd⟩
#print axioms Paper7IntroStarConstraints.intro21_even_actual_attachment_norm_degree_constraints

end Paper7IntroStarConstraints
