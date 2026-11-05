import Research.Backfill.Paper7.IntroPerronSideRemainder
import Research.Backfill.Paper7.IntroUnicyclicDoubleCommonCycle
import Research.Backfill.Paper7.IntroThreeLeafDegreeThreeBudget

/-! Source-only actual-graph budget transport. All witness fields can be
supplied by one successful successor-row witness. This is a generic branch
interface, not an original Intro21 wrapper or an added hypothesis there. -/
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators Matrix

namespace Paper7IntroThreeLeafNonfourBudget
open SimpleGraph Matrix BackfillPaper7.Challenge
open Paper7IntroSideRemainder Paper7IntroTwoStepTopology
open Paper7ThreeLeafDegreeThreeBudget

theorem three_leaf_nonfour_same_witness_budget_contradiction
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (b : ℕ)
    (hG : IsUnicyclicWithCycle G b)
    (r : V) (w : G.Walk r r) (hw : w.IsCycle) (hlen : w.length = b)
    (hb4 : b ≠ 4) (eps f : V → ℝ) (z : V → ℤ)
    (hflip : ∀ x y, G.Adj x y → eps x = -eps y)
    (hAf : G.adjMatrix ℝ *ᵥ f = (3 : ℝ) • f)
    (hz : ∀ x, 0 < z x)
    (a c u v s t : V) (Y K J : Finset V)
    (haout : a ∉ w.support) (huC : u ∈ w.support) (hvC : v ∈ w.support)
    (hsC : s ∈ w.support) (htC : t ∈ w.support)
    (huv : u ≠ v) (hsc : s ≠ c) (htc : t ≠ c)
    (hcu : G.Adj c u) (hcv : G.Adj c v) (hus : G.Adj u s) (hvt : G.Adj v t)
    (hNa : G.neighborFinset a = insert c Y)
    (hYout : ∀ x ∈ Y, x ∉ w.support)
    (haW : eps a = -eps c) (hfa : f a = 3)
    (hscale : ∀ x, eps x = -eps c → f x = 3 * (z x : ℝ))
    (hside : (∑ x, if eps x = -eps c then z x ^ 2 else 0) = 20)
    (huvsum : z u + z v = 5) (horder : z u ≤ z v)
    (hK : K = ((G.neighborFinset u).erase c).erase s)
    (hJ : J = ((G.neighborFinset v).erase c).erase t)
    (hKJ : K.card + J.card = 6)
    (hfs : f s = (9 - (K.card : ℝ)) * (z u : ℝ) - 6)
    (hft : f t = (9 - (J.card : ℝ)) * (z v : ℝ) - 6) : False := by
  subst K
  subst J
  let K := ((G.neighborFinset u).erase c).erase s
  let J := ((G.neighborFinset v).erase c).erase t
  let W := Finset.univ.filter (fun x : V => eps x = -eps c)
  let R := ((W.erase a).erase u).erase v
  let P := R.filter (fun x => G.Adj s x)
  let Q := R.filter (fun x => G.Adj t x)
  let h : V → ℝ := fun x => (z x : ℝ)
  have hmemW : ∀ x, x ∈ W ↔ eps x = -eps c := by
    intro x
    simp only [W, Finset.mem_filter, Finset.mem_univ, true_and]
  have huW : u ∈ W := (hmemW u).mpr (by linarith only [hflip c u hcu])
  have hvW : v ∈ W := (hmemW v).mpr (by linarith only [hflip c v hcv])
  have haW' : a ∈ W := (hmemW a).mpr haW
  have hau : a ≠ u := by
    intro he
    apply haout
    rw [he]
    exact huC
  have hav : a ≠ v := by
    intro he
    apply haout
    rw [he]
    exact hvC
  have hhscale : ∀ x ∈ W, f x = 3 * h x := by
    intro x hx
    exact hscale x ((hmemW x).mp hx)
  have hha : h a = 1 := by
    have hh := hhscale a haW'
    rw [hfa] at hh
    linarith only [hh]
  have hsum : (∑ x ∈ W, h x ^ 2) = 20 := by
    have hh : (∑ x, if eps x = -eps c then (z x : ℝ) ^ 2 else 0) = 20 := by
      exact_mod_cast hside
    simpa only [W, h, Finset.sum_filter] using hh
  have hxy : h u + h v = 5 := by
    change (z u : ℝ) + (z v : ℝ) = 5
    exact_mod_cast huvsum
  have hRsum : (∑ x ∈ R, h x ^ 2) = 2 * h u * h v - 6 :=
    three_erased_square_budget W h a u v haW' huW hvW hau hav huv hha hsum hxy
  have hcs := unicyclic_nonfour_two_step_fibre G b hG r w hw hlen hb4
    c u s hsc.symm hcu hus
  have hct := unicyclic_nonfour_two_step_fibre G b hG r w hw hlen hb4
    c v t htc.symm hcv hvt
  have hnvs : ¬ G.Adj v s := by
    intro hvs
    exact huv.symm ((hcs.1 v).mp ⟨hcv, hvs⟩)
  have hnut : ¬ G.Adj u t := by
    intro hut
    exact huv ((hct.1 u).mp ⟨hcu, hut⟩)
  have hst : s ≠ t := by
    intro he
    apply hnvs
    rw [he]
    exact hvt
  have hnoa : ∀ d, d ∈ w.support → d ≠ c → ¬ G.Adj d a := by
    intro d hdC hdc hda
    have hdN : d ∈ insert c Y := by
      rw [← hNa]
      exact (G.mem_neighborFinset a d).mpr hda.symm
    rcases Finset.mem_insert.mp hdN with hdc' | hdY
    · exact hdc hdc'
    · exact hYout d hdY hdC
  have hNsW : ∀ x, G.Adj s x → x ∈ W := by
    intro x hsx
    apply (hmemW x).mpr
    linarith only [hflip c u hcu, hflip u s hus, hflip s x hsx]
  have hNtW : ∀ x, G.Adj t x → x ∈ W := by
    intro x htx
    apply (hmemW x).mpr
    linarith only [hflip c v hcv, hflip v t hvt, hflip t x htx]
  have havoidS : ∀ x, (x = a ∨ x = u ∨ x = v) → G.Adj s x → x = u := by
    intro x hx hsx
    rcases hx with hxa | hxu | hxv
    · exact (hnoa s hsC hsc (hxa ▸ hsx)).elim
    · exact hxu
    · exact (hnvs (hxv ▸ hsx).symm).elim
  have havoidT : ∀ x, (x = a ∨ x = u ∨ x = v) → G.Adj t x → x = v := by
    intro x hx htx
    rcases hx with hxa | hxu | hxv
    · exact (hnoa t htC htc (hxa ▸ htx)).elim
    · exact (hnut (hxu ▸ htx).symm).elim
    · exact hxv
  have hP : (∑ x ∈ P, h x) = f s - h u :=
    eigen_three_side_remainder_sum G f h hAf W a u v u s hhscale hNsW
      (Or.inl rfl) hus.symm havoidS
  have hQ : (∑ x ∈ Q, h x) = f t - h v :=
    eigen_three_side_remainder_sum G f h hAf W a u v v t hhscale hNtW
      (Or.inr rfl) hvt.symm havoidT
  have hPR : P ⊆ R := fun x hx => (Finset.mem_filter.mp hx).1
  have hQR : Q ⊆ R := fun x hx => (Finset.mem_filter.mp hx).1
  have hoverlap : (P ∩ Q).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro x hx y hy
    have hxs := (Finset.mem_filter.mp (Finset.mem_inter.mp hx).1).2
    have hxt := (Finset.mem_filter.mp (Finset.mem_inter.mp hx).2).2
    have hys := (Finset.mem_filter.mp (Finset.mem_inter.mp hy).1).2
    have hyt := (Finset.mem_filter.mp (Finset.mem_inter.mp hy).2).2
    by_contra hxy'
    exact hb4 (unicyclic_double_common_forces_four_cycle G b hG r w hw hlen
      s x t y hst hxy' hxs hxt.symm hys hyt.symm).1
  have hpos : ∀ x ∈ R, 1 ≤ h x := by
    intro x _hx
    have hh : (1 : ℤ) ≤ z x := by have hx := hz x; omega
    change (1 : ℝ) ≤ (z x : ℝ)
    exact_mod_cast hh
  have hinter :
      @Inter.inter (Finset V)
        (@Finset.instInter V (fun x y => Classical.propDecidable (x = y))) P Q = P ∩ Q := by
    ext x
    simp only [Finset.mem_inter]
  have hoverlapClassical :
      (@Inter.inter (Finset V)
        (@Finset.instInter V (fun x y => Classical.propDecidable (x = y))) P Q).card ≤ 1 := by
    rw [hinter]
    exact hoverlap
  obtain ⟨H, hH, hHs, hupper⟩ :=
    two_neighborhood_square_budget P Q R h hPR hQR hpos hoverlapClassical
  rw [hRsum] at hHs hupper
  have hkjR : (K.card : ℝ) + (J.card : ℝ) = 6 := by exact_mod_cast hKJ
  have hjR : (J.card : ℝ) = 6 - (K.card : ℝ) := by linarith only [hkjR]
  have hy : h v = 5 - h u := by linarith only [hxy]
  have hfs' : f s = (9 - (K.card : ℝ)) * h u - 6 := hfs
  have hft' : f t = (9 - (J.card : ℝ)) * h v - 6 := hft
  have hE : (∑ x ∈ P, h x) + (∑ x ∈ Q, h x) =
      6 * h u - 2 + (K.card : ℝ) * (h v - h u) := by
    rw [hP, hQ, hfs', hft', hjR, hy]
    ring
  rw [hE] at hupper
  have horderR : h u ≤ h v := by
    change (z u : ℝ) ≤ (z v : ℝ)
    exact_mod_cast horder
  exact nonfour_scalar_contradiction (h u) (h v) (K.card : ℝ) H
    horderR hxy (Nat.cast_nonneg _) hH hHs hupper
#print axioms Paper7IntroThreeLeafNonfourBudget.three_leaf_nonfour_same_witness_budget_contradiction

end Paper7IntroThreeLeafNonfourBudget
