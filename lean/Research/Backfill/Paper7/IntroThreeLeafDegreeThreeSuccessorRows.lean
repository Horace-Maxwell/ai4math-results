import Research.Backfill.Paper7.IntroPerronTwoNeighborRows
import Research.Backfill.Paper7.IntroThreeLeafDegreeThreeExternalLeaves
import Research.Backfill.Paper7.IntroUnicyclicCycleCompleteNeighbors

/-! One actual integer Perron witness supplies both successor rows.
Only already proved complete internal cycle neighborhoods are used;
no four-cycle, common-neighbor or fourth-moment result is assumed. -/
set_option autoImplicit false
noncomputable section
open scoped Classical Matrix BigOperators

namespace Paper7IntroThreeLeafSuccessors
open SimpleGraph Matrix BackfillPaper7.Challenge Paper7OddIntegral
open BackfillPaper7.Challenge.Legacy.Algebra
open Paper7IntroProjectors Paper7IntroThreeLeafExternal Paper7IntroCycleCompleteNeighbors

theorem intro21_even_three_leaf_degree_three_successor_rows
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
        f t = (9 - (J.card : ℝ)) * (z v : ℝ) - 6 := by
  obtain ⟨Y, i₀, eps, f, z, hY, hmY, hda, hne, hdata, hcover, hNa, hNl,
    hs, hflip, hf, hAf, h₀, hweights, ha, hc, hsgn, hcs, hproj, hN, hz,
    hsame, hopp, hsumU, hsumW, hexternal⟩ :=
    intro21_even_three_leaf_degree_three_external_leaves G b hG hI hn hb
      r w hw hlen C a c hac hm hd
  refine ⟨Y, i₀, eps, f, z, hY, hmY, hda, hne, hdata, hcover, hNa, hNl,
    hs, hflip, hf, hAf, h₀, hweights, ha, hc, hsgn, hcs, hproj, hN, hz,
    hsame, hopp, hsumU, hsumW, hexternal, ?_⟩
  obtain ⟨u, v, hu, hv, huv, hcu, hcv, hfullc⟩ :=
    unicyclic_cycle_two_neighbors_complete G b hG r w hw hlen c.val c.property
  have hau : a.val.val ≠ u := by
    intro he
    apply a.val.property
    rw [he]
    exact hu
  have hav : a.val.val ≠ v := by
    intro he
    apply a.val.property
    rw [he]
    exact hv
  have hNc : G.neighborFinset c.val = {a.val.val, u, v} :=
    degree_three_neighbor_finset G c.val a.val.val u v hd hau hav huv hac.symm hcu hcv
  have hcsame : eps c.val = eps i₀.val := by linarith only [hcs, hsgn i₀]
  have huW : eps u = -eps i₀.val := by linarith only [hflip c.val u hcu, hcsame]
  have hvW : eps v = -eps i₀.val := by linarith only [hflip c.val v hcv, hcsame]
  have haUV : a.val.val ∉ ({u, v} : Finset V) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨hau, hav⟩
  have hrowc : f a.val.val + (f u + f v) = 3 * f c.val := by
    simpa only [G.adjMatrix_mulVec_apply, hNc, Finset.sum_insert haUV,
      Finset.sum_pair huv, Pi.smul_apply, smul_eq_mul] using congrFun hAf c.val
  have hsumR : (z u : ℝ) + (z v : ℝ) = 5 := by
    rw [ha, hc, hopp u huW, hopp v hvW] at hrowc
    linarith only [hrowc]
  have hsumZ : z u + z v = 5 := by exact_mod_cast hsumR
  have hnext (d : V) (hdcycle : d ∈ w.support) (hdW : eps d = -eps i₀.val)
      (hdc : G.Adj d c.val) :
      ∃ (s : V) (K : Finset V),
        s ∈ w.support ∧ s ≠ c.val ∧ G.Adj d s ∧
        (∀ q, q ∈ w.support → (G.Adj d q ↔ q = c.val ∨ q = s)) ∧
        K = ((G.neighborFinset d).erase c.val).erase s ∧
        (∀ x, x ∈ K ↔ G.Adj d x ∧ x ∉ w.support) ∧
        G.neighborFinset d = insert c.val (insert s K) ∧
        (∀ x ∈ K, G.neighborFinset x = {d} ∧
          (∀ q, G.Adj x q ↔ q = d) ∧ G.degree x = 1 ∧ f x = (z d : ℝ)) ∧
        (∑ x ∈ K, f x) = (K.card : ℝ) * (z d : ℝ) ∧
        f s = (9 - (K.card : ℝ)) * (z d : ℝ) - 6 := by
    obtain ⟨s, hscycle, hsc, hds, hfull⟩ :=
      unicyclic_cycle_neighbor_continuation G b hG r w hw hlen
        d c.val hdcycle c.property hdc
    let K := ((G.neighborFinset d).erase c.val).erase s
    have hK : ∀ x, x ∈ K ↔ G.Adj d x ∧ x ∉ w.support := by
      intro x
      constructor
      · intro hx
        have hxs := (Finset.mem_erase.mp hx).1
        have hinner := Finset.mem_erase.mp (Finset.mem_erase.mp hx).2
        have hdx := (G.mem_neighborFinset d x).mp hinner.2
        refine ⟨hdx, ?_⟩
        intro hxcycle
        rcases (hfull x hxcycle).mp hdx with hxc | hxs'
        · exact hinner.1 hxc
        · exact hxs hxs'
      · rintro ⟨hdx, hxout⟩
        have hxc : x ≠ c.val := by
          intro he
          apply hxout
          rw [he]
          exact c.property
        have hxs : x ≠ s := by
          intro he
          apply hxout
          rw [he]
          exact hscycle
        exact Finset.mem_erase.mpr ⟨hxs,
          Finset.mem_erase.mpr ⟨hxc, (G.mem_neighborFinset d x).mpr hdx⟩⟩
    have hcN : c.val ∈ G.neighborFinset d := (G.mem_neighborFinset d c.val).mpr hdc
    have hsN : s ∈ (G.neighborFinset d).erase c.val :=
      Finset.mem_erase.mpr ⟨hsc, (G.mem_neighborFinset d s).mpr hds⟩
    have hNd : G.neighborFinset d = insert c.val (insert s K) := by
      dsimp [K]
      rw [Finset.insert_erase hsN, Finset.insert_erase hcN]
    have hleaf : ∀ x ∈ K, G.neighborFinset x = {d} ∧
        (∀ q, G.Adj x q ↔ q = d) ∧ G.degree x = 1 ∧ f x = (z d : ℝ) := by
      intro x hx
      have hi := (hK x).mp hx
      obtain ⟨_herase, hsingle, hneighbor, hdegree, hweight⟩ :=
        hexternal d hdcycle hdW x hi.2 hi.1.symm
      exact ⟨hsingle, hneighbor, hdegree, hweight⟩
    have hsumK : (∑ x ∈ K, f x) = (K.card : ℝ) * (z d : ℝ) := by
      calc
        _ = ∑ _x ∈ K, (z d : ℝ) :=
          Finset.sum_congr rfl (fun x hx => (hleaf x hx).2.2.2)
        _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]
    have hrow := eigen_three_two_neighbor_erase_sum G f hAf d c.val s hsc.symm hdc hds
    change (∑ x ∈ K, f x) + f s + f c.val = 3 * f d at hrow
    rw [hsumK, hc, hopp d hdW] at hrow
    have hfs : f s = (9 - (K.card : ℝ)) * (z d : ℝ) - 6 := by
      nlinarith only [hrow]
    exact ⟨s, K, hscycle, hsc, hds, hfull, rfl, hK, hNd, hleaf, hsumK, hfs⟩
  obtain ⟨s, K, hsC, hsc, hus, hfullu, hK, hKmem, hNu, hKleaf, hKsum, hfs⟩ :=
    hnext u hu huW hcu.symm
  obtain ⟨t, J, htC, htc, hvt, hfullv, hJ, hJmem, hNv, hJleaf, hJsum, hft⟩ :=
    hnext v hv hvW hcv.symm
  exact ⟨u, v, s, t, K, J, hu, hv, huv, hcu, hcv, hNc, hfullc, huW, hvW, hsumZ,
    hsC, hsc, hus, hfullu, htC, htc, hvt, hfullv, hK, hJ, hKmem, hJmem,
    hNu, hNv, hKleaf, hJleaf, hKsum, hJsum, hfs, hft⟩
#print axioms Paper7IntroThreeLeafSuccessors.intro21_even_three_leaf_degree_three_successor_rows

end Paper7IntroThreeLeafSuccessors
