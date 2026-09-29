import Research.Backfill.Paper4.Challenge

/-!
Paper4 finite connected graph metrics and the exact frozen reading conventions.
This source alone makes no compilation or acceptance claim; separate evidence
must establish the complete target checks, axiom audit, checker and fresh replay.
Frozen Challenge SHA: 9f1b0c95f35addf03f54c330ea0cd63324154d17e1cc8e707c8bf830da4a0785.
-/
set_option autoImplicit false
noncomputable section
namespace CodexPaper4
open BackfillPaper4 SimpleGraph Finset
namespace MetricBounds

variable {V : Type*} [Fintype V] (G : SimpleGraph V)

lemma triDist_le_triameter (u v w : V) :
    Challenge.triDist G u v w ≤ Challenge.triameter G :=
  Finset.le_sup (f := fun t : V × V × V => Challenge.triDist G t.1 t.2.1 t.2.2)
    (Finset.mem_univ (u, v, w))

lemma dist_le_diameter (hc : G.Connected) (u v : V) : G.dist u v ≤ G.diam := by
  have : Nonempty V := hc.nonempty
  exact SimpleGraph.dist_le_diam (connected_iff_ediam_ne_top.mp hc)

omit [Fintype V] in
lemma triDist_pair_lower (hc : G.Connected) {x y : V}
    (hxy : Challenge.IsDiametral G x y) (z : V) :
    2 * G.diam ≤ Challenge.triDist G x y z := by
  have ht := hc.dist_triangle (u := x) (v := z) (w := y)
  rw [G.dist_comm (u := z) (v := y)] at ht
  change G.dist x y = G.diam at hxy
  unfold Challenge.triDist
  omega

omit [Fintype V] in
lemma triDist_repeated (u v : V) : Challenge.triDist G u u v = 2 * G.dist u v := by
  simp [Challenge.triDist, two_mul]

lemma two_diam_le_triameter (hc : G.Connected) : 2 * G.diam ≤ Challenge.triameter G := by
  have : Nonempty V := hc.nonempty
  obtain ⟨u, v, huv⟩ := G.exists_dist_eq_diam
  have h := triDist_le_triameter G u u v
  rwa [triDist_repeated, huv] at h

lemma triameter_le_three_diam (hc : G.Connected) : Challenge.triameter G ≤ 3 * G.diam := by
  unfold Challenge.triameter
  apply Finset.sup_le
  rintro ⟨u, v, w⟩ _
  have h1 := dist_le_diameter G hc u v
  have h2 := dist_le_diameter G hc u w
  have h3 := dist_le_diameter G hc v w
  change G.dist u v + G.dist u w + G.dist v w ≤ 3 * G.diam
  omega

end MetricBounds

theorem check_Sec2_bounds : Challenge.Sec2_bounds := by
  intro V _ G hc
  exact ⟨MetricBounds.two_diam_le_triameter G hc,
    MetricBounds.triameter_le_three_diam G hc,
    fun x y z hxy => MetricBounds.triDist_pair_lower G hc hxy z⟩

#print axioms check_Sec2_bounds
end CodexPaper4
