import Research.Backfill.Paper7.IntroFourExternalMoments
import Research.Backfill.Paper7.IntroPendantFourExclusion

/-! A bare C4 attachment root cannot have even one outside leaf under the
actual integral radius-three bound. Other outside neighbors remain arbitrary. -/
set_option autoImplicit false
noncomputable section
open scoped Classical Matrix

namespace Paper7IntroFourExternal
open Matrix SimpleGraph BackfillPaper7.Challenge Paper7IntroPendantFour

theorem adjacency_single_one
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (v u : V)
    (hv : ∀ j, G.Adj v j ↔ j = u) :
    G.adjMatrix ℝ *ᵥ Pi.single v 1 = Pi.single u 1 := by
  rw [Matrix.mulVec_single_one]
  funext j
  change (if G.Adj j v then (1 : ℝ) else 0) = (Pi.single u (1 : ℝ) : V → ℝ) j
  by_cases hj : j = u
  · subst j
    rw [ite_eq_left ((hv u).mpr rfl).symm, Pi.single_eq_same]
  · have hnot : ¬G.Adj j v := fun h => hj ((hv j).mp h.symm)
    rw [ite_eq_right hnot, Pi.single_eq_of_ne hj]
#print axioms Paper7IntroFourExternal.adjacency_single_one

theorem integral_radius_three_four_root_no_leaf
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hI : IsIntegralGraph G)
    (hbound : ∀ x ∈ spec G, |x| ≤ 3)
    (o a b u v : V) (hab : a ≠ b) (hou : o ≠ u) (hva : v ≠ a) (hvb : v ≠ b)
    (ho : ∀ j, G.Adj o j ↔ j = a ∨ j = b)
    (ha : ∀ j, G.Adj a j ↔ j = o ∨ j = u)
    (hb : ∀ j, G.Adj b j ↔ j = o ∨ j = u)
    (hv : ∀ j, G.Adj v j ↔ j = u) : False := by
  let A := G.adjMatrix ℝ
  let z := fourExternalVector G o u
  let q : ℝ := (G.degree u : ℝ) - 2
  obtain ⟨hz, hza, hzb, hnorm, h2a, h2b⟩ :=
    four_external_vector_data G hI hbound o a b u hab hou ho ha hb
  change radiusThreeFactor A *ᵥ z = 0 at hz
  change z a = 0 at hza
  change z b = 0 at hzb
  change z ⬝ᵥ z = q at hnorm
  change A ^ 2 *ᵥ Pi.single a 1 = 2 • Pi.single a 1 + 2 • Pi.single b 1 + z at h2a
  change A ^ 2 *ᵥ Pi.single b 1 = 2 • Pi.single a 1 + 2 • Pi.single b 1 + z at h2b
  have hm2 := (four_external_vector_moments G hI hbound o a b u hab hou ho ha hb).1
  change z ⬝ᵥ A ^ 2 *ᵥ z = 6 * q at hm2
  have hvo : A *ᵥ Pi.single o 1 = Pi.single a 1 + Pi.single b 1 :=
    adjacency_single_two G o a b hab ho
  have hvone : A *ᵥ Pi.single v 1 = Pi.single u 1 := adjacency_single_one G v u hv
  have hzv : z v = 1 := by
    change (A *ᵥ Pi.single u 1) v - (A *ᵥ Pi.single o 1) v = 1
    rw [hvo, Matrix.mulVec_single_one]
    change (if G.Adj v u then (1 : ℝ) else 0) -
      ((Pi.single a (1 : ℝ) : V → ℝ) v + (Pi.single b (1 : ℝ) : V → ℝ) v) = 1
    rw [ite_eq_left ((hv u).mpr rfl), Pi.single_eq_of_ne hva, Pi.single_eq_of_ne hvb]
    norm_num
  have h2v : A ^ 2 *ᵥ Pi.single v 1 = Pi.single a 1 + Pi.single b 1 + z := by
    change A ^ 2 *ᵥ Pi.single v 1 = Pi.single a 1 + Pi.single b 1 +
      (A *ᵥ Pi.single u 1 - A *ᵥ Pi.single o 1)
    rw [pow_two, ← Matrix.mulVec_mulVec, hvone, hvo]
    funext i
    simp only [Pi.add_apply, Pi.sub_apply]
    ring
  have h2za : (A ^ 2 *ᵥ z) a = q := by
    rw [symmetric_mulVec_coordinate (A ^ 2) (G.isSymm_adjMatrix.pow 2), h2a]
    simp only [add_dotProduct, smul_dotProduct, single_dotProduct,
      smul_eq_mul, hza, hzb, hnorm, mul_zero, zero_add]
  have h2zb : (A ^ 2 *ᵥ z) b = q := by
    rw [symmetric_mulVec_coordinate (A ^ 2) (G.isSymm_adjMatrix.pow 2), h2b]
    simp only [add_dotProduct, smul_dotProduct, single_dotProduct,
      smul_eq_mul, hza, hzb, hnorm, mul_zero, zero_add]
  have h2zv : (A ^ 2 *ᵥ z) v = q := by
    rw [symmetric_mulVec_coordinate (A ^ 2) (G.isSymm_adjMatrix.pow 2), h2v]
    simp only [add_dotProduct, single_dotProduct, one_mul, hza, hzb, hnorm, zero_add]
  have h4zv : (A ^ 4 *ᵥ z) v = 8 * q := by
    rw [show A ^ 4 = A ^ 2 * A ^ 2 from pow_add A 2 2,
      ← Matrix.mulVec_mulVec,
      symmetric_mulVec_coordinate (A ^ 2) (G.isSymm_adjMatrix.pow 2), h2v]
    simp only [add_dotProduct, single_dotProduct, one_mul, h2za, h2zb, hm2]
    change q + q + 6 * q = 8 * q
    ring
  have he : (A ^ 4 *ᵥ z) v - 10 * (A ^ 2 *ᵥ z) v + 9 * z v = 0 := by
    have h := congrFun hz v
    simpa only [radiusThreeFactor, Matrix.add_mulVec, Matrix.sub_mulVec,
      Matrix.smul_mulVec, Matrix.one_mulVec, Pi.add_apply, Pi.sub_apply,
      Pi.smul_apply, smul_eq_mul, Pi.zero_apply] using h
  rw [h4zv, h2zv, hzv] at he
  have hdR : (2 : ℝ) * (G.degree u : ℝ) = 13 := by
    dsimp [q] at he
    linarith
  have hd : 2 * G.degree u = 13 := by exact_mod_cast hdR
  omega
#print axioms Paper7IntroFourExternal.integral_radius_three_four_root_no_leaf

theorem intro21_four_single_attachment_root_no_outside_leaf
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : IsUnicyclicWithCycle G 4) (hI : IsIntegralGraph G)
    (hn : Fintype.card V ≤ 21)
    (S : Set V) (u : S) (e : G.induce S ≃g cycleGraph 4)
    (hboundary : ∀ i ∈ S, ∀ j ∉ S, G.Adj i j → i = u.val)
    (v : V) (hvS : v ∉ S) (huv : G.Adj u.val v) : G.degree v ≠ 1 := by
  intro hdegree
  let f : Fin 4 → V := fun i => (e.symm i).val
  let k : Fin 4 := e u
  have hf : Function.Injective f := by intro i j h; exact e.symm.injective (Subtype.ext h)
  have hroot : f k = u.val := by simp [f, k]
  have hAdj : ∀ i j, (cycleGraph 4).Adj i j ↔ G.Adj (f i) (f j) := by
    intro i j
    exact e.symm.map_rel_iff.symm
  have hout : ∀ i, i ≠ k → ∀ x, x ∉ Set.range f → ¬G.Adj (f i) x := by
    intro i hi x hx hadj
    have hxS : x ∉ S := by
      intro h
      exact hx ⟨e ⟨x, h⟩, by simp [f]⟩
    have he := hboundary (f i) (e.symm i).property x hxS hadj
    exact hi (hf (he.trans hroot.symm))
  have hnbase (i j : Fin 4) : (cycleGraph 4).Adj i j ↔ j = i - 1 ∨ j = i + 1 := by
    change j ∈ (cycleGraph 4).neighborSet i ↔ _
    simp only [SimpleGraph.cycleGraph_neighborSet, Set.mem_insert_iff, Set.mem_singleton_iff]
  have hn1 (j : Fin 4) : (cycleGraph 4).Adj (k + 1) j ↔ j = k + 2 ∨ j = k := by
    rw [hnbase, add_sub_cancel_right,
      show (k + 1) + 1 = k + 2 from by rw [add_assoc]; rfl]
    exact or_comm
  have hn2 (j : Fin 4) : (cycleGraph 4).Adj (k + 2) j ↔ j = k + 1 ∨ j = k + 3 := by
    rw [hnbase, show (k + 2) - 1 = k + 1 from by
      rw [show (2 : Fin 4) = 1 + 1 from rfl, ← add_assoc, add_sub_cancel_right],
      show (k + 2) + 1 = k + 3 from by rw [add_assoc]; rfl]
  have hn3 (j : Fin 4) : (cycleGraph 4).Adj (k + 3) j ↔ j = k + 2 ∨ j = k := by
    rw [hnbase, show (k + 3) - 1 = k + 2 from by
      rw [show (3 : Fin 4) = 2 + 1 from rfl, ← add_assoc, add_sub_cancel_right],
      show (k + 3) + 1 = k from by
        rw [add_assoc]
        change k + 0 = k
        exact add_zero k]
  have h13 : k + 1 ≠ k + 3 := by
    intro h
    have h' : (1 : Fin 4) = 3 := add_left_cancel h
    norm_num at h'
  have hk (i : Fin 4) (hi : i ≠ 0) : k + i ≠ k := by
    intro h
    apply hi
    exact add_left_cancel (show k + i = k + 0 from by simpa only [add_zero] using h)
  have h10 : k + 1 ≠ k := hk 1 (by norm_num)
  have h20 : k + 2 ≠ k := hk 2 (by norm_num)
  have h30 : k + 3 ≠ k := hk 3 (by norm_num)
  have hvf (i : Fin 4) : v ≠ f i := fun h => hvS (h.symm ▸ (e.symm i).property)
  obtain ⟨t, _hvt, huniq⟩ := SimpleGraph.degree_eq_one_iff_existsUnique_adj.mp hdegree
  have hleaf : ∀ j, G.Adj v j ↔ j = f k := by
    intro j
    constructor
    · intro hvj
      exact ((huniq j hvj).trans (huniq u.val huv.symm).symm).trans hroot.symm
    · intro hj
      rw [hj, hroot]
      exact huv.symm
  exact integral_radius_three_four_root_no_leaf G hI
    (Paper7IntroFour.intro21_even_spectrum_abs_le_three G 4 hG hI hn ⟨2, rfl⟩)
    (f (k + 2)) (f (k + 1)) (f (k + 3)) (f k) v
    (fun h => h13 (hf h)) (fun h => h20 (hf h)) (hvf _) (hvf _)
    (embedded_two_neighbors G (cycleGraph 4) f hf hAdj _ _ _ hn2 (hout _ h20))
    (embedded_two_neighbors G (cycleGraph 4) f hf hAdj _ _ _ hn1 (hout _ h10))
    (embedded_two_neighbors G (cycleGraph 4) f hf hAdj _ _ _ hn3 (hout _ h30)) hleaf
#print axioms Paper7IntroFourExternal.intro21_four_single_attachment_root_no_outside_leaf

end Paper7IntroFourExternal
