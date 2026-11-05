import Research.Backfill.Paper7.IntroTerminalFourParentVector
import Research.Backfill.Paper7.IntroBridgeCubicEntry
import Research.Backfill.Paper7.IntroFourExternalVector

/-! A second terminal fan two edges beyond the parent of a degree-four
terminal forces an exact degree sum. The graph outside these actual vertices
is unrestricted; all bridge and leaf conditions remain explicit. -/
set_option autoImplicit false
noncomputable section
open scoped Classical Matrix BigOperators

namespace Paper7IntroTerminalFourRemote
open Matrix SimpleGraph BackfillPaper7.Challenge
open Paper7IntroLocalQuartic Paper7IntroPendantFour Paper7IntroFourExternal

theorem integral_terminal_four_remote_fan_degree_sum
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hI : IsIntegralGraph G)
    (hbound : ∀ t ∈ spec G, |t| ≤ 3)
    (x p y z : V) (hxp : G.Adj x p) (hx : G.degree x = 4)
    (hxleaf : ∀ j, G.Adj x j → j ≠ p → G.degree j = 1)
    (hpy : G.Adj p y) (hyx : y ≠ x) (hyz : G.Adj y z) (hzp : z ≠ p)
    (hz : 2 ≤ G.degree z)
    (hzleaf : ∀ j, G.Adj z j → j ≠ y → G.degree j = 1)
    (hpbridge : ∀ j, G.Adj p j → G.IsBridge s(p, j))
    (hybridge : ∀ j, G.Adj y j → G.IsBridge s(y, j)) :
    G.degree p + G.degree y + G.degree z = 13 := by
  let A := G.adjMatrix ℝ
  let u : V → ℝ := A *ᵥ Pi.single p 1 - Pi.single x 1
  have hA : A.IsSymm := G.isSymm_adjMatrix
  have hF : radiusThreeFactor A *ᵥ u = 0 :=
    integral_terminal_four_parent_vector_annihilated G hI hbound x p hxp hx hxleaf
  have hpz : (A ^ 2) p z = 1 :=
    bridge_vertex_square_common_neighbor_one G p hpbridge z y hzp hpy hyz
  have hzpentry : (A ^ 2) z p = 1 := ((hA.pow 2).apply p z).trans hpz
  have hyxentry : (A ^ 2) y x = 1 :=
    bridge_vertex_square_common_neighbor_one G y hybridge x p hyx.symm hpy.symm hxp.symm
  have hcube : (A ^ 3) y p = (G.degree y : ℝ) + (G.degree p : ℝ) - 1 :=
    bridge_vertex_cube_neighbor_entry G y hybridge p hpy.symm
  have hzx : ¬ G.Adj z x := by
    intro h
    have hd := hxleaf z h.symm hzp
    omega
  have hzxentry : A z x = 0 := by
    change (if G.Adj z x then (1 : ℝ) else 0) = 0
    exact ite_eq_right hzx
  have hAuxz : (A *ᵥ u) z = 1 := by
    change (A *ᵥ (A *ᵥ Pi.single p 1 - Pi.single x 1)) z = 1
    rw [Matrix.mulVec_sub, Matrix.mulVec_mulVec, ← pow_two,
      Matrix.mulVec_single_one, Matrix.mulVec_single_one]
    change (A ^ 2) z p - A z x = 1
    rw [hzpentry, hzxentry, sub_zero]
  have hBuy : (A ^ 2 *ᵥ u) y = (G.degree p : ℝ) + (G.degree y : ℝ) - 2 := by
    change (A ^ 2 *ᵥ (A *ᵥ Pi.single p 1 - Pi.single x 1)) y = _
    rw [Matrix.mulVec_sub, Matrix.mulVec_mulVec, ← pow_succ,
      Matrix.mulVec_single_one, Matrix.mulVec_single_one]
    change (A ^ 3) y p - (A ^ 2) y x = _
    rw [hcube, hyxentry]
    ring
  have hyN : y ∈ G.neighborFinset z := (G.mem_neighborFinset z y).mpr hyz.symm
  have hEpos : 0 < ((G.neighborFinset z).erase y).card := by
    rw [Finset.card_erase_of_mem hyN, G.card_neighborFinset_eq_degree]
    omega
  obtain ⟨l, hl⟩ := Finset.card_pos.mp hEpos
  have hly : l ≠ y := (Finset.mem_erase.mp hl).1
  have hzl : G.Adj z l := (G.mem_neighborFinset z l).mp (Finset.mem_erase.mp hl).2
  have hldeg : G.degree l = 1 := hzleaf l hzl hly
  obtain ⟨_k, _hlk, huniq⟩ := SimpleGraph.degree_eq_one_iff_existsUnique_adj.mp hldeg
  have hlrow : ∀ j, G.Adj l j ↔ j = z := by
    intro j
    constructor
    · intro hlj
      exact (huniq j hlj).trans (huniq z hzl.symm).symm
    · intro hjz
      exact hjz.symm ▸ hzl.symm
  have hlcol : A *ᵥ Pi.single l 1 = Pi.single z 1 := by
    funext j
    rw [Matrix.mulVec_single_one]
    change (if G.Adj j l then (1 : ℝ) else 0) = (Pi.single z (1 : ℝ) : V → ℝ) j
    by_cases hjz : j = z
    · subst j
      rw [ite_eq_left hzl, Pi.single_eq_same]
    · rw [ite_eq_right (fun h => hjz ((hlrow j).mp h.symm)),
        Pi.single_eq_of_ne (M := fun _ : V => ℝ) hjz (1 : ℝ)]
  have hleafrow (v : V → ℝ) : (A *ᵥ v) l = v z := by
    rw [symmetric_mulVec_coordinate A hA, hlcol, single_one_dotProduct]
  have hlx : l ≠ x := by
    intro he
    rw [he, hx] at hldeg
    omega
  have hlp : ¬ G.Adj l p := by
    intro h
    exact hzp ((hlrow p).mp h).symm
  have hul : u l = 0 := by
    change (A *ᵥ Pi.single p 1) l - (Pi.single x (1 : ℝ) : V → ℝ) l = 0
    rw [Matrix.mulVec_single_one, Pi.single_eq_of_ne hlx]
    change (if G.Adj l p then (1 : ℝ) else 0) - 0 = 0
    rw [ite_eq_right hlp, sub_self]
  have h2l : (A ^ 2 *ᵥ u) l = 1 := by
    rw [pow_two, ← Matrix.mulVec_mulVec, hleafrow, hAuxz]
  have hzcol : A ^ 2 *ᵥ Pi.single z 1 = A *ᵥ Pi.single y 1 +
      (((G.degree z - 1 : ℕ) : ℝ)) • Pi.single z 1 :=
    terminal_fan_square_column G z y hyz.symm hzleaf
  have hdot : (A *ᵥ Pi.single y 1) ⬝ᵥ (A *ᵥ u) = (A ^ 2 *ᵥ u) y := by
    calc
      _ = (A *ᵥ (A *ᵥ u)) y := (symmetric_mulVec_coordinate A hA (A *ᵥ u) y).symm
      _ = _ := by rw [Matrix.mulVec_mulVec, ← pow_two]
  have hzR : (((G.degree z - 1 : ℕ) : ℝ)) = (G.degree z : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega), Nat.cast_one]
  have h3z : (A ^ 3 *ᵥ u) z =
      (G.degree p : ℝ) + (G.degree y : ℝ) + (G.degree z : ℝ) - 3 := by
    rw [show A ^ 3 = A ^ 2 * A from pow_succ A 2, ← Matrix.mulVec_mulVec,
      symmetric_mulVec_coordinate (A ^ 2) (hA.pow 2), hzcol, add_dotProduct,
      smul_dotProduct, single_one_dotProduct, smul_eq_mul, hdot, hBuy, hAuxz, hzR]
    ring
  have h4l : (A ^ 4 *ᵥ u) l =
      (G.degree p : ℝ) + (G.degree y : ℝ) + (G.degree z : ℝ) - 3 := by
    rw [show A ^ 4 = A * A ^ 3 from pow_succ' A 3,
      ← Matrix.mulVec_mulVec, hleafrow, h3z]
  have he : (A ^ 4 *ᵥ u) l - 10 * (A ^ 2 *ᵥ u) l + 9 * u l = 0 := by
    simpa only [radiusThreeFactor, Matrix.add_mulVec, Matrix.sub_mulVec,
      Matrix.smul_mulVec, Matrix.one_mulVec, Pi.add_apply, Pi.sub_apply,
      Pi.smul_apply, smul_eq_mul, Pi.zero_apply] using congrFun hF l
  rw [h4l, h2l, hul] at he
  have hsum : (G.degree p : ℝ) + (G.degree y : ℝ) + (G.degree z : ℝ) = 13 := by linarith
  exact_mod_cast hsum
#print axioms Paper7IntroTerminalFourRemote.integral_terminal_four_remote_fan_degree_sum

end Paper7IntroTerminalFourRemote
