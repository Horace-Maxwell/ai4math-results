import Research.Backfill.Paper7.C61SmallProfileLedger
import Research.Backfill.Paper7.SunPerron
import Research.Backfill.Paper7.SunDegrees

set_option autoImplicit false
noncomputable section
namespace Paper7C61Higher
open Matrix SimpleGraph BackfillPaper7.Challenge
open Paper7C61Profile Paper7C61Small
open scoped BigOperators Classical

/-- A positive Perron vector and a real length-two continuation force the
strict star bound at its initial vertex. No graph classification is used. -/
theorem degree_lt_eigenvalue_sq {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (r : ℝ) (v : V → ℝ)
    (hv : ∀ i, 0 < v i) (he : G.adjMatrix ℝ *ᵥ v = r • v)
    (i j w : V) (hij : G.Adj i j) (hjw : G.Adj j w) (hwi : w ≠ i) :
    (G.degree i : ℝ) < r^2 := by
  have hrow (k : V) : (∑ x ∈ G.neighborFinset k, v x) = r*v k := by
    simpa only [SimpleGraph.adjMatrix_mulVec_apply,Pi.smul_apply,smul_eq_mul] using congrFun he k
  have hneighbor (k : V) (hk : k ∈ G.neighborFinset i) : v i ≤ r*v k := by
    have hi : i ∈ G.neighborFinset k := (G.mem_neighborFinset k i).mpr
      ((G.mem_neighborFinset i k).mp hk).symm
    have hs := Finset.single_le_sum (fun x _ => (hv x).le) hi
    rwa [hrow k] at hs
  have hji : i ∈ G.neighborFinset j := (G.mem_neighborFinset j i).mpr hij.symm
  have hjw' : w ∈ G.neighborFinset j := (G.mem_neighborFinset j w).mpr hjw
  have hi' : i ∈ (G.neighborFinset j).erase w := Finset.mem_erase.mpr ⟨Ne.symm hwi,hji⟩
  have hs := Finset.single_le_sum (fun x _ => (hv x).le) hi'
  have hsum := Finset.sum_erase_add (G.neighborFinset j) v hjw'
  rw [hrow j] at hsum
  have hstrict : v i < r*v j := by linarith [hv w]
  have hj : j ∈ G.neighborFinset i := (G.mem_neighborFinset i j).mpr hij
  have htotal := Finset.sum_lt_sum hneighbor ⟨j,hj,hstrict⟩
  have hineq : (G.degree i : ℝ)*v i < r^2*v i := by
    calc
      (G.degree i : ℝ)*v i = ∑ k ∈ G.neighborFinset i, v i := by
        simp only [Finset.sum_const,SimpleGraph.card_neighborFinset_eq_degree,nsmul_eq_mul]
      _ < ∑ k ∈ G.neighborFinset i, r*v k := htotal
      _ = r*(∑ k ∈ G.neighborFinset i, v k) := (Finset.mul_sum _ _ _).symm
      _ = r*(r*v i) := by rw [hrow i]
      _ = r^2*v i := by ring
  exact (mul_lt_mul_iff_left₀ (hv i)).mp hineq
#print axioms Paper7C61Higher.degree_lt_eigenvalue_sq

theorem spectrum_upper_from_profile (p q : Fin 6 → ℕ) (hn : nOf 6 p q ≤ 42)
    (hG : IsIntegralGraph (SG 6 p q)) (R : ℝ) (hR : 2 ≤ R)
    (hprofile : ∀ i : Fin 5, 0 < (actual p q i).val → (value i : ℝ) ≤ R) :
    ∀ x ∈ spec (SG 6 p q), x ≤ R := by
  intro x hx
  by_cases h2 : 2 ≤ x
  · have hmem : x ∈ Bplus (SG 6 p q) := Multiset.mem_filter.mpr ⟨hx,h2⟩
    obtain ⟨i,hi⟩ := bplus_covered p q hn hG x hmem
    have hpos : 0 < (actual p q i).val := by
      rw [actual_eq_mult,hi]
      exact Multiset.count_pos.mpr hx
    rw [← hi]
    exact hprofile i hpos
  · linarith
#print axioms Paper7C61Higher.spectrum_upper_from_profile

theorem sun_load_lt_sq_sub_two (p q : Fin 6 → ℕ) (R : ℝ) (hR : 0 ≤ R)
    (hbound : ∀ x ∈ spec (SG 6 p q), x ≤ R) (k : Fin 6) :
    (2+p k+q k : ℕ) < R^2 := by
  let : Nonempty (SunV 6 (pq 6 p q)) := ⟨Sum.inl 0⟩
  obtain ⟨r,hr,v,hv,_hnorm,he,hr0,_hsimp,_hupper,_hdom⟩ :=
    Paper7Admissible.connected_perron (SG 6 p q)
      (Paper7Admissible.sun_connected 6 (pq 6 p q) (by decide))
  have hle := hbound r hr
  have hcycle1 : (SimpleGraph.cycleGraph 6).Adj k (k+1) := by fin_cases k <;> decide
  have hcycle2 : (SimpleGraph.cycleGraph 6).Adj (k+1) (k+2) := by fin_cases k <;> decide
  have hne : (k+2 : Fin 6) ≠ k := by fin_cases k <;> decide
  have hij : (SG 6 p q).Adj (Sum.inl k) (Sum.inl (k+1)) :=
    (Paper7Cleared.sun_cycle_adj_iff 6 (pq 6 p q) (by decide) k (k+1)).mpr hcycle1
  have hjw : (SG 6 p q).Adj (Sum.inl (k+1)) (Sum.inl (k+2)) :=
    (Paper7Cleared.sun_cycle_adj_iff 6 (pq 6 p q) (by decide) (k+1) (k+2)).mpr hcycle2
  have hwi : (Sum.inl (k+2) : SunV 6 (pq 6 p q)) ≠ Sum.inl k :=
    fun h => hne (Sum.inl.inj h)
  have hd := degree_lt_eigenvalue_sq (SG 6 p q) r v hv he _ _ _ hij hjw hwi
  rw [Paper7Setup.sg_root_degree 6 p q (by decide) k] at hd
  have hsq : r^2 ≤ R^2 := by nlinarith
  exact hd.trans_le hsq
#print axioms Paper7C61Higher.sun_load_lt_sq_sub_two

theorem root_four_load_le_thirteen (p q : Fin 6 → ℕ)
    (hn : nOf 6 p q ≤ 42) (hG : IsIntegralGraph (SG 6 p q))
    (h4 : RootFour (actual p q)) : ∀ k, p k+q k ≤ 13 := by
  obtain ⟨_h2,h3,h4⟩ := h4
  have hb := spectrum_upper_from_profile p q hn hG 4 (by norm_num) (by
    intro i hi
    fin_cases i
    · norm_num [value]
    · norm_num [value]
    · norm_num [value]
    · change 0 < (actual p q 3).val at hi
      rw [h3] at hi; omega
    · change 0 < (actual p q 4).val at hi
      rw [h4] at hi; omega)
  intro k
  have hd := sun_load_lt_sq_sub_two p q 4 (by norm_num) hb k
  norm_num at hd
  have hnat : 2+p k+q k < 16 := by exact_mod_cast hd
  omega
#print axioms Paper7C61Higher.root_four_load_le_thirteen

theorem no_six_load_le_twenty_two (p q : Fin 6 → ℕ)
    (hn : nOf 6 p q ≤ 42) (hG : IsIntegralGraph (SG 6 p q))
    (h4 : (actual p q 4).val = 0) : ∀ k, p k+q k ≤ 22 := by
  have hb := spectrum_upper_from_profile p q hn hG 5 (by norm_num) (by
    intro i hi
    fin_cases i
    · norm_num [value]
    · norm_num [value]
    · norm_num [value]
    · norm_num [value]
    · change 0 < (actual p q 4).val at hi
      rw [h4] at hi; omega)
  intro k
  have hd := sun_load_lt_sq_sub_two p q 5 (by norm_num) hb k
  norm_num at hd
  have hnat : 2+p k+q k < 25 := by exact_mod_cast hd
  omega
#print axioms Paper7C61Higher.no_six_load_le_twenty_two

end Paper7C61Higher
