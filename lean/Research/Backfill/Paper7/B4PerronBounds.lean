import Research.Backfill.Paper7.B4MonodromyRigidity
import Research.Backfill.Paper7.C61PerronDegreeBound

/-! NEW SOURCE ONLY. The Perron root and the strict load bound are conclusions
from the original graph. They are not classification hypotheses. -/
set_option autoImplicit false
noncomputable section
namespace Paper7B4Analytic
open BackfillPaper7.Challenge
open scoped BigOperators Matrix Classical

theorem integral_perron_integer (p q : Fin 4 → ℕ)
    (hp : 0 < ∑ k, (p k+q k)) (hG : IsIntegralGraph (SG 4 p q)) :
    ∃ R : ℕ, 3 ≤ R ∧ (R : ℝ)∈spec (SG 4 p q) ∧
      ∀ x∈spec (SG 4 p q), x ≤ R := by
  obtain ⟨r,hr,_hsimple,hr3,hmax⟩ := (Paper7Admissible.check_Lemma24 4 p q (by decide) hp hG).1
  obtain ⟨z,hz⟩ := Paper7Moments.integral_spec_entry (SG 4 p q) hG r hr
  have hz3 : (3 : ℤ) ≤ z := by rw [hz] at hr3; exact_mod_cast hr3
  have hnat : (z.toNat : ℤ)=z := Int.toNat_of_nonneg (by omega)
  have hreal : (z.toNat : ℝ)=r := by
    have hh : (z.toNat : ℝ)=(z : ℝ) := by exact_mod_cast hnat
    exact hh.trans hz.symm
  refine ⟨z.toNat,by omega,by simpa only [hreal] using hr,?_⟩
  intro x hx
  rw [hreal]
  exact (le_abs_self x).trans (hmax x hx).1
#print axioms Paper7B4Analytic.integral_perron_integer

theorem four_load_strict_bound (p q : Fin 4 → ℕ) (R : ℝ) (hR : 0 ≤ R)
    (hbound : ∀ x∈spec (SG 4 p q), x ≤ R) (k : Fin 4) :
    (2+p k+q k : ℕ) < R^2 := by
  let : Nonempty (SunV 4 (pq 4 p q)) := ⟨Sum.inl 0⟩
  obtain ⟨r,hr,v,hv,_hnorm,he,hr0,_hsimp,_hupper,_hdom⟩ :=
    Paper7Admissible.connected_perron (SG 4 p q)
      (Paper7Admissible.sun_connected 4 (pq 4 p q) (by decide))
  have hle := hbound r hr
  have hcycle1 : (SimpleGraph.cycleGraph 4).Adj k (k+1) := by fin_cases k <;> decide
  have hcycle2 : (SimpleGraph.cycleGraph 4).Adj (k+1) (k+2) := by fin_cases k <;> decide
  have hne : (k+2 : Fin 4)≠k := by fin_cases k <;> decide
  have hij : (SG 4 p q).Adj (Sum.inl k) (Sum.inl (k+1)) :=
    (Paper7Cleared.sun_cycle_adj_iff 4 (pq 4 p q) (by decide) k (k+1)).mpr hcycle1
  have hjw : (SG 4 p q).Adj (Sum.inl (k+1)) (Sum.inl (k+2)) :=
    (Paper7Cleared.sun_cycle_adj_iff 4 (pq 4 p q) (by decide) (k+1) (k+2)).mpr hcycle2
  have hwi : (Sum.inl (k+2) : SunV 4 (pq 4 p q))≠Sum.inl k :=
    fun h => hne (Sum.inl.inj h)
  have hd := Paper7C61Higher.degree_lt_eigenvalue_sq (SG 4 p q) r v hv he _ _ _ hij hjw hwi
  rw [Paper7Setup.sg_root_degree 4 p q (by decide) k] at hd
  have hsq : r^2 ≤ R^2 := by nlinarith
  exact hd.trans_le hsq
#print axioms Paper7B4Analytic.four_load_strict_bound

theorem integral_perron_load_data (p q : Fin 4 → ℕ)
    (hp : 0 < ∑ k, (p k+q k)) (hG : IsIntegralGraph (SG 4 p q)) :
    ∃ R : ℕ, 3 ≤ R ∧ (R : ℝ)∈spec (SG 4 p q) ∧
      (∀ x∈spec (SG 4 p q), x ≤ R) ∧ (∀ k, p k+q k+3 ≤ R^2) := by
  obtain ⟨R,hR,hmem,hbound⟩ := integral_perron_integer p q hp hG
  refine ⟨R,hR,hmem,hbound,?_⟩
  intro k
  have hd := four_load_strict_bound p q R (Nat.cast_nonneg R) hbound k
  have hdN : 2+p k+q k < R^2 := by exact_mod_cast hd
  omega
#print axioms Paper7B4Analytic.integral_perron_load_data

end Paper7B4Analytic
