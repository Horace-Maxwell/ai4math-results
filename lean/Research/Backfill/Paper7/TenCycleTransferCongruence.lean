import Research.Backfill.Paper7.TransferModFourCharacter
import Research.Backfill.Paper7.TwelveCycleUnitRank
import Research.Backfill.Paper7.ZeroGapParity
import Research.Backfill.Paper7.DihedralOrbitBasics

/-! Source-only congruences forced by actual double eigenvalues. Saturated
zero multiplicity supplies the alternating support; it is not postulated
in the eventual graph exclusion. -/
set_option autoImplicit false
noncomputable section
namespace Paper7TenCycle
open BackfillPaper7.Challenge Paper7TransferModFour
open scoped BigOperators Matrix Classical

theorem unit_double_four_dvd_total (p : Fin 10 → ℕ)
    (hm : mult (SG 10 p (fun _ => 0)) 1 = 2) : (4 : ℤ) ∣ ((∑ i, p i : ℕ) : ℤ) := by
  have hid := Paper7MainReduction.qzero_unit_transfer_identity 10 p (by decide) hm
  let l : List ℤ := [1-p 9,1-p 8,1-p 7,1-p 6,1-p 5,1-p 4,1-p 3,1-p 2,1-p 1,1-p 0]
  have hprod : ((l.map (Int.castRingHom ℝ)).map transfer).prod = Mono 10 p (fun _ => 0) 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [l,transfer,Mono,Tk,fk,List.finRange_succ,Matrix.mul_apply,Fin.sum_univ_two]
  have hdiv := integer_transfer_identity_div_four l (hprod.trans hid)
  have hsum : (l.map (fun x => x+1)).sum = 20-((∑ i, p i : ℕ) : ℤ) := by
    norm_num [l,Fin.sum_univ_succ]
    ring
  rw [hsum] at hdiv
  obtain ⟨z,hz⟩ := hdiv
  exact ⟨5-z,by omega⟩
#print axioms Paper7TenCycle.unit_double_four_dvd_total

theorem alternating_double_congruence (p : Fin 10 → ℕ) (m : ℕ) (hm : 0 < m)
    (h1 : p 1 = 0) (h3 : p 3 = 0) (h5 : p 5 = 0) (h7 : p 7 = 0) (h9 : p 9 = 0)
    (hid : Mono 10 p (fun _ => 0) (m : ℝ) = 1) :
    (4 : ℤ) ∣ 5*(m : ℤ)^2-5-((∑ i, p i : ℕ) : ℤ) := by
  let l : List ℤ := [(m : ℤ)^2-p 8-2,(m : ℤ)^2-p 6-2,(m : ℤ)^2-p 4-2,
    (m : ℤ)^2-p 2-2,(m : ℤ)^2-p 0-2]
  let U : Matrix (Fin 2) (Fin 2) ℝ := !![(m : ℝ),0;1,1]
  let V : Matrix (Fin 2) (Fin 2) ℝ := !![1/(m : ℝ),0;-1/(m : ℝ),1]
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
  have hVU : V*U = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [V,U,hm0,Matrix.mul_apply,Fin.sum_univ_two]
  have hfac : U*((l.map (Int.castRingHom ℝ)).map transfer).prod =
      Mono 10 p (fun _ => 0) (m : ℝ)*U := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [U,l,transfer,Mono,Tk,fk,List.finRange_succ,h1,h3,h5,h7,h9,
        Matrix.mul_apply,Fin.sum_univ_two]
    all_goals field_simp [hm0]
    all_goals ring
  have hprod : ((l.map (Int.castRingHom ℝ)).map transfer).prod = 1 := by
    calc
      _ = (V*U)*((l.map (Int.castRingHom ℝ)).map transfer).prod := by rw [hVU,one_mul]
      _ = V*(U*((l.map (Int.castRingHom ℝ)).map transfer).prod) := mul_assoc _ _ _
      _ = V*(Mono 10 p (fun _ => 0) (m : ℝ)*U) := congrArg (fun M => V*M) hfac
      _ = 1 := by rw [hid,one_mul,hVU]
  have hdiv := integer_transfer_identity_div_four l hprod
  have hsum : (l.map (fun x => x+1)).sum =
      5*(m : ℤ)^2-5-((∑ i, p i : ℕ) : ℤ) := by
    norm_num [l,Fin.sum_univ_succ,h1,h3,h5,h7,h9]
    ring
  rwa [hsum] at hdiv
#print axioms Paper7TenCycle.alternating_double_congruence

theorem saturated_rotated_odd_zero (p : Fin 10 → ℕ)
    (hd : delta0 10 p = (Kp 10 p).card) (k : Fin 10) (hk : 0 < p k) :
    p (1+k) = 0 ∧ p (3+k) = 0 ∧ p (5+k) = 0 ∧ p (7+k) = 0 ∧ p (9+k) = 0 := by
  have hr (d : Fin 10) : ((finRotate 10)^d.val) k = d+k := by
    fin_cases d <;> fin_cases k <;> decide
  have hz (d : Fin 10) (hh : Odd d.val) : p (d+k) = 0 := by
    rw [← hr d]
    exact Paper7MainReduction.saturated_zero_gap_odd_rotation 10 p hd d.val k hk hh d.isLt
  exact ⟨hz 1 (by decide),hz 3 (by decide),hz 5 (by decide),
    hz 7 (by decide),hz 9 (by decide)⟩
#print axioms Paper7TenCycle.saturated_rotated_odd_zero

theorem saturated_double_congruence (p : Fin 10 → ℕ) (hp : 0 < ∑ i, p i)
    (hd : delta0 10 p = (Kp 10 p).card) (m : ℕ) (hm : 2 ≤ m)
    (hroot : mult (SG 10 p (fun _ => 0)) (m : ℝ) = 2) :
    (4 : ℤ) ∣ 5*(m : ℤ)^2-5-((∑ i, p i : ℕ) : ℤ) := by
  obtain ⟨k,hk⟩ : ∃ k : Fin 10, 0 < p k := by
    by_contra hh
    push Not at hh
    have hz : ∑ i, p i = 0 := Finset.sum_eq_zero (fun i _ => by have hi := hh i; omega)
    omega
  let σ : Fin 10 → Fin 10 := fun i => i+k
  have hσ : IsDihedral 10 σ := ⟨k,Or.inl (fun _ => rfl)⟩
  obtain ⟨e⟩ := Paper7Setup.sg_iso_of_dihedral 10 p (fun _ => 0)
    (p ∘ σ) (fun _ => 0) (by decide) σ hσ rfl rfl
  have hspec : spec (SG 10 (p ∘ σ) (fun _ => 0)) = spec (SG 10 p (fun _ => 0)) := by
    change ((SG 10 (p ∘ σ) (fun _ => 0)).adjMatrix ℝ).charpoly.roots =
      ((SG 10 p (fun _ => 0)).adjMatrix ℝ).charpoly.roots
    congr 1
    rw [← e.reindex_adjMatrix ℝ]
    exact Matrix.charpoly_reindex e.toEquiv ((SG 10 p (fun _ => 0)).adjMatrix ℝ)
  have hm' : mult (SG 10 (p ∘ σ) (fun _ => 0)) (m : ℝ) = 2 := by
    simpa only [mult,hspec] using hroot
  have hmR : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hid := (Paper7Lemma22Periodic.lemma22_ordinary_clause 10 (p ∘ σ) (fun _ => 0)
    (by decide) (m : ℝ) (by linarith) (by linarith) (by linarith)).2.2.1.mp hm'
  obtain ⟨h1,h3,h5,h7,h9⟩ := saturated_rotated_odd_zero p hd k hk
  have hh := alternating_double_congruence (p ∘ σ) m (by omega) h1 h3 h5 h7 h9 hid
  have hsum : ∑ i, (p ∘ σ) i = ∑ i, p i :=
    (Paper7PruningCanonical.dihedral_bijective 10 (by decide) σ hσ).sum_comp p
  rwa [hsum] at hh
#print axioms Paper7TenCycle.saturated_double_congruence

end Paper7TenCycle
