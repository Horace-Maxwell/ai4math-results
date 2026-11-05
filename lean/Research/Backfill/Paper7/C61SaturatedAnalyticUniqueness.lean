import Research.Backfill.Paper7.C61DoubleRootMonodromy
import Research.Backfill.Paper7.C61SaturatedParameters

/-! NEW SOURCE ONLY. The saturated original branch is classified by two
actual repeated-root monodromies, with no finite-row certificate premise. -/
set_option autoImplicit false
noncomputable section
namespace Paper7C61Four
open BackfillPaper7.Challenge
open Paper7C61Profile Paper7C61Parameters Paper7C61Orbit
open scoped BigOperators Classical

theorem opposite_coordinates_zero_rotations (p : Fin 6 → ℕ)
    (h : ∀ k : Fin 6, p k+p (k+3) = 12 ∧
      p k*p (k+1)+p (k+3)*p (k+4) = 72)
    (hz : ∃ j, p j = 0) : p ∈ C61Rotations := by
  obtain ⟨j,hj⟩ := hz
  have h3 : p (j+3) = 12 := by have hi := (h j).1; omega
  have h4 : p (j+4) = 6 := by
    have hi := (h j).2
    rw [hj,h3] at hi
    omega
  have h1 : p (j+1) = 6 := by
    have hi := (h (j+1)).1
    simp only [add_assoc,show (1 : Fin 6)+3 = 4 from rfl] at hi
    omega
  have h2 : p (j+2) = 6 := by
    have hi := (h (j+2)).2
    simp only [add_assoc,show (2 : Fin 6)+1 = 3 from rfl,
      show (2 : Fin 6)+3 = 5 from rfl,show (2 : Fin 6)+4 = 0 from rfl,add_zero] at hi
    rw [h3,hj] at hi
    omega
  have h5 : p (j+5) = 6 := by
    have hi := (h (j+2)).1
    simp only [add_assoc,show (2 : Fin 6)+3 = 5 from rfl] at hi
    omega
  have hp : ∀ k : Fin 6, p (k+j) = C61P k := by
    intro k
    fin_cases k
    · simpa [C61P] using hj
    · simpa [C61P,add_comm] using h1
    · simpa [C61P,add_comm] using h2
    · simpa [C61P,add_comm] using h3
    · simpa [C61P,add_comm] using h4
    · simpa [C61P,add_comm] using h5
  apply (mem_rotations_iff p).mpr
  refine ⟨-j,?_⟩
  funext k
  have hi := hp (k-j)
  simpa only [sub_eq_add_neg,rotationParameter,add_assoc,neg_add_cancel,add_zero] using hi
#print axioms Paper7C61Four.opposite_coordinates_zero_rotations

theorem saturated_rotations_analytic (p q : Fin 6 → ℕ)
    (hp : 0 < ∑ k, (p k+q k)) (hn : nOf 6 p q ≤ 42)
    (hG : IsIntegralGraph (SG 6 p q)) (hc : card (actual p q) = 5) :
    q = (fun _ => 0) ∧ p ∈ C61Rotations := by
  obtain ⟨hq,_hP,_hS,hK⟩ := saturated_parameter_data p q hp hn hG hc
  have hm := (saturated_profile_parameters p q hp hn hG hc).1
  have h2 : (actual p q 0).val = 2 := by rw [hm]; rfl
  have h3 : (actual p q 1).val = 2 := by rw [hm]; rfl
  have hcoords := double_two_three_qzero_coordinates p q hq h2 h3
  obtain ⟨j,hj,_huniq⟩ := unique_zero_of_support_five p hK
  exact ⟨hq,opposite_coordinates_zero_rotations p hcoords ⟨j,hj⟩⟩
#print axioms Paper7C61Four.saturated_rotations_analytic

end Paper7C61Four
