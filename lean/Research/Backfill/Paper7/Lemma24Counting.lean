import Research.Backfill.Paper7.EvenSunSpectrum
import Research.Backfill.Paper7.IntegralSquareCounts
import Research.Backfill.Paper7.Identities12
import Research.Backfill.Paper7.Lemma22

/-! The complete (c) branches use only the frozen hypotheses and accepted
multiplicity and moment results. There is no Perron hypothesis in this file. -/
set_option autoImplicit false
noncomputable section
namespace Paper7Admissible
open BackfillPaper7.Challenge

theorem lemma24_big_square_lower (b : ℕ) (p q : Fin b → ℕ) (hb : 3 ≤ b)
    (hG : IsIntegralGraph (SG b p q)) :
    ((∑ k, p k + ∑ k, q k : ℕ) : ℝ) ≤
      (1 / 2) * ((bigEigs (SG b p q)).map (fun x => x ^ 2)).sum - b + 2 := by
  have hsum := graph_square_partition (SG b p q) hG
  rw [Paper7SunMoments.sg_second_moment b p q hb] at hsum
  have hbounds := (Paper7Lemma22.check_Lemma22 b p q hb).2.2.2
  have hp : (mult (SG b p q) 1 : ℝ) ≤ (max (∑ k, q k) 2 : ℕ) := by
    exact_mod_cast hbounds.2.1
  have hn : (mult (SG b p q) (-1) : ℝ) ≤ (max (∑ k, q k) 2 : ℕ) := by
    exact_mod_cast hbounds.2.2
  have hmax : (max (∑ k, q k) 2 : ℕ) ≤ (∑ k, q k) + 2 := by omega
  have hmaxR : ((max (∑ k, q k) 2 : ℕ) : ℝ) ≤ (∑ k, q k : ℕ) + 2 := by
    exact_mod_cast hmax
  simp only [nOf, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] at hsum ⊢
  linarith

theorem lemma24_counting_even (b : ℕ) (p q : Fin b → ℕ) (hb : 3 ≤ b)
    (hG : IsIntegralGraph (SG b p q)) (he : Even b) :
    (∀ x : ℝ, mult (SG b p q) x = mult (SG b p q) (-x)) ∧
    S2 (SG b p q) = (nOf b p q : ℝ) - mult (SG b p q) 1 ∧
    ((∑ k, p k + ∑ k, q k : ℕ) : ℝ) ≤ S2 (SG b p q) - b + 2 := by
  have hsym : ∀ x : ℝ, mult (SG b p q) x = mult (SG b p q) (-x) :=
    even_sun_mult_symmetry b (pq b p q) he
  refine ⟨hsym, ?_, ?_⟩
  · have hm := graph_square_partition (SG b p q) hG
    rw [Paper7SunMoments.sg_second_moment b p q hb,
      symmetric_large_square (SG b p q) hsym, ← hsym 1] at hm
    linarith
  · have h := lemma24_big_square_lower b p q hb hG
    rw [symmetric_large_square (SG b p q) hsym] at h
    linarith

theorem lemma24_counting_odd (b : ℕ) (p q : Fin b → ℕ) (hb : 3 ≤ b)
    (hG : IsIntegralGraph (SG b p q)) (_ho : Odd b) :
    ((∑ k, p k + ∑ k, q k : ℕ) : ℝ) ≤
      (1 / 2) * ((bigEigs (SG b p q)).map (fun x => x ^ 2)).sum - b + 2 :=
  lemma24_big_square_lower b p q hb hG

end Paper7Admissible
#print axioms Paper7Admissible.lemma24_big_square_lower
#print axioms Paper7Admissible.lemma24_counting_even
#print axioms Paper7Admissible.lemma24_counting_odd
