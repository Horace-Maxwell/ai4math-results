import Research.Backfill.Paper7.EightOddNormalization
import Research.Backfill.Paper7.EightHalfMonodromyExclusion

/-! Source-only transportation of the proved four parameter multisets to
the six integer transfer coefficients. No coefficient table is assumed. -/
set_option autoImplicit false
noncomputable section
namespace Paper7EightCycle
open BackfillPaper7.Challenge
open scoped BigOperators Classical

def halfCoefficient (n : ℕ) : ℤ := 2-(n/2 : ℕ)
#print axioms Paper7EightCycle.halfCoefficient

theorem half_coefficient_even (n : ℕ) (hn : n % 2 = 0) :
    (4 : ℤ)-n = 2*halfCoefficient n := by
  have h := Nat.mod_add_div n 2
  unfold halfCoefficient
  omega
#print axioms Paper7EightCycle.half_coefficient_even

theorem opposite_parity_nat (p : Fin 8 → ℕ)
    (hpar : ∀ i : Fin 8, (p i : ZMod 2) = if i = 0 ∨ i = 4 then 1 else 0) :
    ∀ i : Fin 8, p i % 2 = if i = 0 ∨ i = 4 then 1 else 0 := by
  intro i
  have h := congrArg (fun z : ZMod 2 => z.val) (hpar i)
  by_cases hi : i = 0 ∨ i = 4 <;> simpa [hi,ZMod.val_natCast, show (1 : ZMod 2).val = 1 by decide] using h
#print axioms Paper7EightCycle.opposite_parity_nat

theorem eight_opposite_coefficients (p : Fin 8 → ℕ) (hp : 0 < ∑ i, p i)
    (hn : nOf 8 p (fun _ => 0) ≤ 41) (hG : IsIntegralGraph (SG 8 p (fun _ => 0)))
    (hpar : ∀ i : Fin 8, (p i : ZMod 2) = if i = 0 ∨ i = 4 then 1 else 0) :
    (p 0+p 4 = 14 ∧
      [halfCoefficient (p 1),halfCoefficient (p 2),halfCoefficient (p 3),
       halfCoefficient (p 5),halfCoefficient (p 6),halfCoefficient (p 7)].Perm [-2,1,1,2,2,2]) ∨
    [halfCoefficient (p 1),halfCoefficient (p 2),halfCoefficient (p 3),
     halfCoefficient (p 5),halfCoefficient (p 6),halfCoefficient (p 7)].Perm [-1,-1,2,2,2,2] ∨
    [halfCoefficient (p 1),halfCoefficient (p 2),halfCoefficient (p 3),
     halfCoefficient (p 5),halfCoefficient (p 6),halfCoefficient (p 7)].Perm [-4,0,2,2,2,2] ∨
    [halfCoefficient (p 1),halfCoefficient (p 2),halfCoefficient (p 3),
     halfCoefficient (p 5),halfCoefficient (p 6),halfCoefficient (p 7)].Perm [-4,2,2,2,2,2] := by
  have hm := opposite_parity_nat p hpar
  have heven : (pBag p).filter (fun n => n % 2 = 0) =
      ↑([p 1,p 2,p 3,p 5,p 6,p 7] : List ℕ) := by simp [pBag,hm]
  have hodd : ((pBag p).filter (fun n => n % 2 = 1)).sum = p 0+p 4 := by
    simp [pBag,hm]
  rcases eight_integral_parameter_cover p hp hn hG with ha|hb|hc|hd
  · left
    have ho := congrArg (fun s : Multiset ℕ => (s.filter (fun n => n % 2 = 1)).sum) ha
    rw [hodd] at ho
    have hp14 : p 0+p 4 = 14 := by simpa using ho
    have he := congrArg (fun s : Multiset ℕ => s.filter (fun n => n % 2 = 0)) ha
    rw [heven] at he
    have hperm : [p 1,p 2,p 3,p 5,p 6,p 7].Perm [8,2,2,0,0,0] :=
      Multiset.coe_eq_coe.mp (by simpa using he)
    exact ⟨hp14,by simpa [halfCoefficient] using hperm.map halfCoefficient⟩
  · right; left
    have he := congrArg (fun s : Multiset ℕ => s.filter (fun n => n % 2 = 0)) hb
    rw [heven] at he
    have hperm : [p 1,p 2,p 3,p 5,p 6,p 7].Perm [6,6,0,0,0,0] :=
      Multiset.coe_eq_coe.mp (by simpa using he)
    simpa [halfCoefficient] using hperm.map halfCoefficient
  · right; right; left
    have he := congrArg (fun s : Multiset ℕ => s.filter (fun n => n % 2 = 0)) hc
    rw [heven] at he
    have hperm : [p 1,p 2,p 3,p 5,p 6,p 7].Perm [12,4,0,0,0,0] :=
      Multiset.coe_eq_coe.mp (by simpa using he)
    simpa [halfCoefficient] using hperm.map halfCoefficient
  · right; right; right
    have he := congrArg (fun s : Multiset ℕ => s.filter (fun n => n % 2 = 0)) hd
    rw [heven] at he
    have hperm : [p 1,p 2,p 3,p 5,p 6,p 7].Perm [12,0,0,0,0,0] :=
      Multiset.coe_eq_coe.mp (by simpa using he)
    simpa [halfCoefficient] using hperm.map halfCoefficient
#print axioms Paper7EightCycle.eight_opposite_coefficients

theorem eight_opposite_odd_nonintegral (p : Fin 8 → ℕ) (hp : 0 < ∑ i, p i)
    (hn : nOf 8 p (fun _ => 0) ≤ 41)
    (hpar : ∀ i : Fin 8, (p i : ZMod 2) = if i = 0 ∨ i = 4 then 1 else 0) :
    ¬ IsIntegralGraph (SG 8 p (fun _ => 0)) := by
  intro hG
  have hm := opposite_parity_nat p hpar
  have hne := Paper7EightHalf.mono_eight_opposite_four_coefficients_ne_one p
    (halfCoefficient (p 1)) (halfCoefficient (p 2)) (halfCoefficient (p 3))
    (halfCoefficient (p 5)) (halfCoefficient (p 6)) (halfCoefficient (p 7))
    (half_coefficient_even _ (by simpa using hm 1))
    (half_coefficient_even _ (by simpa using hm 2))
    (half_coefficient_even _ (by simpa using hm 3))
    (half_coefficient_even _ (by simpa using hm 5))
    (half_coefficient_even _ (by simpa using hm 6))
    (half_coefficient_even _ (by simpa using hm 7))
    (eight_opposite_coefficients p hp hn hG hpar)
  exact hne (eight_pure_p_remaining_monodromy p hp hn hG).1
#print axioms Paper7EightCycle.eight_opposite_odd_nonintegral

end Paper7EightCycle
