import Research.TaskP.RectangleDefect.RowSplit

namespace TaskP.RectangleDefect

open Challenge

def lengthBudget (k : ℕ) : ℕ := ∑ i : Fin k, (i.val+1)

def weighted {k : ℕ} (c : Fin k → ℤ) : ℤ := ∑ i, (i.val+1 : ℕ) * c i

theorem weighted_scale {k : ℕ} (t : ℤ) (c : Fin k → ℤ) :
    weighted (fun i => t*c i) = t * weighted c := by
  simp only [weighted, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro _ _
  ring

theorem gcd_combination {k : ℕ} (s : Finset (Fin k)) :
    ∃ c : Fin k → ℤ, (∀ i ∉ s, c i = 0) ∧ weighted c = s.gcd (fun i => i.val+1) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨fun _ => 0, by simp, by simp [weighted]⟩
  | @insert a s ha ih =>
    obtain ⟨c, supp, rep⟩ := ih
    let g := s.gcd (fun i => i.val+1)
    let x := a.val+1
    let A := Nat.gcdA x g
    let B := Nat.gcdB x g
    refine ⟨fun i => (if i = a then A else 0) + B*c i,?_,?_⟩
    · intro i hi
      simp only [Finset.mem_insert, not_or] at hi
      simp [hi.1,supp i hi.2]
    · have hb := weighted_scale B c
      unfold weighted at hb ⊢
      simp only [mul_add, Finset.sum_add_distrib, mul_ite, mul_zero, Finset.sum_ite_eq',
        Finset.mem_univ, ite_true, Finset.gcd_insert]
      rw [hb]
      change (x : ℤ) * A + B * weighted c = (x.gcd g : ℤ)
      rw [rep, Nat.gcd_eq_gcd_ab]
      dsimp only [A,B,g]
      ring

theorem bounded_combination (k : ℕ) :
    ∃ bound : ℕ, ∀ (s : Finset (Fin k)) (h : ℕ), h ≤ lengthBudget k →
      s.gcd (fun i => i.val+1) ∣ h →
      ∃ c : Fin k → ℤ, (∀ i ∉ s, c i = 0) ∧ (∀ i, (c i).natAbs ≤ bound) ∧ weighted c = h := by
  classical
  have rep (s : Finset (Fin k)) (t : Fin (lengthBudget k + 1)) :
      ∃ c : Fin k → ℤ, (∀ i ∉ s, c i = 0) ∧
        (s.gcd (fun i => i.val+1) ∣ t.val → weighted c = t.val) := by
    by_cases hd : s.gcd (fun i => i.val+1) ∣ t.val
    · obtain ⟨q,hq⟩ := hd
      obtain ⟨c,supp,hc⟩ := gcd_combination s
      refine ⟨fun i => (q:ℤ)*c i,fun i hi => by simp [supp i hi],fun _ => ?_⟩
      rw [weighted_scale,hc,hq,Nat.cast_mul,mul_comm]
    · exact ⟨fun _ => 0,by simp,fun h => (hd h).elim⟩
  choose C hC using rep
  let B (s : Finset (Fin k)) (h : Fin (lengthBudget k+1)) := ∑ i, (C s h i).natAbs
  refine ⟨∑ s : Finset (Fin k), ∑ h : Fin (lengthBudget k+1), B s h, ?_⟩
  intro s h hh hd
  let t : Fin (lengthBudget k+1) := ⟨h, by omega⟩
  refine ⟨C s t,(hC s t).1,?_,(hC s t).2 hd⟩
  intro i
  calc (C s t i).natAbs ≤ B s t := Finset.single_le_sum (f := fun j => (C s t j).natAbs)
                                   (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
       _ ≤ ∑ t, B s t := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ t)
       _ ≤ _ := Finset.single_le_sum (f := fun s : Finset (Fin k) => ∑ t, B s t)
                  (fun _ _ => Nat.zero_le _) (Finset.mem_univ s)

end TaskP.RectangleDefect
