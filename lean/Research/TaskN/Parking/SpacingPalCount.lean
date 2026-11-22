import Research.TaskN.Parking.SpacingWord

namespace TaskN.Parking
open Challenge
open scoped Classical

noncomputable def palCount (s : List ℕ) : ℕ :=
  ((Finset.range (s.length+1)).filter fun i => pal (s.take i)).card

private theorem sum_pairs (f : ℕ → ℕ) (n : ℕ) :
    (∑ i ∈ Finset.range (2*n), f i) =
    ∑ i ∈ Finset.range n, (f (2*i)+f (2*i+1)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show 2*(n+1)=2*n+1+1 by omega,Finset.sum_range_succ,Finset.sum_range_succ,
      Finset.sum_range_succ,ih,Nat.add_assoc]

private theorem card_le_sum (k n : ℕ) (hk : k ≤ n) :
    (∑ i ∈ Finset.range (n+1), if i ≤ k then 1 else 0) = k+1 := by
  rw [← Finset.card_filter]
  have eq : ((Finset.range (n+1)).filter fun i => i ≤ k) = Finset.range (k+1) := by
    ext i; simp only [Finset.mem_filter,Finset.mem_range]; omega
  simp [eq]

theorem palCount_stretch (x : ℕ) (s : List ℕ) :
    palCount (stretch x s) = (lead x s + 1) + palCount s := by
  simp only [palCount,length_stretch,Finset.card_filter]
  rw [show 2*s.length+1+1=2*(s.length+1) by omega,sum_pairs,Finset.sum_add_distrib]
  congr 1
  · rw [← card_le_sum (lead x s) s.length (lead_le_length x s)]
    apply Finset.sum_congr rfl
    intro i hi
    have h : i ≤ s.length := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
    simp only [take_stretch_even x s i h,pal_pairs,all_take_iff x s i h]
  · apply Finset.sum_congr rfl
    intro i hi
    have h : i ≤ s.length := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
    simp only [take_stretch_odd x s i h,pal_stretch]

theorem lead_stretch_eq (x : ℕ) (s : List ℕ) :
    lead x (stretch x s) = 2 * lead x s + 1 := by
  induction s with
  | nil => simp [lead]
  | cons y ys ih =>
    simp only [stretch_cons,lead,ite_true]
    by_cases e : y=x
    · subst y; simp only [ite_true,ih]; omega
    · simp [e]

theorem lead_stretch_ne (x y : ℕ) (h : y ≠ x) (s : List ℕ) :
    lead x (stretch y s) = 0 := by
  cases s <;> simp [lead,h]

theorem lead_ruler (x : ℕ) (s : List ℕ) :
    lead x (ruler s)+1 = 2 ^ lead x s := by
  induction s with
  | nil => simp [ruler,lead]
  | cons y ys ih =>
    by_cases h : y = x
    · subst y
      rw [ruler,lead_stretch_eq,lead,ite_eq_left (Eq.refl x),pow_add,← ih]
      omega
    · simp [ruler,lead,lead_stretch_ne x y h,h]

private theorem runs_info_cons (x : ℕ) (xs : List ℕ) :
    ∃ rest, runs (x::xs) = (x,1+lead x xs)::rest := by
  induction xs generalizing x with
  | nil => exact ⟨[],rfl⟩
  | cons y ys ih =>
    obtain ⟨rest,eq⟩ := ih y
    rw [runs,eq]
    by_cases h : x=y
    · subst y
      exact ⟨rest,by simp [lead,Nat.add_comm]⟩
    · exact ⟨(y,1+lead y ys)::rest,by simp [h,Ne.symm h,lead]⟩

theorem runContribution_cons (x : ℕ) (xs : List ℕ) :
    runContribution (x::xs) = 2^(lead x xs) + runContribution xs := by
  cases xs with
  | nil => rfl
  | cons y ys =>
    obtain ⟨rest,eq⟩ := runs_info_cons y ys
    unfold runContribution
    conv_lhs => rw [runs,eq]
    rw [eq]
    by_cases h : x=y
    · subst y
      simp only [ite_true,List.map_cons,List.sum_cons,lead,pow_succ]
      have hp : 0 < 2^(1+lead x ys) := by positivity
      omega
    · simp [h,Ne.symm h,lead]

theorem palCount_ruler (s : List ℕ) :
    palCount (ruler s) = 1 + runContribution s := by
  induction s with
  | nil => simp [palCount,ruler,pal,runContribution,runs]
  | cons x xs ih =>
    rw [ruler,palCount_stretch,lead_ruler,ih,runContribution_cons]; omega

end TaskN.Parking
