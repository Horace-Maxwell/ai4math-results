import Research.Backfill.Paper7.EightCountMomentBounds

/-! Uncompiled analytic classification from the original two moments.
No profile, table completeness or graph hypothesis is added. -/
set_option autoImplicit false
noncomputable section
namespace Paper7EightCount
open scoped BigOperators Classical

theorem cap_ten_impossible (c : Fin 14 → ℕ) (h : Moments c 26 242 10) : False := by
  have ha := h.atom_square 10
  norm_num at ha
  rcases (by omega : c 10 = 0 ∨ c 10 = 1 ∨ c 10 = 2) with h10|h10|h10
  · have hb := (h.lower 10 rfl h10).bound
    omega
  · let d := cut c 10
    have hd : Moments d 16 142 9 :=
      (h.remove 10 1 16 142 h10 (by decide) (by decide)).lower 10 rfl (by simp [cut])
    have ha9 := hd.atom_square 9
    norm_num at ha9
    rcases (by omega : d 9 = 0 ∨ d 9 = 1) with h9|h9
    · have hb := (hd.lower 9 rfl h9).bound
      omega
    · have he := (hd.remove 9 1 7 61 h9 (by decide) (by decide)).cap_first (N := 7) (by decide)
      have hb := he.bound
      omega
  · have hd := (h.remove 10 2 6 42 h10 (by decide) (by decide)).cap_first (N := 6) (by decide)
    have hb := hd.bound
    omega
#print axioms Paper7EightCount.cap_ten_impossible

theorem cap_eleven_impossible (c : Fin 14 → ℕ) (h : Moments c 26 242 11) : False := by
  have ha := h.excess_atom 11
  norm_num at ha
  rcases (by omega : c 11 = 0 ∨ c 11 = 1) with h11|h11
  · exact cap_ten_impossible c (h.lower 11 rfl h11)
  · let d := cut c 11
    have hd : Moments d 15 121 10 :=
      (h.remove 11 1 15 121 h11 (by decide) (by decide)).lower 11 rfl (by simp [cut])
    have ha10 := hd.atom_square 10
    norm_num at ha10
    rcases (by omega : d 10 = 0 ∨ d 10 = 1) with h10|h10
    · have he : Moments d 15 121 9 := hd.lower 10 rfl h10
      have ha9 := he.atom_square 9
      norm_num at ha9
      rcases (by omega : d 9 = 0 ∨ d 9 = 1) with h9|h9
      · have hb := (he.lower 9 rfl h9).bound
        omega
      · have hf := (he.remove 9 1 6 40 h9 (by decide) (by decide)).cap_first (N := 6) (by decide)
        have hb := hf.bound
        omega
    · have he := (hd.remove 10 1 5 21 h10 (by decide) (by decide)).cap_square (N := 4) (by decide)
      have hb := he.bound
      omega
#print axioms Paper7EightCount.cap_eleven_impossible

theorem residual_five_nine (c : Fin 14 → ℕ) (h : Moments c 5 9 3) :
    PosEq c (fun j => if j = 2 then 2 else if j = 1 then 1 else 0) := by
  have he := h.excess_atom 3
  norm_num at he
  have h3 : c 3 = 0 := by omega
  have ht : Moments c 5 9 2 := h.lower 3 rfl h3
  have hs := ht.first
  have hq := ht.square
  norm_num [Fin.sum_univ_succ,ht.cap] at hs hq
  have h1 : c 1 = 1 := by omega
  have h2 : c 2 = 2 := by omega
  intro j hj
  fin_cases j
  all_goals norm_num at hj
  all_goals norm_num [h1,h2,ht.cap]
#print axioms Paper7EightCount.residual_five_nine

theorem residual_thirteen (c : Fin 14 → ℕ) (h : Moments c 13 73 8) :
    PosEq c (fun j => if j = 8 then 1 else if j = 2 then 2 else if j = 1 then 1 else 0) ∨
    PosEq c (fun j => if j = 6 then 2 else if j = 1 then 1 else 0) := by
  have ha8 := h.atom_square 8
  norm_num at ha8
  rcases (by omega : c 8 = 0 ∨ c 8 = 1) with h8|h8
  · have ht : Moments c 13 73 7 := h.lower 8 rfl h8
    have ha7 := ht.atom_square 7
    norm_num at ha7
    have h7 : c 7 = 0 := by
      by_contra hn
      have hc7 : c 7 = 1 := by omega
      have hd := (ht.remove 7 1 6 24 hc7 (by decide) (by decide)).cap_square (N := 4) (by decide)
      have he := hd.tight_first (by decide) 4 rfl
      omega
    have hu : Moments c 13 73 6 := ht.lower 7 rfl h7
    have ha6 := hu.atom_square 6
    have hb6 := hu.top_bound 6 rfl
    norm_num at ha6 hb6
    have h6 : c 6 = 2 := by omega
    have hd := (hu.remove 6 2 1 1 h6 (by decide) (by decide)).cap_square (N := 1) (by decide)
    have hs := hd.single (by decide) 1 rfl (by decide) 1 (by decide)
    right
    exact PosEq.restore 6 2 hs h6
  · have hd := (h.remove 8 1 5 9 h8 (by decide) (by decide)).cap_square (N := 3) (by decide)
    left
    exact PosEq.restore 8 1 (residual_five_nine _ hd) h8
#print axioms Paper7EightCount.residual_thirteen

theorem residual_fourteen (c : Fin 14 → ℕ) (h : Moments c 14 98 9) :
    PosEq c (fun j => if j = 9 then 1 else if j = 4 then 1 else if j = 1 then 1 else 0) ∨
    PosEq c (fun j => if j = 7 then 2 else 0) := by
  have ha9 := h.atom_square 9
  norm_num at ha9
  rcases (by omega : c 9 = 0 ∨ c 9 = 1) with h9|h9
  · have ht : Moments c 14 98 8 := h.lower 9 rfl h9
    have ha8 := ht.atom_square 8
    norm_num at ha8
    have h8 : c 8 = 0 := by
      by_contra hn
      have hc8 : c 8 = 1 := by omega
      have hd := (ht.remove 8 1 6 34 hc8 (by decide) (by decide)).cap_square (N := 5) (by decide)
      have hb := hd.bound
      omega
    have hu : Moments c 14 98 7 := ht.lower 8 rfl h8
    right
    exact hu.single (by decide) 7 rfl (by decide) 2 (by decide)
  · let d := cut c 9
    have hd : Moments d 5 17 4 :=
      (h.remove 9 1 5 17 h9 (by decide) (by decide)).cap_square (N := 4) (by decide)
    have ha4 := hd.atom_square 4
    have hb4 := hd.top_bound 4 rfl
    norm_num at ha4 hb4
    have h4 : d 4 = 1 := by omega
    have he := (hd.remove 4 1 1 1 h4 (by decide) (by decide)).cap_square (N := 1) (by decide)
    have hs := he.single (by decide) 1 rfl (by decide) 1 (by decide)
    have hp := PosEq.restore 4 1 hs h4
    left
    exact PosEq.restore 9 1 hp h9
#print axioms Paper7EightCount.residual_fourteen

theorem moment_positive_cover (c : Fin 14 → ℕ)
    (hs : ∑ j, j.val*c j = 26) (hq : ∑ j, j.val^2*c j = 242) :
    PosEq c ![0,1,2,0,0,0,0,0,1,0,0,0,0,1] ∨
    PosEq c ![0,1,0,0,0,0,2,0,0,0,0,0,0,1] ∨
    PosEq c ![0,1,0,0,1,0,0,0,0,1,0,0,1,0] ∨
    PosEq c ![0,0,0,0,0,0,0,2,0,0,0,0,1,0] := by
  have h : Moments c 26 242 13 := ⟨hs,hq,by intro j hj; have := j.isLt; omega⟩
  have ha13 := h.atom_square 13
  norm_num at ha13
  rcases (by omega : c 13 = 0 ∨ c 13 = 1) with h13|h13
  · have ht : Moments c 26 242 12 := h.lower 13 rfl h13
    have ha12 := ht.atom_square 12
    norm_num at ha12
    have h12 : c 12 = 1 := by
      by_contra hn
      have hz : c 12 = 0 := by omega
      exact cap_eleven_impossible c (ht.lower 12 rfl hz)
    have hd := (ht.remove 12 1 14 98 h12 (by decide) (by decide)).cap_square (N := 9) (by decide)
    rcases residual_fourteen _ hd with hp|hp
    · right; right; left
      have he := PosEq.restore 12 1 hp h12
      intro j hj
      have hjj := he j hj
      fin_cases j <;> simpa using hjj
    · right; right; right
      have he := PosEq.restore 12 1 hp h12
      intro j hj
      have hjj := he j hj
      fin_cases j <;> simpa using hjj
  · have hd := (h.remove 13 1 13 73 h13 (by decide) (by decide)).cap_square (N := 8) (by decide)
    rcases residual_thirteen _ hd with hp|hp
    · left
      have he := PosEq.restore 13 1 hp h13
      intro j hj
      have hjj := he j hj
      fin_cases j <;> simpa using hjj
    · right; left
      have he := PosEq.restore 13 1 hp h13
      intro j hj
      have hjj := he j hj
      fin_cases j <;> simpa using hjj
#print axioms Paper7EightCount.moment_positive_cover

end Paper7EightCount
