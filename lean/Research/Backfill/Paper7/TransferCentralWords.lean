import Research.Backfill.Paper7.TransferModFourCharacter

/-! Source-only local surgery and cyclic transport for integral transfer
words. These are exact identities, not a bounded search. -/
set_option autoImplicit false
noncomputable section
namespace Paper7CentralWords
open Paper7TransferModFour
open scoped Matrix

def word (l : List ℤ) : Matrix (Fin 2) (Fin 2) ℤ := (l.map transfer).prod
#print axioms Paper7CentralWords.word

def Central (M : Matrix (Fin 2) (Fin 2) ℤ) : Prop := M = 1 ∨ M = -1
#print axioms Paper7CentralWords.Central

theorem central_neg (M : Matrix (Fin 2) (Fin 2) ℤ) : Central (-M) ↔ Central M := by
  simp [Central,neg_eq_iff_eq_neg,or_comm]
#print axioms Paper7CentralWords.central_neg

theorem central_move_head (x : ℤ) (l : List ℤ) (h : Central (word (x::l))) :
    Central (word (l++[x])) := by
  let V : Matrix (Fin 2) (Fin 2) ℤ := !![0,1;-1,x]
  have hV : V*transfer x = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [V,transfer,Matrix.mul_apply,Fin.sum_univ_two]
  have he : word (l++[x]) = V*word (x::l)*transfer x := by
    simp only [word,List.map_append,List.prod_append,List.map_cons,List.map_nil,
      List.prod_cons,List.prod_nil,mul_one]
    rw [← mul_assoc,hV,one_mul]
  rw [he]
  rcases h with h | h
  · exact Or.inl (by rw [h,mul_one,hV])
  · exact Or.inr (by rw [h,mul_neg_one,neg_mul,hV])
#print axioms Paper7CentralWords.central_move_head

theorem central_cycle (a b : List ℤ) (h : Central (word (a++b))) :
    Central (word (b++a)) := by
  induction a generalizing b with
  | nil => simpa using h
  | cons x a ih =>
    have hh := central_move_head x (a++b) h
    have ht : Central (word (a++(b++[x]))) := by simpa only [List.append_assoc] using hh
    have hr := ih (b++[x]) ht
    simpa only [List.append_assoc,List.singleton_append] using hr
#print axioms Paper7CentralWords.central_cycle

theorem central_one_false (x : ℤ) : ¬ Central (word [x]) := by
  intro h
  rcases h with h | h
  all_goals
    have hh := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℤ => M 1 0) h
    norm_num [word,transfer] at hh
#print axioms Paper7CentralWords.central_one_false

theorem central_two_zero (a b : ℤ) (h : Central (word [a,b])) : a = 0 ∧ b = 0 := by
  rcases h with h | h
  · have hh := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℤ => M 1 1) h
    norm_num [word,transfer,Matrix.mul_apply,Fin.sum_univ_two] at hh
  · have h01 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℤ => M 0 1) h
    have h10 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℤ => M 1 0) h
    norm_num [word,transfer,Matrix.mul_apply,Fin.sum_univ_two] at h01 h10
    exact ⟨by omega,h10⟩
#print axioms Paper7CentralWords.central_two_zero

theorem central_surgery_one (a b : ℤ) (l : List ℤ)
    (h : Central (word (a::1::b::l))) : Central (word ((a-1)::(b-1)::l)) := by
  have ht : transfer a*transfer (1 : ℤ)*transfer b = transfer (a-1)*transfer (b-1) := by
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [transfer,Matrix.mul_apply,Fin.sum_univ_two]
    all_goals ring
  have he : word (a::1::b::l) = word ((a-1)::(b-1)::l) := by
    simp only [word,List.map_cons,List.prod_cons]
    rw [← mul_assoc,← mul_assoc,ht,mul_assoc]
  rwa [he] at h
#print axioms Paper7CentralWords.central_surgery_one

theorem central_surgery_zero (a b : ℤ) (l : List ℤ)
    (h : Central (word (a::0::b::l))) : Central (word ((a+b)::l)) := by
  have ht : transfer a*transfer (0 : ℤ)*transfer b = -transfer (a+b) := by
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [transfer,Matrix.mul_apply,Fin.sum_univ_two]
  have he : word (a::0::b::l) = -word ((a+b)::l) := by
    simp only [word,List.map_cons,List.prod_cons]
    rw [← mul_assoc,← mul_assoc,ht,neg_mul]
  rw [he] at h
  exact (central_neg _).mp h
#print axioms Paper7CentralWords.central_surgery_zero

theorem central_surgery_neg_one (a b : ℤ) (l : List ℤ)
    (h : Central (word (a::(-1)::b::l))) : Central (word ((a+1)::(b+1)::l)) := by
  have ht : transfer a*transfer (-1 : ℤ)*transfer b = -(transfer (a+1)*transfer (b+1)) := by
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [transfer,Matrix.mul_apply,Fin.sum_univ_two]
    all_goals ring
  have he : word (a::(-1)::b::l) = -word ((a+1)::(b+1)::l) := by
    simp only [word,List.map_cons,List.prod_cons]
    rw [← mul_assoc,← mul_assoc,ht,neg_mul,mul_assoc]
  rw [he] at h
  exact (central_neg _).mp h
#print axioms Paper7CentralWords.central_surgery_neg_one

theorem split_member (l : List ℤ) (x : ℤ) (hx : x ∈ l) :
    ∃ a b, l = a++x::b := by
  induction l with
  | nil => simp at hx
  | cons y l ih =>
    rcases List.mem_cons.mp hx with rfl | hx
    · exact ⟨[],l,rfl⟩
    · obtain ⟨a,b,hab⟩ := ih hx
      exact ⟨y::a,b,by simp [hab]⟩
#print axioms Paper7CentralWords.split_member

theorem split_last (l : List ℤ) (hl : l ≠ []) : ∃ a x, l = a++[x] := by
  induction l with
  | nil => contradiction
  | cons x l ih =>
    by_cases ht : l = []
    · exact ⟨[],x,by simp [ht]⟩
    · obtain ⟨a,y,ha⟩ := ih ht
      exact ⟨x::a,y,by simp [ha]⟩
#print axioms Paper7CentralWords.split_last

theorem central_pivot (l : List ℤ) (x : ℤ) (hx : x ∈ l) (hl : 3 ≤ l.length)
    (hc : Central (word l)) :
    ∃ a b r, l.Perm (a::x::b::r) ∧ Central (word (a::x::b::r)) := by
  obtain ⟨u,v,rfl⟩ := split_member l x hx
  have hh := central_cycle u (x::v) hc
  have hp : (u++x::v).Perm (x::(v++u)) := by
    simpa only [List.cons_append] using (List.perm_append_comm :
      (u++(x::v)).Perm ((x::v)++u))
  have hlen : 2 ≤ (v++u).length := by simp only [List.length_append,List.length_cons] at hl ⊢; omega
  cases ht : v++u with
  | nil => simp [ht] at hlen
  | cons b t =>
    have htne : t ≠ [] := by intro he; simp [ht,he] at hlen
    obtain ⟨r,a,rfl⟩ := split_last t htne
    have hh' : Central (word ((x::b::r)++[a])) := by
      simpa only [List.cons_append,ht] using hh
    have hc' := central_cycle (x::b::r) [a] hh'
    refine ⟨a,b,r,?_,by simpa using hc'⟩
    have hp' : (u++x::v).Perm ((x::b::r)++[a]) := by
      simpa only [ht,List.cons_append] using hp
    exact hp'.trans (by simpa using (List.perm_append_comm :
      ((x::b::r)++[a]).Perm ([a]++(x::b::r))))
#print axioms Paper7CentralWords.central_pivot

end Paper7CentralWords
