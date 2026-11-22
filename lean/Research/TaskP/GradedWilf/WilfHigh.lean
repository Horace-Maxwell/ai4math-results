import Research.TaskP.GradedWilf.WilfLayers
namespace TaskP.GradedWilf

theorem mc_as_choose (v t : ℕ) : (v+1).multichoose t = (t+v).choose v := by
  rw [Nat.multichoose_eq,show v+1+t-1=t+v by omega]
  exact Nat.choose_symm_add

private theorem mc_three (t : ℕ) : 2 * (3).multichoose t = (t+1)*(t+2) := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [Nat.multichoose_succ_succ 2 t, Nat.multichoose_two]
    nlinarith

private theorem mc_poslevel (d t : ℕ) : d+1 ≤ (d+1).multichoose (t+1) := by
  induction t with
  | zero => simp
  | succ t ih => rw [Nat.multichoose_succ_succ d (t+1)];omega

private theorem mc_step {d t : ℕ} (ht : 2 ≤ t) :
    d.multichoose t + (d+1) ≤ (d+1).multichoose t := by
  obtain ⟨r,rfl⟩ := Nat.exists_eq_add_of_le ht
  rw [show 2+r = (r+1)+1 by omega,Nat.multichoose_succ_succ]
  have := mc_poslevel d r
  omega

theorem embedding_lower {a b d : ℕ} (ha : 2 ≤ a) (hb : a < b) (hd : 3 ≤ d) :
    frob a b + d*d + d - 1 ≤ d.multichoose a + d.multichoose b := by
  have hab := bound_add ha hb
  have hF : frob a b + b+a=a*b := by dsimp [frob];omega
  induction d,hd using Nat.le_induction with
  | base =>
    have hA := mc_three a
    have hB := mc_three b
    have hsq := Nat.mul_self_le_mul_self (Nat.sub_le b a)
    have hdiff : a+(b-a)=b := Nat.add_sub_of_le (by omega)
    have hrem : 0 ≤ (b-a)*(b-a) := Nat.zero_le _
    change frob a b + 3*3+3-1 ≤ _
    have hnum : 2*(frob a b+11) ≤ 2*(Nat.multichoose 3 a + Nat.multichoose 3 b) := by
      nlinarith [congrArg (fun t : ℕ => t*t) hdiff, congrArg (fun t : ℕ => a*t) hdiff]
    omega
  | succ d hd ih =>
    have h1 := mc_step (d:=d) ha
    have h2 := mc_step (d:=d) (t:=b) (by omega)
    have hstep : frob a b+(d+1)*(d+1)+(d+1) = (frob a b+d*d+d) + 2*(d+1) := by ring
    omega

private theorem slice_ratio (u v : ℕ) :
    (u+1)*((v+1)*((u+1+(v+1)).choose (v+1))) =
      (u+v+2)*(u+v+1)*(v+1).multichoose u := by
  rw [mc_as_choose]
  have h1 := Nat.add_one_mul_choose_eq (u+v+1) v
  have h2 := Nat.choose_mul_succ_eq (u+v) v
  rw [show u+v+1-v=u+1 by omega] at h2
  rw [show u+1+(v+1)=u+v+1+1 by omega]
  nlinarith only [congrArg (fun z : ℕ => z*(u+1)) h1,congrArg (fun z : ℕ => z*(u+v+2)) h2]

theorem high_wilf {a b d : ℕ} (ha : 2 ≤ a) (hb : a < b) (hd : 3 ≤ d) :
    d * ((frob a b+d).choose d) ≤
      (d.multichoose a+d.multichoose b)*d.multichoose (frob a b-1) := by
  obtain ⟨u,hu⟩ : ∃ u, frob a b = u+1 := by
    have := bound_add ha hb
    exact ⟨frob a b-1,by dsimp [frob];omega⟩
  obtain ⟨v,rfl⟩ : ∃ v, d=v+1 := ⟨d-1,by omega⟩
  have he := embedding_lower ha hb hd
  rw [hu] at he ⊢
  simp only [Nat.add_sub_cancel] at *
  have ratio := slice_ratio u v
  have ht : (u+v+2)*(u+v+1) ≤ (u+1)*((u+1)+(v+1)*(v+1)+(v+1)-1) := by
    rw [show (u+1)+(v+1)*(v+1)+(v+1)-1=u+(v+1)*(v+1)+(v+1) by omega]
    nlinarith only [Nat.zero_le (u*v*v),Nat.zero_le (u*v)]
  have h := (Nat.mul_le_mul_right ((v+1).multichoose u) (ht.trans (Nat.mul_le_mul_left _ he)))
  rw [← ratio,Nat.mul_assoc] at h
  exact Nat.le_of_mul_le_mul_left h (by omega)

end TaskP.GradedWilf
