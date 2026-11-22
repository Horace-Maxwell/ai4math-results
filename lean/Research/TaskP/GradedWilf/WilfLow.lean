import Research.TaskP.GradedWilf.WilfHigh
namespace TaskP.GradedWilf
open Challenge

noncomputable def good (a b : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range (frob a b + 1)).filter (· ∈ scalar a b)

@[simp] theorem mem_good {a b t : ℕ} : t ∈ good a b ↔ t ≤ frob a b ∧ t ∈ scalar a b := by
  classical
  simp [good]

theorem twice_card_good {a b : ℕ} (ha : 2 ≤ a) (hb : a < b) (hc : a.Coprime b) :
    2*(good a b).card = frob a b + 1 := by
  classical
  let F := frob a b
  let bad := (Finset.range (F+1)).filter (· ∉ scalar a b)
  have hbad (t) : t ∈ bad ↔ t ≤ F ∧ t ∉ scalar a b := by simp [bad]
  have same : (good a b).card = bad.card := by
    apply Finset.card_bij' (fun t _ => F-t) (fun t _ => F-t)
    · intro i hi
      obtain ⟨hi,hm⟩ := mem_good.mp hi
      exact (hbad _).2 ⟨Nat.sub_le .., fun h => (reflect_mem ha hb hc hi).1 h hm⟩
    · intro i hi
      obtain ⟨hi,hm⟩ := (hbad _).1 hi
      exact mem_good.mpr ⟨Nat.sub_le ..,(reflect_mem ha hb hc hi).2 hm⟩
    · intro i hi
      have h := (mem_good.mp hi).1
      dsimp [F]; omega
    · intro i hi
      have h := ((hbad _).1 hi).1
      omega
  have total : (good a b).card + bad.card = F+1 := by
    simpa [good,bad,F] using (Finset.card_filter_add_card_filter_not (s := Finset.range (F+1)) (fun t => t ∈ scalar a b))
  omega

theorem good_count {a b d : ℕ} (ha : 2 ≤ a) (hb : a < b) (hc : a.Coprime b) (hd : 0 < d) :
    (belowGaps (graded a b d) ∩ graded a b d).ncard =
      ∑ t ∈ good a b,d.multichoose t := by
  classical
  have hs : belowGaps (graded a b d) ∩ graded a b d =
      (((good a b).biUnion (layer d)) : Set (Point d)) := by
    ext x
    rw [below_eq_ball ha hb hc hd]
    change (x ∈ ball d (frob a b) ∧ degree x ∈ scalar a b) ↔ _
    simp
  rw [hs, Set.ncard_coe_finset, Finset.card_biUnion]
  · simp [card_layer]
  · intro i _ j _ hij
    exact Finset.disjoint_left.mpr (fun x hx hy => hij ((mem_layer.mp hx).symm.trans (mem_layer.mp hy)))

theorem twice_sum_succ (s : Finset ℕ) : s.card*(s.card+1) ≤ 2 * ∑ x ∈ s,(x+1) := by
  induction s using Finset.induction_on_max with
  | empty => simp
  | insert x s h ih =>
    have hx : x ∉ s := fun hmem => (lt_irrefl _) (h x hmem)
    have count : s.card ≤ x := by
      simpa using Finset.card_le_card (show s ⊆ Finset.range x from fun j hj => Finset.mem_range.mpr (h j hj))
    rw [Finset.sum_insert hx,Finset.card_insert_of_notMem hx]
    nlinarith only [ih,count]

theorem low_wilf {a b d : ℕ} (ha : 2 ≤ a) (hb : a < b) (hc : a.Coprime b)
    (hd : 0 < d) (hlo : d ≤ 2) :
    d * ((frob a b+d).choose d) ≤
      (d.multichoose a+d.multichoose b) * ∑ t ∈ good a b,d.multichoose t := by
  classical
  have hcount := twice_card_good ha hb hc
  interval_cases d
  · simp only [Nat.choose_one_right, Nat.one_mul,Nat.multichoose_one,Finset.sum_const,
      nsmul_eq_mul,mul_one]
    simpa using le_of_eq hcount.symm
  · simp only [Nat.multichoose_two]
    have ht := twice_sum_succ (good a b)
    by_cases he : 8 ≤ a+1+(b+1)
    · have he' := Nat.mul_le_mul_right (∑ t ∈ good a b,(t+1)) he
      rw [Nat.choose_two_right]
      have hsub : frob a b+2-1=frob a b+1 := by omega
      rw [hsub]
      have hdv := Nat.div_mul_le_self ((frob a b+2)*(frob a b+1)) 2
      have hF : frob a b+2=2*(good a b).card+1 := by omega
      nlinarith only [he',ht,hdv, congrArg (fun z : ℕ => (frob a b+2)*z) hcount,
        congrArg (fun z : ℕ => z * (2*(good a b).card)) hF]
    · have A : a=2 := by omega
      have B : b=3 := by omega
      subst a b
      have H : (good 2 3).card=1 := by norm_num [frob] at hcount;omega
      rw [H] at ht
      norm_num [frob]
      omega

end TaskP.GradedWilf
