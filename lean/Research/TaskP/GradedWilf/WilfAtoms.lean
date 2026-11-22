import Research.TaskP.GradedWilf.WilfLayers
namespace TaskP.GradedWilf
open Challenge

theorem take_degree {d : ℕ} (t : ℕ) (x : Point d) (ht : t ≤ degree x) :
    ∃ y ≤ x, degree y = t := by
  induction t generalizing x with
  | zero => exact ⟨0,fun _ => Nat.zero_le _,by simp [degree]⟩
  | succ t ih =>
    have hx : x ≠ 0 := fun h => by simp [h,degree] at ht
    obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := by
      by_contra! h
      exact hx (funext h)
    let e : Point d := Pi.single i 1
    have he : degree e = 1 := by simp [e,degree,Pi.single_apply]
    have hle : e ≤ x := by
      intro j
      by_cases h : i = j
      · subst j
        simp only [e,Pi.single_eq_same]; omega
      · simp [e,Ne.symm h]
    have dec : e+(x-e) = x := add_tsub_cancel_of_le hle
    have hdeg := congrArg degree dec
    rw [degree_add,he] at hdeg
    obtain ⟨v,hv,hv'⟩ := ih (x-e) (by omega)
    exact ⟨e+v,dec ▸ (show e+v ≤ e+(x-e) from add_le_add_right hv e),by rw [degree_add,he,hv'];omega⟩

theorem split_scalar {a b t : ℕ} (ha : 2 ≤ a) (hb : a < b) (ht : t ∈ scalar a b)
    (h0 : t ≠ 0) (hnA : t ≠ a) (hnB : t ≠ b) :
    ∃ s r, s ∈ scalar a b ∧ r ∈ scalar a b ∧ 0 < s ∧ 0 < r ∧ s+r=t := by
  obtain ⟨i,j,he⟩ := scalar_iff.mp ht
  cases i with
  | zero =>
    cases j with
    | zero => simp_all
    | succ j =>
      simp only [Nat.zero_mul,Nat.zero_add,Nat.succ_mul] at he
      exact ⟨b,j*b,AddSubmonoid.subset_closure (by simp),
        scalar_iff.mpr ⟨0,j,by simp⟩,by omega,by omega,by omega⟩
  | succ i =>
    rw [Nat.succ_mul] at he
    exact ⟨a,i*a+j*b,AddSubmonoid.subset_closure (by simp),
      scalar_iff.mpr ⟨i,j,rfl⟩,by omega,by omega,by omega⟩

theorem min_degree {a b t : ℕ} (_ha : 2 ≤ a) (hb : a < b)
    (ht : t ∈ scalar a b) (h0 : t ≠ 0) : a ≤ t := by
  obtain ⟨i,j,rfl⟩ := scalar_iff.mp ht
  cases i with
  | succ i => rw [Nat.succ_mul];omega
  | zero =>
    cases j with
    | zero => simp_all
    | succ j => simp only [Nat.zero_mul,Nat.zero_add,Nat.succ_mul];omega

theorem divides_small {a b t : ℕ} (ht : t ∈ scalar a b) (small : t < b) : a ∣ t := by
  obtain ⟨i,j,rfl⟩ := scalar_iff.mp ht
  cases j with
  | zero => simp
  | succ j => rw [Nat.succ_mul] at small;omega

theorem atoms_eq {a b d : ℕ} (ha : 2 ≤ a) (hb : a < b) (hc : a.Coprime b) :
    atoms (graded a b d) = ((layer d a ∪ layer d b : Finset _) : Set (Point d)) := by
  ext x
  simp only [Finset.mem_coe,Finset.mem_union,mem_layer]
  constructor
  · rintro ⟨hx,hx0,hatom⟩
    by_contra! h
    obtain ⟨s,r,hs,hr,hsp,hrp,he⟩ := split_scalar ha hb hx (mt (degree_zero_iff x).mp hx0) h.1 h.2
    obtain ⟨v,hv,hd⟩ := take_degree s x (by omega)
    have dec : v+(x-v) = x := add_tsub_cancel_of_le hv
    have hv' := congrArg degree dec
    rw [degree_add,hd] at hv'
    have hdd : degree (x-v) = r := by omega
    rcases hatom v (show degree v ∈ scalar a b by rwa [hd]) (x-v)
        (show degree (x-v) ∈ scalar a b by rwa [hdd]) dec.symm with h | h
    · have := (degree_zero_iff _).mpr h;omega
    · have := (degree_zero_iff _).mpr h;omega
  · intro h
    have hpos : degree x ≠ 0 := by omega
    refine ⟨?_, mt (degree_zero_iff x).mpr hpos,?_⟩
    · change degree x ∈ scalar a b
      rcases h with he|he <;> rw [he] <;> exact AddSubmonoid.subset_closure (by simp)
    intro y hy z hz he
    by_contra! hn
    have yp := mt (degree_zero_iff y).mp hn.1
    have zp := mt (degree_zero_iff z).mp hn.2
    have hs := congrArg degree he
    rw [degree_add] at hs
    rcases h with hg|hg
    · have := min_degree ha hb hy yp
      omega
    · have hdiv := Nat.dvd_add (divides_small hy (by omega)) (divides_small hz (by omega))
      have hd : a ∣ b := by simpa only [← hs,hg] using hdiv
      have := Nat.gcd_eq_left hd
      rw [hc.gcd_eq_one] at this
      omega

end TaskP.GradedWilf
