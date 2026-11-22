import Research.TaskN.Antichain.TreeCode

namespace TaskN.Antichain

open Polynomial Set

private theorem above_crossing (p : ℝ[X]) (s : ℝ) (hs : s < 0)
    (hneg : p.eval s < 0) (hn : ∀ x : ℝ, 0 ≤ x → 0 < p.eval x) :
    ∃ r : ℝ, s < r ∧ r < 0 ∧ IsGreatest {x : ℝ | p.eval x = 0} r ∧
      ∀ x : ℝ, r < x → x ≤ 0 → 0 < p.eval x := by
  have h0 := hn 0 le_rfl
  have cross (a : ℝ) (ha : a ≤ 0) (hv : p.eval a ≤ 0) :
      ∃ b ∈ Icc a 0, p.eval b = 0 :=
    intermediate_value_Icc ha p.continuous.continuousOn ⟨hv,h0.le⟩
  obtain ⟨b,hb,hr⟩ := cross s hs.le hneg.le
  have pn : p ≠ 0 := by intro e; simp [e] at h0
  have hf : Set.Finite {x : ℝ | p.eval x = 0} := Polynomial.finite_setOfPred_isRoot pn
  obtain ⟨r,hmax⟩ := hf.isCompact.exists_isGreatest ⟨b,hr⟩
  have hrs : s < r := lt_of_lt_of_le (lt_of_le_of_ne hb.1 (by rintro rfl; linarith)) (hmax.2 hr)
  have hrn : r < 0 := by
    by_contra! bad
    have hz : p.eval r = 0 := hmax.1
    linarith [hn r bad]
  refine ⟨r,hrs,hrn,hmax,?_⟩
  intro x hx hx0
  by_contra! hv
  obtain ⟨y,hy,hyz⟩ := cross x hx0 hv
  linarith [hmax.2 hyz,hy.1]

private noncomputable abbrev z (t : RT) (x : ℝ) : ℝ := t.pair.1.eval x
private noncomputable abbrev u (t : RT) (x : ℝ) : ℝ := t.pair.2.eval x
private theorem linkZ (l r : RT) (x : ℝ) :
    z (.link l r) x = u l x*z r x + (z l x-u l x)*u r x := by simp [z,u,RT.pair]
private theorem linkU (l r : RT) (x : ℝ) :
    u (.link l r) x = u l x*z r x := by simp [z,u,RT.pair]

private theorem pos_side (t : RT) (x : ℝ) (hx : 0 ≤ x) :
    0 < u t x ∧ u t x ≤ z t x := by
  induction t with
  | leaf => simp [z,u,RT.pair,hx]
  | link l r hl hr =>
    rw [linkU,linkZ]
    exact ⟨mul_pos hl.1 (lt_of_lt_of_le hr.1 hr.2),
        le_add_of_nonneg_right (mul_nonneg (sub_nonneg.mpr hl.2) hr.1.le)⟩

private theorem root_invariant (t : RT) :
    ∃ r : ℝ, r < 0 ∧ IsGreatest {x : ℝ | z t x = 0} r ∧
    (∀ x, r < x → x ≤ 0 → 0 < z t x) ∧
    (∀ x, r ≤ x → x ≤ 0 → 0 < u t x) ∧
    (∀ x, r ≤ x → x < 0 → z t x < u t x) := by
  induction t with
  | leaf =>
    refine ⟨-1,by norm_num,?_,?_,?_,?_⟩
    · constructor
      · norm_num [RT.pair,z]
      · intro x hx
        have h : 1 + x = 0 := by simpa [RT.pair,z] using hx
        linarith
    · intro x ha _; simp [RT.pair,z]; linarith
    · intro x _ _; simp [RT.pair,u]
    · intro x _ hx; simpa [RT.pair,z,u] using hx
  | link l q hL hQ =>
    obtain ⟨a,ha,ham,haz,hau,had⟩ := hL
    obtain ⟨b,hb,hbm,hbz,hbu,hbd⟩ := hQ
    let s := max a b
    have hs : s < 0 := max_lt ha hb
    have hal : a ≤ s := le_max_left _ _
    have hbl : b ≤ s := le_max_right _ _
    have hleft : z l a = 0 := ham.1
    have hright : z q b = 0 := hbm.1
    have hneg : z (.link l q) s < 0 := by
      rw [linkZ]
      by_cases hab : b ≤ a
      · have e : s = a := max_eq_left hab
        rw [← e] at hleft
        rw [hleft,zero_sub,neg_mul]
        nlinarith [mul_pos (hau s hal hs.le) (sub_pos.mpr (hbd s hbl hs))]
      · have e : s = b := max_eq_right (le_of_not_ge hab)
        rw [← e] at hright
        rw [hright,mul_zero,zero_add]
        exact mul_neg_of_neg_of_pos (sub_neg.mpr (had s hal hs)) (hbu s hbl hs.le)
    obtain ⟨r,hr,hn,hm,hz⟩ := above_crossing (RT.link l q).pair.1 s hs hneg
      (fun x hx => let hh := pos_side (RT.link l q) x hx; lt_of_lt_of_le hh.1 hh.2)
    refine ⟨r,hn,hm,hz,?_,?_⟩
    · intro x hrx hx; rw [linkU]
      exact mul_pos (hau x (by linarith) hx) (hbz x (by linarith) hx)
    · intro x hrx hx; rw [linkZ,linkU]
      exact lt_of_sub_neg (by
        have hh := mul_neg_of_neg_of_pos (sub_neg.mpr (had x (by linarith) hx)) (hbu x (by linarith) hx.le)
        linarith)

theorem RT.exists_largestRoot (t : RT) : ∃ r : ℝ, IsGreatest {x : ℝ | t.pair.1.eval x = 0} r := by
  obtain ⟨r,_,hr,_⟩ := root_invariant t
  exact ⟨r,hr⟩

end TaskN.Antichain
