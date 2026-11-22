import Research.TaskP.RectangleDefect.RectCounts
import Research.TaskP.RectangleDefect.RowSplit

namespace TaskP.RectangleDefect.Lower

open Challenge

def spot {k : ℕ} (j : Fin k) (c : ℕ) : Counts k := fun i => if j = i then c else 0

theorem area_spot {k : ℕ} (j : Fin k) (c : ℕ) : area (spot j c) = (j.val+1)*c := by
  simp [spot, area, mul_ite]

theorem area_add {k : ℕ} (m n : Counts k) : area (m+n) = area m + area n := by
  simp [area, mul_add, Finset.sum_add_distrib]

theorem area_sum {k r : ℕ} (m : Fin r → Counts k) : area (∑ j, m j) = ∑ j, area (m j) := by
  unfold area
  simp only [Finset.sum_apply, Finset.mul_sum]
  rw [Finset.sum_comm]

def four {k : ℕ} (hk : 6 ≤ k) : Fin k := ⟨3, by omega⟩
def six {k : ℕ} (hk : 6 ≤ k) : Fin k := ⟨5, by omega⟩

/-- Parameter j counts pairs of bricks of length 2(j+3). -/
def pos {k : ℕ} (_hk : 6 ≤ k) (j : Fin (exponent k)) : Fin k :=
  ⟨2*j.val+5, by have hj := j.isLt; unfold exponent at hj; omega⟩

theorem pos_inj {k : ℕ} (hk : 6 ≤ k) : Function.Injective (pos hk) := by
  intro i j h
  apply Fin.ext
  have e := congrArg Fin.val h
  dsimp [pos] at e
  omega

def weight {k M : ℕ} (x : Fin (exponent k) → Fin M) : ℕ :=
  ∑ j, (j.val + 3) * (x j).val

def family {k M : ℕ} (hk : 6 ≤ k) (n : ℕ) (x : Fin (exponent k) → Fin M) : Counts k :=
  spot (four hk) ((n-3)/2 - weight x) + spot (six hk) 1 +
    ∑ j, spot (pos hk j) (2*(x j).val)

theorem family_area {k M n : ℕ} (hk : 6 ≤ k) (hn : 3 ≤ n) (ho : Odd n)
    (x : Fin (exponent k) → Fin M) (hw : weight x ≤ (n-3)/2) :
    area (family hk n x) = 2*n := by
  rw [family, area_add, area_add, area_spot, area_spot, area_sum]
  simp only [area_spot, four, six, pos]
  have hs : (∑ j : Fin (exponent k), (2*j.val+5+1)*(2*(x j).val)) = 4 * weight x := by
    rw [weight, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intros
    ring
  rw [hs]
  obtain ⟨b,hb⟩ := ho
  omega

theorem family_inj {k M : ℕ} (hk : 6 ≤ k) (n : ℕ) : Function.Injective (@family k M hk n) := by
  intro x y h
  funext j
  have ex (f : Fin (exponent k) → Fin M) :
      family hk n f (pos hk j) = (if six hk = pos hk j then 1 else 0) + 2*(f j).val := by
    have ne : four hk ≠ pos hk j := by
      intro hh
      have h' := congrArg Fin.val hh
      simp [four,pos] at h'
    simp only [family, Pi.add_apply, spot, ite_eq_right ne, zero_add, Finset.sum_apply]
    congr 1
    rw [Finset.sum_eq_single j]
    · simp
    · intro i _ hi
      exact ite_eq_right (fun hh => hi (pos_inj hk hh))
    · simp
  have he := congrFun h (pos hk j)
  rw [ex, ex] at he
  apply Fin.ext
  omega

def long {k : ℕ} (m : Counts k) : Prop :=
  ∀ i, m i ≠ 0 → Even (i.val + 1) ∧ 4 ≤ i.val+1

theorem family_long {k M n : ℕ} (hk : 6 ≤ k) (x : Fin (exponent k) → Fin M) :
    long (family hk n x) := by
  intro i hi
  by_cases h₄ : four hk = i
  · subst i
    change Even 4 ∧ 4 ≤ 4
    decide
  by_cases h₆ : six hk = i
  · subst i
    change Even 6 ∧ 4 ≤ 6
    decide
  by_cases h : ∃ j, pos hk j = i
  · obtain ⟨j,rfl⟩ := h
    exact ⟨⟨j.val+3, by simp [pos]; omega⟩, by simp [pos]⟩
  · push Not at h
    simp [family, spot, h₄, h₆, Finset.sum_apply, h] at hi

theorem long_forbids {k n : ℕ} {m : Counts k} (hm : long m) (hn : Odd n) :
    ¬ RowSplit m n := by
  rintro ⟨top, bottom, vert, hsum, hvert, htop, _⟩
  have hv (i : Fin k) : vert i = 0 := by
    by_contra! h
    have h₁ := hvert i h
    have h₂ := hsum i
    have h₃ := (hm i (by omega)).2
    omega
  simp [hv] at htop
  have ht : area top = 2 * (∑ i, ((i.val+1)/2) * top i) := by
    rw [area, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    by_cases h : top i = 0
    · simp [h]
    have e := hsum i
    obtain ⟨z, hz⟩ := (hm i (by omega)).1
    have hhalf : (i.val+1)/2 = z := by omega
    rw [hhalf, hz]
    ring
  obtain ⟨z,hz⟩ := hn
  omega

end TaskP.RectangleDefect.Lower
