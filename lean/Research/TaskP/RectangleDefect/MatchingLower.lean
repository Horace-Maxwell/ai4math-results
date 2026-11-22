import Research.TaskP.RectangleDefect.LowerFamily
import Research.TaskP.RectangleDefect.BoundaryRows

namespace TaskP.RectangleDefect.Lower

open Challenge

private def scale (k : ℕ) : ℕ := 2*k*k + 4

private theorem weight_bound {k M : ℕ} (hk : 6 ≤ k) (x : Fin (exponent k) → Fin M) :
    weight x ≤ k*k*M := by
  have he : exponent k ≤ k := by unfold exponent; omega
  calc
    weight x ≤ ∑ _j : Fin (exponent k), k*M := by
      apply Finset.sum_le_sum
      intro j _
      have hj := j.isLt
      unfold exponent at hj
      exact Nat.mul_le_mul (by omega) (Nat.le_of_lt (x j).isLt)
    _ = exponent k * (k*M) := by simp
    _ ≤ k*k*M := by rw [Nat.mul_assoc]; exact Nat.mul_le_mul_right _ he

theorem odd_lower (k : ℕ) (hk : 6 ≤ k) :
    ∃ C N : ℕ, 0 < C ∧ ∀ n ≥ N, Odd n → (n+1)^exponent k ≤ C * defect k n := by
  let D := scale k
  have hD : 0 < D := by dsimp [D, scale]; omega
  refine ⟨(2*D)^exponent k, D, by positivity, ?_⟩
  intro n hn ho
  let M := n / D
  have hM : 0 < M := Nat.div_pos hn hD
  have hmul : M*D ≤ n := Nat.div_mul_le_self _ _
  have hbound : n < (M+1)*D := by
    have h₁ := Nat.mod_add_div n D
    have h₂ := Nat.mod_lt n hD
    dsimp [M]
    nlinarith
  have hn₃ : 3 ≤ n := by dsimp [D, scale] at hn; omega
  have hw (x : Fin (exponent k) → Fin M) : weight x ≤ (n-3)/2 := by
    have hx := weight_bound hk x
    dsimp [D, scale] at hmul
    nlinarith [Nat.sub_add_cancel hn₃, Nat.mod_add_div (n-3) 2, Nat.mod_lt (n-3) (by decide : 0 < 2)]
  have hfail (x : Fin (exponent k) → Fin M) : family hk n x ∈ failures k n := by
    have ha := family_area hk hn₃ ho x (hw x)
    exact ⟨ha, fun ht => long_forbids (family_long hk x) ho (rowSplit_of_tiles ha ht)⟩
  have hs : Set.range (@family k M hk n) ⊆ failures k n := Set.range_subset_iff.mpr hfail
  have hfin : (failures k n).Finite := (multisets_finite k n).subset fun _ h => h.1
  have hc := Set.ncard_le_ncard hs hfin
  rw [Set.ncard_range_of_injective (family_inj hk n), ← defect_eq_failures] at hc
  have hc' : M ^ exponent k ≤ defect k n := by simpa [Nat.card_eq_fintype_card] using hc
  have hsmall : n+1 ≤ 2*D*M := by nlinarith
  calc
    (n+1)^exponent k ≤ (2*D*M)^exponent k := Nat.pow_le_pow_left hsmall _
    _ = (2*D)^exponent k * M^exponent k := mul_pow ..
    _ ≤ _ := Nat.mul_le_mul_left _ hc'

private def smallOne {k : ℕ} (hk : 3 ≤ k) : Fin k := ⟨0, by omega⟩
private def smallThree {k : ℕ} (hk : 3 ≤ k) : Fin k := ⟨2, by omega⟩

private theorem small_failure {k : ℕ} (hk : 3 ≤ k) (b : ℕ) :
    ∃ m ∈ failures k (3*b+2), True := by
  let i := smallOne hk
  let j := smallThree hk
  let m := spot i 1 + spot j (2*b+1)
  have hn : i ≠ j := by intro h; have e := congrArg Fin.val h; contradiction
  have hai : i.val + 1 = 1 := rfl
  have haj : j.val + 1 = 3 := rfl
  have ha : area m = 2*(3*b+2) := by simp [m, area_add, area_spot, hai, haj]; omega
  refine ⟨m, ⟨ha, fun h => ?_⟩, trivial⟩
  obtain ⟨top, bottom, vert, hsum, hvert, htop, _⟩ := rowSplit_of_tiles ha h
  have outside (l : Fin k) (h₁ : i ≠ l) (h₃ : j ≠ l) : m l = 0 := by simp [m,spot,h₁,h₃]
  have hv (l : Fin k) : vert l = 0 := by
    by_contra! hnz
    have hl := hvert l hnz
    have ho := outside l (by rintro rfl; omega) (by rintro rfl; omega)
    have hs := hsum l
    omega
  have hm : top i ≤ 1 := by
    have hi := hsum i
    simp [m,spot,hn.symm] at hi
    omega
  have ht : top = spot i (top i) + spot j (top j) := by
    ext l
    by_cases hi : i = l
    · subst l
      simp [spot,hn.symm]
    by_cases hj : j = l
    · subst l
      simp [spot,hn]
    have h₀ := outside l hi hj
    have hs := hsum l
    simp [spot,hi,hj]
    omega
  have harea : area top = top i + 3*top j := by
    calc
      area top = area (spot i (top i) + spot j (top j)) := congrArg area ht
      _ = _ := by simp [area_add, area_spot, hai, haj]
  simp [hv,harea] at htop
  omega

theorem subsequence_lower (k : ℕ) (hk : 3 ≤ k) :
    ∃ C : ℕ, 0 < C ∧ ∀ N, ∃ n ≥ N, (n+1)^exponent k ≤ C * defect k n := by
  by_cases large : 6 ≤ k
  · obtain ⟨C,A,hC,h⟩ := odd_lower k large
    refine ⟨C,hC,fun N => ⟨2*(A+N)+1, by omega, h _ (by omega) ⟨A+N,rfl⟩⟩⟩
  · refine ⟨1,by decide,fun N => ⟨3*N+2,by omega,?_⟩⟩
    have he : exponent k = 0 := by unfold exponent; omega
    obtain ⟨m, hm, _⟩ := small_failure hk N
    have hf : (failures k (3*N+2)).Finite := (multisets_finite k _).subset fun _ h => h.1
    have hpos := (Set.ncard_pos hf).mpr ⟨m,hm⟩
    simp [he,defect_eq_failures]
    omega

end TaskP.RectangleDefect.Lower
