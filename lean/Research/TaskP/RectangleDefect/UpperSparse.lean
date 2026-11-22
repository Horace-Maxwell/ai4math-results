import Research.TaskP.RectangleDefect.UpperCount
namespace TaskP.RectangleDefect
open Challenge

private theorem bound_multiples {k g h L M : ℕ} (J : Finset (Fin k))
    (lower : ∀ i∈J, h ≤ (i.val+1)/g)
    (upper : ∀ i∈J, (i.val+1)/g ≤ L)
    (dvd : ∀ i∈J, g ∣ i.val+1) (hsize : L+1 ≤ M+h) : J.card ≤ M := by
  let key (i : Fin k) := (i.val+1)/g-h
  have maps : Set.MapsTo key (J : Set _) (Finset.range M) := by
    intro i hi
    apply Finset.mem_range.mpr
    dsimp [key]
    have := lower i hi
    have := upper i hi
    omega
  have inj : (J : Set _).InjOn key := by
    intro i hi j hj he
    dsimp [key] at he
    have hi' := lower i hi
    have hj' := lower j hj
    have eq : (i.val+1)/g=(j.val+1)/g := by omega
    have ei := Nat.div_mul_cancel (dvd i hi)
    have ej := Nat.div_mul_cancel (dvd j hj)
    rw [eq] at ei
    exact Fin.ext (by omega)
  simpa using Finset.card_le_card_of_injOn key maps inj

theorem sparse_of_gcd {k : ℕ} (hk : 3 ≤ k) (J : Finset (Fin k))
    (hg : 3 ≤ J.gcd (fun i => i.val+1) ∨
      J.gcd (fun i => i.val+1)=2 ∧ ∀ i∈J, i.val+1≠2) :
    J.card ≤ exponent k+1 := by
  let g := J.gcd (fun i => i.val+1)
  have dv (i : Fin k) (hi : i ∈ J) : g ∣ i.val+1 := Finset.gcd_dvd hi
  unfold exponent
  rcases hg with h | ⟨h,avoid⟩
  · change 3 ≤ g at h
    apply bound_multiples (g:=g) (h:=1) (L:=k/3) J _ _ dv (by omega)
    · intro i hi
      exact Nat.div_pos (Nat.le_of_dvd (by omega) (dv i hi)) (by omega)
    · intro i hi
      have eq := Nat.div_mul_cancel (dv i hi)
      have := Nat.mul_le_mul_left ((i.val+1)/g) h
      have := i.isLt
      omega
  · change g=2 at h
    have d2 (i : Fin k) (hi : i∈J) : 2 ∣ i.val+1 := h ▸ dv i hi
    apply bound_multiples (g:=2) (h:=2) (L:=k/2) J _ _ d2 (by omega)
    · intro i hi
      have := d2 i hi
      have := avoid i hi
      omega
    · intro i _
      have := i.isLt
      omega

theorem upper_of_sparse {k T : ℕ} (hk : 3 ≤ k)
    (h : ∀ n, 0<n → ∀ m∈failures k n, (heavy T m).card ≤ exponent k+1) :
    ∃ C : ℕ, 0<C ∧ ∀ n, 0<n → defect k n ≤ C*(n+1)^exponent k := by
  refine ⟨2^k*(T+1)^k*2^(exponent k),by positivity,fun n hn => ?_⟩
  apply (count_with_sparse_heavy (T:=T) (by omega : 0<k) (h n hn)).trans
  calc
    _ ≤ 2^k * (T+1)^k * (2*(n+1))^exponent k :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega : 2*n+1 ≤ 2*(n+1)) _)
    _ = _ := by rw [Nat.mul_pow, Nat.mul_assoc _ (2 ^ exponent k)]

end TaskP.RectangleDefect
