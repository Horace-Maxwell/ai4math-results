import Mathlib

/-! Uncompiled analytic helpers for the unchanged fourteen-count problem.
Only first and second moments of an arbitrary natural-valued count function
are used. The zero count is deliberately left free until the final cardinality. -/
set_option autoImplicit false
noncomputable section
namespace Paper7EightCount
open scoped BigOperators Classical

def cut (c : Fin 14 → ℕ) (k : Fin 14) : Fin 14 → ℕ :=
  fun j => if j = k then 0 else c j
#print axioms Paper7EightCount.cut

def PosEq (c d : Fin 14 → ℕ) : Prop := ∀ j, 0 < j.val → c j = d j
#print axioms Paper7EightCount.PosEq

structure Moments (c : Fin 14 → ℕ) (S Q M : ℕ) : Prop where
  first : ∑ j, j.val * c j = S
  square : ∑ j, j.val^2 * c j = Q
  cap : ∀ j, M < j.val → c j = 0
#print axioms Paper7EightCount.Moments

theorem cut_split (c w : Fin 14 → ℕ) (k : Fin 14) :
    (∑ j, w j * cut c k j) + w k * c k = ∑ j, w j * c j := by
  have he (j : Fin 14) : w j * cut c k j + (if j = k then w k * c k else 0) =
      w j * c j := by
    by_cases hj : j = k
    · subst j
      simp [cut]
    · simp [cut,hj]
  have h := Finset.sum_congr (s₁ := Finset.univ) rfl (fun j _ => he j)
  simpa [Finset.sum_add_distrib] using h
#print axioms Paper7EightCount.cut_split

theorem first_le_square (c : Fin 14 → ℕ) :
    (∑ j, j.val * c j) ≤ ∑ j, j.val^2 * c j := by
  apply Finset.sum_le_sum
  intro j _
  apply Nat.mul_le_mul_right
  by_cases hj : j.val = 0
  · simp [hj]
  · have hp : 1 ≤ j.val := by omega
    nlinarith
#print axioms Paper7EightCount.first_le_square

theorem Moments.atom_first {c : Fin 14 → ℕ} {S Q M : ℕ}
    (h : Moments c S Q M) (j : Fin 14) : j.val * c j ≤ S := by
  rw [← h.first]
  exact Finset.single_le_sum (f := fun i : Fin 14 => i.val * c i) (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
#print axioms Paper7EightCount.Moments.atom_first

theorem Moments.atom_square {c : Fin 14 → ℕ} {S Q M : ℕ}
    (h : Moments c S Q M) (j : Fin 14) : j.val^2 * c j ≤ Q := by
  rw [← h.square]
  exact Finset.single_le_sum (f := fun i : Fin 14 => i.val^2 * c i) (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
#print axioms Paper7EightCount.Moments.atom_square

theorem Moments.excess_atom {c : Fin 14 → ℕ} {S Q M : ℕ}
    (h : Moments c S Q M) (j : Fin 14) : S + j.val^2 * c j ≤ Q + j.val * c j := by
  have hs := cut_split c (fun i => i.val) j
  have hq := cut_split c (fun i => i.val^2) j
  have hi := first_le_square (cut c j)
  rw [h.first] at hs
  rw [h.square] at hq
  omega
#print axioms Paper7EightCount.Moments.excess_atom

theorem Moments.term_le {c : Fin 14 → ℕ} {S Q M : ℕ}
    (h : Moments c S Q M) (j : Fin 14) : j.val^2 * c j ≤ M * (j.val * c j) := by
  by_cases hj : j.val ≤ M
  · calc
      j.val^2 * c j ≤ (M * j.val) * c j := by
        apply Nat.mul_le_mul_right
        nlinarith
      _ = M * (j.val * c j) := by ring
  · rw [h.cap j (by omega)]
    simp
#print axioms Paper7EightCount.Moments.term_le

theorem Moments.bound {c : Fin 14 → ℕ} {S Q M : ℕ}
    (h : Moments c S Q M) : Q ≤ M * S := by
  calc
    Q = ∑ j, j.val^2 * c j := h.square.symm
    _ ≤ ∑ j, M * (j.val * c j) := Finset.sum_le_sum (fun j _ => h.term_le j)
    _ = M * S := by rw [← Finset.mul_sum,h.first]
#print axioms Paper7EightCount.Moments.bound

theorem Moments.cap_first {c : Fin 14 → ℕ} {S Q M N : ℕ}
    (h : Moments c S Q M) (hN : S ≤ N) : Moments c S Q N := by
  refine ⟨h.first,h.square,?_⟩
  intro j hj
  by_contra hn
  have hc : 1 ≤ c j := by omega
  have hmul := Nat.mul_le_mul_left j.val hc
  have ha := h.atom_first j
  omega
#print axioms Paper7EightCount.Moments.cap_first

theorem Moments.cap_square {c : Fin 14 → ℕ} {S Q M N : ℕ}
    (h : Moments c S Q M) (hN : Q < (N+1)^2) : Moments c S Q N := by
  refine ⟨h.first,h.square,?_⟩
  intro j hj
  by_contra hn
  have hc : 1 ≤ c j := by omega
  have hmul := Nat.mul_le_mul_left (j.val^2) hc
  have ha := h.atom_square j
  have hj' : N+1 ≤ j.val := by omega
  have hpow : (N+1)^2 ≤ j.val^2 := by nlinarith
  nlinarith
#print axioms Paper7EightCount.Moments.cap_square

theorem Moments.lower {c : Fin 14 → ℕ} {S Q N : ℕ}
    (h : Moments c S Q (N+1)) (k : Fin 14) (hk : k.val = N+1)
    (hz : c k = 0) : Moments c S Q N := by
  refine ⟨h.first,h.square,?_⟩
  intro j hj
  by_cases he : j.val = N+1
  · have hjk : j = k := Fin.ext (he.trans hk.symm)
    simpa only [hjk] using hz
  · exact h.cap j (by omega)
#print axioms Paper7EightCount.Moments.lower

theorem Moments.remove {c : Fin 14 → ℕ} {S Q M : ℕ}
    (h : Moments c S Q M) (k : Fin 14) (n S' Q' : ℕ)
    (hk : c k = n) (hs : S' + k.val*n = S) (hq : Q' + k.val^2*n = Q) :
    Moments (cut c k) S' Q' M := by
  have hfirst := cut_split c (fun j => j.val) k
  have hsquare := cut_split c (fun j => j.val^2) k
  rw [hk,h.first] at hfirst
  rw [hk,h.square] at hsquare
  refine ⟨by omega,by omega,?_⟩
  intro j hj
  by_cases he : j = k
  · simp [cut,he]
  · simp [cut,he,h.cap j hj]
#print axioms Paper7EightCount.Moments.remove

theorem Moments.top_bound {c : Fin 14 → ℕ} {S Q N : ℕ}
    (h : Moments c S Q (N+1)) (k : Fin 14) (hk : k.val = N+1) :
    Q ≤ N*S + (N+1)*c k := by
  have hi (j : Fin 14) : j.val^2*c j ≤
      N*(j.val*c j) + (if j = k then (N+1)*c k else 0) := by
    by_cases he : j = k
    · subst j
      simp [hk]
      nlinarith
    · simp only [ite_eq_right he,add_zero]
      by_cases hj : N+1 < j.val
      · rw [h.cap j hj]
        simp
      · have hv : j.val ≠ N+1 := by
          intro hv
          exact he (Fin.ext (hv.trans hk.symm))
        have hjN : j.val ≤ N := by omega
        calc
          j.val^2*c j ≤ (N*j.val)*c j := by
            apply Nat.mul_le_mul_right
            nlinarith
          _ = N*(j.val*c j) := by ring
  calc
    Q = ∑ j, j.val^2*c j := h.square.symm
    _ ≤ ∑ j, (N*(j.val*c j) + if j = k then (N+1)*c k else 0) :=
      Finset.sum_le_sum (fun j _ => hi j)
    _ = N*S + (N+1)*c k := by
      rw [Finset.sum_add_distrib,← Finset.mul_sum,h.first]
      simp
#print axioms Paper7EightCount.Moments.top_bound

theorem Moments.tight_zero {c : Fin 14 → ℕ} {S Q M : ℕ}
    (h : Moments c S Q M) (heq : Q = M*S) (j : Fin 14)
    (hj0 : 0 < j.val) (hjM : j.val < M) : c j = 0 := by
  have hsum : (∑ i, i.val^2*c i) = ∑ i, M*(i.val*c i) := by
    rw [← Finset.mul_sum,h.first,h.square,heq]
  have hi := (Finset.sum_eq_sum_iff_of_le (fun i _ => h.term_le i)).mp hsum j (Finset.mem_univ j)
  by_contra hn
  have hc : 0 < c j := by omega
  have hlt : j.val^2 < M*j.val := by nlinarith
  have hh := Nat.mul_lt_mul_of_pos_right hlt hc
  have hieq : j.val^2*c j = (M*j.val)*c j := by simpa only [mul_assoc] using hi
  omega
#print axioms Paper7EightCount.Moments.tight_zero

theorem Moments.tight_first {c : Fin 14 → ℕ} {S Q M : ℕ}
    (h : Moments c S Q M) (heq : Q = M*S) (k : Fin 14) (hk : k.val = M) :
    S = M*c k := by
  calc
    S = ∑ j, j.val*c j := h.first.symm
    _ = k.val*c k := by
      apply Finset.sum_eq_single k
      · intro j _ hjk
        by_cases hj0 : j.val = 0
        · simp [hj0]
        · by_cases hjM : M < j.val
          · rw [h.cap j hjM]
            simp
          · have hne : j.val ≠ M := by
              intro he
              exact hjk (Fin.ext (he.trans hk.symm))
            rw [h.tight_zero heq j (by omega) (by omega)]
            simp
      · simp
    _ = M*c k := by rw [hk]
#print axioms Paper7EightCount.Moments.tight_first

theorem Moments.single {c : Fin 14 → ℕ} {S Q M : ℕ}
    (h : Moments c S Q M) (heq : Q = M*S) (k : Fin 14) (hk : k.val = M)
    (hM : 0 < M) (n : ℕ) (hS : S = M*n) :
    PosEq c (fun j => if j = k then n else 0) := by
  have hcount : c k = n := Nat.eq_of_mul_eq_mul_left hM ((h.tight_first heq k hk).symm.trans hS)
  intro j hj0
  by_cases he : j = k
  · simpa [he] using hcount
  · simp only [ite_eq_right he]
    by_cases hjM : M < j.val
    · exact h.cap j hjM
    · have hne : j.val ≠ M := by
        intro hv
        exact he (Fin.ext (hv.trans hk.symm))
      exact h.tight_zero heq j hj0 (by omega)
#print axioms Paper7EightCount.Moments.single

theorem PosEq.restore {c v : Fin 14 → ℕ} (k : Fin 14) (n : ℕ)
    (h : PosEq (cut c k) v) (hk : c k = n) :
    PosEq c (fun j => if j = k then n else v j) := by
  intro j hj
  by_cases he : j = k
  · simpa [he] using hk
  · simpa [cut,he] using h j hj
#print axioms Paper7EightCount.PosEq.restore

end Paper7EightCount
