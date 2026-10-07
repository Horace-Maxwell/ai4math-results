import Research.Backfill.Paper5.Proof.InvolutionEndpoints

set_option autoImplicit false

namespace CodexPaper5.InvolutionEndpointCount

open Function CodexPaper5.InvolutionEndpoints

variable {V : Type*}

/-- Exchanging the two actual involution generators leaves the moving-edge graph unchanged. -/
theorem movingGraph_swap (α β : Equiv.Perm V) : movingGraph α β = movingGraph β α := by
  ext u v
  change (u ≠ v ∧ ((α u = v ∨ β u = v) ∨ (α v = u ∨ β v = u))) ↔
    (u ≠ v ∧ ((β u = v ∨ α u = v) ∨ (β v = u ∨ α v = u)))
  tauto

theorem reachable_alpha (α β : Equiv.Perm V) (a : V) :
    (movingGraph α β).Reachable a (α a) := by
  by_cases h : α a = a
  · rw [h]
  · apply SimpleGraph.Adj.reachable
    change a ≠ α a ∧ ((α a = α a ∨ β a = α a) ∨ (α (α a) = a ∨ β (α a) = a))
    exact ⟨Ne.symm h, Or.inl (Or.inl rfl)⟩

theorem reachable_beta (α β : Equiv.Perm V) (a : V) :
    (movingGraph α β).Reachable a (β a) := by
  rw [movingGraph_swap α β]
  exact reachable_alpha β α a

/-- Every nonnegative product power is joined by a real sequence of generator edges. -/
theorem reachable_pow (α β : Equiv.Perm V) (a : V) (k : ℕ) :
    (movingGraph α β).Reachable a (((α * β) ^ k) a) := by
  induction k with
  | zero => simpa only [pow_zero, Equiv.Perm.one_apply] using
      (SimpleGraph.Reachable.rfl : (movingGraph α β).Reachable a a)
  | succ k ih =>
    have hstep := (reachable_beta α β (((α * β) ^ k) a)).trans
      (reachable_alpha α β (β (((α * β) ^ k) a)))
    simpa only [pow_succ', Equiv.Perm.mul_apply] using ih.trans hstep

/-- On a finite type, every integer orbit point has a nonnegative representative,
so this is the converse actual graph bridge, without a preselected path. -/
theorem reachable_of_sameCycle [Finite V] (α β : Equiv.Perm V) {a b : V}
    (hab : (α * β).SameCycle a b) : (movingGraph α β).Reachable a b := by
  obtain ⟨k, hk⟩ := hab.exists_nat_pow_eq
  rw [← hk]
  exact reachable_pow α β a k

/-- Positive minimal period comes from actual finiteness and bijectivity. -/
theorem period_pos [Finite V] (τ : Equiv.Perm V) (a : V) :
    0 < minimalPeriod (fun v => τ v) a :=
  minimalPeriod_pos_of_mem_periodicPts (τ.injective.mem_periodicPts a)

theorem exists_bounded_coordinate [Finite V] (τ : Equiv.Perm V) {a b : V}
    (hab : τ.SameCycle a b) :
    ∃ k : ℕ, k < minimalPeriod (fun v => τ v) a ∧ (τ ^ k) a = b := by
  obtain ⟨k, hk⟩ := hab.exists_nat_pow_eq
  refine ⟨k % minimalPeriod (fun v => τ v) a, Nat.mod_lt _ (period_pos τ a), ?_⟩
  have h := iterate_mod_minimalPeriod_eq (f := fun v => τ v) (x := a) (n := k)
  change (τ ^ (k % minimalPeriod (fun v => τ v) a)) a = (τ ^ k) a at h
  exact h.trans hk

/-- At an α-fixed start, an α-fixed orbit point gives the even return exponent 2k. -/
theorem even_return_of_alpha_fixed (α β : Equiv.Perm V)
    (hα : Involutive α) (hβ : Involutive β) {a : V} (ha : α a = a)
    (k : ℤ) (hk : α (((α * β) ^ k) a) = ((α * β) ^ k) a) :
    ((α * β) ^ (2 * k)) a = a := by
  let τ := α * β
  have hreflect : (τ ^ (-k)) a = (τ ^ k) a :=
    (alpha_reflect α β hα hβ ha k).symm.trans hk
  calc
    (τ ^ (2 * k)) a = (τ ^ k) ((τ ^ k) a) := by
      rw [show 2 * k = k + k by ring, zpow_add]
      rfl
    _ = (τ ^ k) ((τ ^ (-k)) a) := congrArg _ hreflect.symm
    _ = a := by
      change ((τ ^ k) * (τ ^ (-k))) a = a
      rw [← zpow_add, add_neg_cancel, zpow_zero]
      rfl

/-- A multiple lying below twice its positive modulus is zero or the modulus. -/
theorem eq_zero_or_eq_of_dvd_lt_two_mul {m n : ℕ} (hdiv : m ∣ n)
    (hlt : n < 2 * m) : n = 0 ∨ n = m := by
  obtain ⟨q, hq⟩ := hdiv
  have hq2 : q < 2 := by
    by_contra h
    have h2 : 2 ≤ q := by omega
    have hmul := Nat.mul_le_mul_left m h2
    nlinarith
  interval_cases q <;> simp_all

/-- Exact possible coordinates of an endpoint in one finite component.
The two nonzero alternatives have opposite parity and cannot coexist. -/
theorem endpoint_coordinate [Finite V] (α β : Equiv.Perm V)
    (hα : Involutive α) (hβ : Involutive β) {a : V} (ha : α a = a)
    {k : ℕ} (hk : k < minimalPeriod (fun v => (α * β) v) a)
    (hend : α (((α * β) ^ k) a) = ((α * β) ^ k) a ∨
      β (((α * β) ^ k) a) = ((α * β) ^ k) a) :
    k = 0 ∨ 2 * k = minimalPeriod (fun v => (α * β) v) a ∨
      2 * k + 1 = minimalPeriod (fun v => (α * β) v) a := by
  rcases hend with he | he
  · have hz := even_return_of_alpha_fixed α β hα hβ ha (k : ℤ)
      (by simpa only [zpow_natCast] using he)
    have hcast : 2 * (k : ℤ) = ((2 * k : ℕ) : ℤ) := by omega
    rw [hcast, zpow_natCast] at hz
    have hper : IsPeriodicPt (fun v => (α * β) v) (2 * k) a := hz
    rcases eq_zero_or_eq_of_dvd_lt_two_mul hper.minimalPeriod_dvd (by omega) with h0 | hm
    · left
      omega
    · exact Or.inr (Or.inl hm)
  · have hz := odd_return_of_beta_fixed α β hα hβ ha (k : ℤ)
      (by simpa only [zpow_natCast] using he)
    have hcast : 2 * (k : ℤ) + 1 = ((2 * k + 1 : ℕ) : ℤ) := by omega
    rw [hcast, zpow_natCast] at hz
    have hper : IsPeriodicPt (fun v => (α * β) v) (2 * k + 1) a := hz
    rcases eq_zero_or_eq_of_dvd_lt_two_mul hper.minimalPeriod_dvd (by omega) with h0 | hm
    · omega
    · exact Or.inr (Or.inr hm)

/-- The endpoint count with a chosen first color at the base point. -/
theorem endpoints_at_most_two_of_alpha_fixed [Finite V] (α β : Equiv.Perm V)
    (hα : Involutive α) (hβ : Involutive β) {a b c : V} (ha : α a = a)
    (hb : α b = b ∨ β b = b) (hc : α c = c ∨ β c = c)
    (hab : (movingGraph α β).Reachable a b)
    (hac : (movingGraph α β).Reachable a c) : a = b ∨ a = c ∨ b = c := by
  obtain ⟨k, hklt, hk⟩ := exists_bounded_coordinate (α * β)
    (sameCycle_of_reachable α β hα hβ ha hab)
  obtain ⟨l, hllt, hl⟩ := exists_bounded_coordinate (α * β)
    (sameCycle_of_reachable α β hα hβ ha hac)
  have hkb := endpoint_coordinate α β hα hβ ha hklt (by simpa only [hk] using hb)
  have hlc := endpoint_coordinate α β hα hβ ha hllt (by simpa only [hl] using hc)
  by_cases hk0 : k = 0
  · left
    simpa only [hk0, pow_zero, Equiv.Perm.one_apply] using hk
  by_cases hl0 : l = 0
  · right
    left
    simpa only [hl0, pow_zero, Equiv.Perm.one_apply] using hl
  right
  right
  have hkl : k = l := by omega
  exact hk.symm.trans ((congrArg (fun t : ℕ => ((α * β) ^ t) a) hkl).trans hl)

/-- Any three fixed endpoints in one actual moving-edge component include a repetition. -/
theorem endpoints_at_most_two [Finite V] (α β : Equiv.Perm V)
    (hα : Involutive α) (hβ : Involutive β) {a b c : V}
    (ha : α a = a ∨ β a = a) (hb : α b = b ∨ β b = b)
    (hc : α c = c ∨ β c = c)
    (hab : (movingGraph α β).Reachable a b)
    (hac : (movingGraph α β).Reachable a c) : a = b ∨ a = c ∨ b = c := by
  rcases ha with ha | ha
  · exact endpoints_at_most_two_of_alpha_fixed α β hα hβ ha hb hc hab hac
  · apply endpoints_at_most_two_of_alpha_fixed β α hβ hα ha hb.symm hc.symm
    · rw [movingGraph_swap β α]
      exact hab
    · rw [movingGraph_swap β α]
      exact hac

/-- A return exponent k+l identifies the negative k coordinate with l. -/
theorem negative_power_eq_of_return (τ : Equiv.Perm V) {a : V} (k l : ℤ)
    (hret : (τ ^ (k + l)) a = a) : (τ ^ (-k)) a = (τ ^ l) a := by
  calc
    (τ ^ (-k)) a = (τ ^ (-k)) ((τ ^ (k + l)) a) := congrArg _ hret.symm
    _ = (τ ^ (-k + (k + l))) a := by
      change ((τ ^ (-k)) * (τ ^ (k + l))) a = (τ ^ (-k + (k + l))) a
      rw [← zpow_add]
    _ = (τ ^ l) a := by rw [neg_add_cancel_left]

/-- The other endpoint is the midpoint of the finite product orbit.
Even period gives an α-fixed midpoint; odd period gives a β-fixed midpoint. -/
theorem exists_other_endpoint_of_alpha_fixed [Finite V] (α β : Equiv.Perm V)
    (hα : Involutive α) (hβ : Involutive β) {a : V} (ha : α a = a)
    (hcommon : ∀ v, ¬ (α v = v ∧ β v = v)) :
    ∃ b, b ≠ a ∧ (movingGraph α β).Reachable a b ∧ (α b = b ∨ β b = b) := by
  let τ := α * β
  let m := minimalPeriod (fun v => τ v) a
  have hmpos : 0 < m := period_pos τ a
  have hmne : m ≠ 1 := by
    intro hm
    have hfix : τ a = a := (minimalPeriod_eq_one_iff_isFixedPt).mp hm
    have hβa : β a = a := by
      calc
        β a = α (τ a) := (hα (β a)).symm
        _ = α a := congrArg α hfix
        _ = a := ha
    exact hcommon a ⟨ha, hβa⟩
  have hm2 : 2 ≤ m := by omega
  let k := m / 2
  have hkpos : 0 < k := by dsimp [k]; omega
  have hklt : k < m := by dsimp [k]; omega
  have hp : (τ ^ m) a = a := iterate_minimalPeriod (f := fun v => τ v) (x := a)
  have hpz : (τ ^ (m : ℤ)) a = a := by simpa only [zpow_natCast] using hp
  refine ⟨(τ ^ k) a, ?_, reachable_pow α β a k, ?_⟩
  · intro heq
    have hper : IsPeriodicPt (fun v => τ v) k a := heq
    have hz := hper.eq_zero_of_lt_minimalPeriod hklt
    omega
  · have hparity : m = 2 * k ∨ m = 2 * k + 1 := by dsimp [k]; omega
    rcases hparity with hm | hm
    · left
      have he : (k : ℤ) + (k : ℤ) = (m : ℤ) := by omega
      have hr : (τ ^ ((k : ℤ) + (k : ℤ))) a = a := by rw [he]; exact hpz
      have hfixed : α ((τ ^ (k : ℤ)) a) = (τ ^ (k : ℤ)) a :=
        (alpha_reflect α β hα hβ ha (k : ℤ)).trans
          (negative_power_eq_of_return τ (k : ℤ) (k : ℤ) hr)
      simpa only [zpow_natCast] using hfixed
    · right
      have he : ((k : ℤ) + 1) + (k : ℤ) = (m : ℤ) := by omega
      have hr : (τ ^ (((k : ℤ) + 1) + (k : ℤ))) a = a := by rw [he]; exact hpz
      have hfixed : β ((τ ^ (k : ℤ)) a) = (τ ^ (k : ℤ)) a :=
        (beta_reflect α β hα hβ ha (k : ℤ)).trans
          (negative_power_eq_of_return τ ((k : ℤ) + 1) (k : ℤ) hr)
      simpa only [zpow_natCast] using hfixed

/-- With no common fixed point, a finite endpoint component has a distinct other endpoint. -/
theorem exists_other_endpoint [Finite V] (α β : Equiv.Perm V)
    (hα : Involutive α) (hβ : Involutive β) {a : V}
    (ha : α a = a ∨ β a = a) (hcommon : ∀ v, ¬ (α v = v ∧ β v = v)) :
    ∃ b, b ≠ a ∧ (movingGraph α β).Reachable a b ∧ (α b = b ∨ β b = b) := by
  rcases ha with ha | ha
  · exact exists_other_endpoint_of_alpha_fixed α β hα hβ ha hcommon
  · obtain ⟨b, hba, hab, hb⟩ := exists_other_endpoint_of_alpha_fixed β α hβ hα ha
      (fun v h => hcommon v h.symm)
    refine ⟨b, hba, ?_, hb.symm⟩
    rw [movingGraph_swap α β]
    exact hab

#print axioms CodexPaper5.InvolutionEndpointCount.movingGraph_swap
#print axioms CodexPaper5.InvolutionEndpointCount.reachable_pow
#print axioms CodexPaper5.InvolutionEndpointCount.reachable_of_sameCycle
#print axioms CodexPaper5.InvolutionEndpointCount.period_pos
#print axioms CodexPaper5.InvolutionEndpointCount.exists_bounded_coordinate
#print axioms CodexPaper5.InvolutionEndpointCount.even_return_of_alpha_fixed
#print axioms CodexPaper5.InvolutionEndpointCount.endpoint_coordinate
#print axioms CodexPaper5.InvolutionEndpointCount.endpoints_at_most_two
#print axioms CodexPaper5.InvolutionEndpointCount.negative_power_eq_of_return
#print axioms CodexPaper5.InvolutionEndpointCount.exists_other_endpoint

end CodexPaper5.InvolutionEndpointCount
