import Research.Backfill.Paper5.Challenge

set_option autoImplicit false

namespace CodexPaper5.CyclePotential

open Function
open scoped BigOperators

variable {H : Type}

/-- The quotient by the actual cycles of the permutation. -/
def cycleClass (ρ : Equiv.Perm H) (x : H) : Quotient (Equiv.Perm.SameCycle.setoid ρ) :=
  Quotient.mk _ x

/-- Choosing from the quotient, rather than separately for each vertex, fixes one base per cycle. -/
noncomputable def base (ρ : Equiv.Perm H) (x : H) : H := (cycleClass ρ x).out

theorem base_sameCycle (ρ : Equiv.Perm H) (x : H) : ρ.SameCycle (base ρ x) x := by
  exact Quotient.mk_out' (s₁ := Equiv.Perm.SameCycle.setoid ρ) x

theorem base_apply (ρ : Equiv.Perm H) (x : H) : base ρ (ρ x) = base ρ x := by
  have hq : cycleClass ρ (ρ x) = cycleClass ρ x := by
    apply Quotient.sound
    exact (Equiv.Perm.SameCycle.refl ρ x).apply_left
  exact congrArg (fun q : Quotient (Equiv.Perm.SameCycle.setoid ρ) => q.out) hq

/-- The length of the cycle, measured at its stable base. -/
noncomputable def period (ρ : Equiv.Perm H) (x : H) : ℕ := minimalPeriod ρ (base ρ x)

theorem period_apply (ρ : Equiv.Perm H) (x : H) : period ρ (ρ x) = period ρ x := by
  simp only [period, base_apply]

theorem period_pos [Finite H] (ρ : Equiv.Perm H) (x : H) : 0 < period ρ x :=
  Function.minimalPeriod_pos_of_mem_periodicPts (ρ.injective.mem_periodicPts (base ρ x))

/-- Every vertex has a bounded natural coordinate relative to the stable base of its cycle. -/
theorem coordinate_exists [Finite H] (ρ : Equiv.Perm H) (x : H) :
    ∃ k : ℕ, k < period ρ x ∧ (ρ ^ k) (base ρ x) = x := by
  obtain ⟨n, hn⟩ := (base_sameCycle ρ x).exists_nat_pow_eq
  refine ⟨n % period ρ x, Nat.mod_lt _ (period_pos ρ x), ?_⟩
  exact (Function.iterate_mod_minimalPeriod_eq
    (f := (ρ : H → H)) (x := base ρ x) (n := n)).trans hn

noncomputable def coordinate [Finite H] (ρ : Equiv.Perm H) (x : H) : ℕ :=
  Classical.choose (coordinate_exists ρ x)

theorem coordinate_spec [Finite H] (ρ : Equiv.Perm H) (x : H) :
    coordinate ρ x < period ρ x ∧ (ρ ^ coordinate ρ x) (base ρ x) = x :=
  Classical.choose_spec (coordinate_exists ρ x)

theorem coordinate_lt [Finite H] (ρ : Equiv.Perm H) (x : H) :
    coordinate ρ x < period ρ x := (coordinate_spec ρ x).1

theorem coordinate_pow [Finite H] (ρ : Equiv.Perm H) (x : H) :
    (ρ ^ coordinate ρ x) (base ρ x) = x := (coordinate_spec ρ x).2

/-- Bounded coordinates are unique; this removes dependence on the choice implementation. -/
theorem coordinate_eq [Finite H] (ρ : Equiv.Perm H) (x : H) (k : ℕ)
    (hk : k < period ρ x) (he : (ρ ^ k) (base ρ x) = x) : coordinate ρ x = k := by
  apply (Function.iterate_eq_iterate_iff_of_lt_minimalPeriod
    (f := (ρ : H → H)) (x := base ρ x) (coordinate_lt ρ x) hk).mp
  exact (coordinate_pow ρ x).trans he.symm

theorem coordinate_apply_of_lt [Finite H] (ρ : Equiv.Perm H) (x : H)
    (hlt : coordinate ρ x + 1 < period ρ x) :
    coordinate ρ (ρ x) = coordinate ρ x + 1 := by
  apply coordinate_eq ρ (ρ x) (coordinate ρ x + 1)
  · simpa only [period_apply] using hlt
  · rw [base_apply, pow_succ', Equiv.Perm.mul_apply, coordinate_pow]

theorem coordinate_apply_of_eq [Finite H] (ρ : Equiv.Perm H) (x : H)
    (hend : coordinate ρ x + 1 = period ρ x) : coordinate ρ (ρ x) = 0 := by
  have hnext : ρ x = base ρ x := by
    calc
      ρ x = ρ ((ρ ^ coordinate ρ x) (base ρ x)) := congrArg ρ (coordinate_pow ρ x).symm
      _ = (ρ ^ (coordinate ρ x + 1)) (base ρ x) := by
        rw [pow_succ', Equiv.Perm.mul_apply]
      _ = (ρ ^ period ρ x) (base ρ x) := by rw [hend]
      _ = base ρ x := Function.iterate_minimalPeriod (f := (ρ : H → H)) (x := base ρ x)
  apply coordinate_eq ρ (ρ x) 0 (period_pos ρ (ρ x))
  change base ρ (ρ x) = ρ x
  rw [base_apply]
  exact hnext.symm

/-- Prefix sum of the actual weight function along powers of the permutation. -/
def prefixSum (ρ : Equiv.Perm H) (w : H → ZMod 2) (b : H) (k : ℕ) : ZMod 2 :=
  ∑ t ∈ Finset.range k, w ((ρ ^ t) b)

theorem prefix_zero (ρ : Equiv.Perm H) (w : H → ZMod 2) (b : H) :
    prefixSum ρ w b 0 = 0 := by simp only [prefixSum, Finset.range_zero, Finset.sum_empty]

theorem prefix_succ (ρ : Equiv.Perm H) (w : H → ZMod 2) (b : H) (k : ℕ) :
    prefixSum ρ w b (k + 1) = prefixSum ρ w b k + w ((ρ ^ k) b) := by
  simp only [prefixSum, Finset.sum_range_succ]

noncomputable def potential [Finite H] (ρ : Equiv.Perm H) (w : H → ZMod 2) (x : H) : ZMod 2 :=
  prefixSum ρ w (base ρ x) (coordinate ρ x)

/-- The full-cycle zero sum is exactly what makes the last-to-first edge satisfy the same
recurrence as every internal edge. Fixed points are covered by the same wrap-around argument. -/
theorem potential_step [Finite H] (ρ : Equiv.Perm H) (w : H → ZMod 2)
    (hcycle : ∀ b : H, ∑ t ∈ Finset.range (minimalPeriod ρ b), w ((ρ ^ t) b) = 0)
    (x : H) : potential ρ w (ρ x) = potential ρ w x + w x := by
  change prefixSum ρ w (base ρ (ρ x)) (coordinate ρ (ρ x)) =
    prefixSum ρ w (base ρ x) (coordinate ρ x) + w x
  by_cases hlt : coordinate ρ x + 1 < period ρ x
  · rw [base_apply, coordinate_apply_of_lt ρ x hlt, prefix_succ, coordinate_pow]
  · have hend : coordinate ρ x + 1 = period ρ x := by
      have hk := coordinate_lt ρ x
      omega
    rw [base_apply, coordinate_apply_of_eq ρ x hend, prefix_zero]
    have hsum : prefixSum ρ w (base ρ x) (coordinate ρ x + 1) = 0 := by
      rw [hend]
      exact hcycle (base ρ x)
    rw [prefix_succ, coordinate_pow] at hsum
    exact hsum.symm

/-- General finite permutation potential theorem; no enumeration or bound on H is assumed. -/
theorem exists_potential [Finite H] (ρ : Equiv.Perm H) (w : H → ZMod 2)
    (hcycle : ∀ b : H, ∑ t ∈ Finset.range (minimalPeriod ρ b), w ((ρ ^ t) b) = 0) :
    ∃ c : H → ZMod 2, ∀ x, c (ρ x) = c x + w x :=
  ⟨potential ρ w, potential_step ρ w hcycle⟩

#print axioms CodexPaper5.CyclePotential.base_apply
#print axioms CodexPaper5.CyclePotential.coordinate_spec
#print axioms CodexPaper5.CyclePotential.coordinate_eq
#print axioms CodexPaper5.CyclePotential.coordinate_apply_of_lt
#print axioms CodexPaper5.CyclePotential.coordinate_apply_of_eq
#print axioms CodexPaper5.CyclePotential.potential_step
#print axioms CodexPaper5.CyclePotential.exists_potential

end CodexPaper5.CyclePotential
