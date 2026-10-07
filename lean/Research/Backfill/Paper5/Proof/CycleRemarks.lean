import Research.Backfill.Paper5.Challenge

set_option autoImplicit false

namespace CodexPaper5

open BackfillPaper5 Function

namespace CycleRemarks

/-- The parity map respects the right-action convention: opposite multiplication reverses the
factors, but the target is commutative. -/
theorem sgn_mul {r : ℕ} (g h : Challenge.Sym r) :
    Challenge.sgn (g * h) = Challenge.sgn g + Challenge.sgn h := by
  rcases Int.units_eq_one_or (Equiv.Perm.sign (MulOpposite.unop g)) with hg | hg <;>
    rcases Int.units_eq_one_or (Equiv.Perm.sign (MulOpposite.unop h)) with hh | hh <;>
    norm_num [Challenge.sgn, MulOpposite.unop_mul, Equiv.Perm.sign_mul, hg, hh]
  all_goals decide

@[simp] theorem sgn_inv {r : ℕ} (g : Challenge.Sym r) :
    Challenge.sgn g⁻¹ = Challenge.sgn g := by
  simp [Challenge.sgn]

@[simp] theorem sgn_one {r : ℕ} : Challenge.sgn (1 : Challenge.Sym r) = 0 := by
  simp [Challenge.sgn]

/-- A nonfixed point returning at a prime exponent has that exact minimal period. -/
theorem minimalPeriod_of_prime {H : Type*} (ρ : Equiv.Perm H) (l : H)
    (p : ℕ) (hp : Nat.Prime p) (hne : ρ l ≠ l) (hret : (ρ ^ p) l = l) :
    minimalPeriod ρ l = p := by
  have hper : IsPeriodicPt (ρ : H → H) p l := by
    change (ρ ^ p) l = l
    exact hret
  rcases (Nat.dvd_prime hp).mp hper.minimalPeriod_dvd with hone | hfull
  · exact (hne (minimalPeriod_eq_one_iff_isFixedPt.mp hone)).elim
  · exact hfull

private theorem one_add_eq_zero_iff (z : ZMod 2) : 1 + z = 0 ↔ z = 1 := by
  have hone : (1 : ZMod 2) + 1 = 0 := by decide
  constructor
  · intro h
    have h' := congrArg (fun x : ZMod 2 => 1 + x) h
    simpa only [← add_assoc, hone, zero_add, add_zero] using h'
  · intro h
    rw [h, hone]

end CycleRemarks

/-- A fixed point would contribute the forbidden parity `1 + s(1) = 1`. -/
theorem check_Remark45a : Challenge.Remark45a := by
  intro r H _ P ρ hdiag hcycle l hfixed
  have hm : minimalPeriod ρ l = 1 :=
    minimalPeriod_eq_one_iff_isFixedPt.mpr hfixed
  have hc := hcycle l
  simp [Challenge.CycleCond, hm, hfixed, Challenge.sOf, hdiag,
    Challenge.sgn] at hc

/-- In a two-cycle the two edge signs agree, so their sum and the cycle length vanish mod 2. -/
theorem check_Remark45b : Challenge.Remark45b := by
  intro r H _ P hinv ρ l hne hret hnz
  classical
  have hpow : (ρ ^ 2) l = l := by
    simpa only [pow_two, Equiv.Perm.mul_apply] using hret
  have hm := CycleRemarks.minimalPeriod_of_prime ρ l 2 Nat.prime_two hne hpow
  obtain ⟨p, hp⟩ := Option.ne_none_iff_exists'.mp hnz
  have hr := hinv l (ρ l) p hp
  norm_num [Challenge.CycleCond, hm, Finset.sum_range_succ, hpow,
    Challenge.sOf, hp, hr, CycleRemarks.sgn_inv, CharTwo.add_self_eq_zero]
  decide

/-- For a three-cycle the cycle parity is exactly the parity of the three edge product. -/
theorem check_Remark45c : Challenge.Remark45c := by
  intro r H _ P ρ l pab pbc pca hne hret hab hbc hca
  have hm := CycleRemarks.minimalPeriod_of_prime ρ l 3 Nat.prime_three hne hret
  have hthree : (3 : ZMod 2) = 1 := by decide
  constructor
  · have he : Challenge.CycleCond P ρ l ↔
        1 + (Challenge.sgn pab + Challenge.sgn pbc + Challenge.sgn pca) = 0 := by
      norm_num [Challenge.CycleCond, hm, Finset.sum_range_succ, hret,
        Challenge.sOf, hab, hbc, hca]
      rw [hthree]
    exact he.trans (CycleRemarks.one_add_eq_zero_iff _)
  · rw [CycleRemarks.sgn_mul, CycleRemarks.sgn_mul]

#print axioms CodexPaper5.check_Remark45a
#print axioms CodexPaper5.check_Remark45b
#print axioms CodexPaper5.check_Remark45c

end CodexPaper5
