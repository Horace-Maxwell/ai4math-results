import Research.Backfill.Paper2.Challenge

/-!
The Deutsch--Sagan Catalan valuation identity in the frozen Paper 2 contract.
Use choose(2n+1,n)=(2n+1)Catalan(n), whose odd factor has valuation zero.
Kummer then needs only the elementary binary identity s(2n+1)=1+s(n).
-/
set_option autoImplicit false
namespace BackfillPaper2.CatalanValuation
open BackfillPaper2.Challenge

theorem check_RC_DS21 : RC_DS21 := by
  intro n
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hchoose : Nat.choose (2 * n + 1) n = (2 * n + 1) * catalan n := by
    apply Nat.eq_of_mul_eq_mul_right (Nat.succ_pos n)
    calc
      Nat.choose (2 * n + 1) n * (n + 1) = n.centralBinom * (2 * n + 1) := by
        simpa only [Nat.centralBinom, show 2 * n + 1 - n = n + 1 by omega] using
          (Nat.choose_mul_succ_eq (2 * n) n).symm
      _ = ((2 * n + 1) * catalan n) * (n + 1) := by
        rw [← succ_mul_catalan_eq_centralBinom n]
        ring
  have hcn : catalan n ≠ 0 := by
    intro h
    apply Nat.centralBinom_ne_zero n
    rw [← succ_mul_catalan_eq_centralBinom n, h, mul_zero]
  have ho : padicValNat 2 (2 * n + 1) = 0 :=
    padicValNat.eq_zero_of_not_dvd (by omega)
  have hv : padicValNat 2 ((2 * n + 1) * catalan n) = padicValNat 2 (catalan n) := by
    rw [padicValNat.mul (by omega : 2 * n + 1 ≠ 0) hcn, ho, zero_add]
  have hd : Nat.digits 2 (2 * n + 1) = 1 :: Nat.digits 2 n := by
    simpa only [Nat.add_comm] using
      (Nat.digits_add 2 (by omega) 1 n (by omega) (Or.inl (by decide)))
  have hk := sub_one_mul_padicValNat_choose_eq_sub_sum_digits
    (p := 2) (k := n) (n := 2 * n + 1) (by omega)
  rw [hchoose, hv, hd, List.sum_cons,
    show 2 * n + 1 - n = n + 1 by omega] at hk
  norm_num only [Nat.reduceSub, one_mul] at hk
  omega

end BackfillPaper2.CatalanValuation
#print axioms BackfillPaper2.CatalanValuation.check_RC_DS21
