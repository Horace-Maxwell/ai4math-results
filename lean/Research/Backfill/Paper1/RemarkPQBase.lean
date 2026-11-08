import Research.Backfill.Paper1.EqualParityMax

/-! Exact pq energy table and genuine two-maximizer instances for Remark16.
Compilation and acceptance status is recorded separately. -/
set_option autoImplicit false
namespace CodexPaper1
open BackfillPaper1 Finset ICGGeneral
namespace RemarkPQ

lemma proper_pq_subset {p q : ℕ} (hpq : Challenge.DistinctOddPrimes p q)
    {D : Finset ℕ} (hD : D ⊆ {1, p, q}) : D ⊆ (p*q).properDivisors := by
  have hp := hpq.1
  have hq := hpq.2.1
  have hpl : p < p*q := by simpa using Nat.mul_lt_mul_of_pos_left hq.one_lt hp.pos
  have hql : q < p*q := by simpa using Nat.mul_lt_mul_of_pos_right hp.one_lt hq.pos
  intro d hd
  have hd' := hD hd
  simp only [Finset.mem_insert, Finset.mem_singleton] at hd'
  rcases hd' with rfl | rfl | rfl
  · exact Nat.mem_properDivisors.mpr ⟨one_dvd _, lt_trans hp.one_lt hpl⟩
  · exact Nat.mem_properDivisors.mpr ⟨dvd_mul_right _ _, hpl⟩
  · exact Nat.mem_properDivisors.mpr ⟨dvd_mul_left _ _, hql⟩

def R0 (P Q x y z : ℝ) : ℝ := P*Q*(x-y-z)
def R1 (P Q x y z : ℝ) : ℝ := P*(Q*z-Q*x-y)
def R2 (P Q x y z : ℝ) : ℝ := Q*(P*y-P*x-z)
def R3 (P Q x y z : ℝ) : ℝ := P*Q*x+P*y+Q*z

def normPQ (P Q x y z : ℝ) : ℝ :=
  |R0 P Q x y z| + |R1 P Q x y z| + |R2 P Q x y z| + |R3 P Q x y z|

lemma pq_rows (p q : ℕ) (D : Finset ℕ) (hN : p*q ∉ D) :
    Challenge.triple 1 1 p q (Challenge.divMat p q D) 0 0 =
      R0 ((p:ℝ)-1) ((q:ℝ)-1) (if 1 ∈ D then 1 else 0) (if q ∈ D then 1 else 0) (if p ∈ D then 1 else 0) ∧
    Challenge.triple 1 1 p q (Challenge.divMat p q D) 0 1 =
      R1 ((p:ℝ)-1) ((q:ℝ)-1) (if 1 ∈ D then 1 else 0) (if q ∈ D then 1 else 0) (if p ∈ D then 1 else 0) ∧
    Challenge.triple 1 1 p q (Challenge.divMat p q D) 1 0 =
      R2 ((p:ℝ)-1) ((q:ℝ)-1) (if 1 ∈ D then 1 else 0) (if q ∈ D then 1 else 0) (if p ∈ D then 1 else 0) ∧
    Challenge.triple 1 1 p q (Challenge.divMat p q D) 1 1 =
      R3 ((p:ℝ)-1) ((q:ℝ)-1) (if 1 ∈ D then 1 else 0) (if q ∈ D then 1 else 0) (if p ∈ D then 1 else 0) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  all_goals
    norm_num only [Challenge.triple, Challenge.tEntry, Challenge.divMat,
      Finset.sum_range_succ, Finset.sum_range_zero, R0, R1, R2, R3]
    simp only [true_and, false_and, ite_true, ite_false, hN, pow_zero, pow_one,
      one_mul, mul_one]
    ring

lemma energy_pq {p q : ℕ} (hpq : Challenge.DistinctOddPrimes p q)
    (D : Finset ℕ) (hD : D ⊆ (p*q).properDivisors) :
    Challenge.energy (p*q) D = normPQ ((p:ℝ)-1) ((q:ℝ)-1)
      (if 1 ∈ D then 1 else 0) (if q ∈ D then 1 else 0) (if p ∈ D then 1 else 0) := by
  have hN : p*q ∉ D := fun h => Nat.self_notMem_properDivisors (hD h)
  have he := check_Proposition6 p q 1 1 hpq.1 hpq.2.1 hpq.2.2.1 (by omega) (by omega) D
    (by simpa only [pow_one] using hD)
  simp only [pow_one] at he
  obtain ⟨h0,h1,h2,h3⟩ := pq_rows p q D hN
  rw [he]
  simp [Challenge.l1Mat, Finset.sum_range_succ, h0,h1,h2,h3,normPQ]
  ring

lemma norm_table {P Q : ℝ} (hP : 2 ≤ P) (hQ : 2 ≤ Q) :
    normPQ P Q 1 0 0 = 4*P*Q ∧
    normPQ P Q 0 1 1 = 4*P*Q ∧
    normPQ P Q 0 0 1 = 2*(P+1)*Q ∧
    normPQ P Q 1 0 1 = 2*(P+1)*Q ∧
    normPQ P Q 0 1 0 = 2*(Q+1)*P ∧
    normPQ P Q 1 1 0 = 2*(Q+1)*P ∧
    normPQ P Q 1 1 1 = 2*((P+1)*(Q+1)-1) := by
  have hp0 : 0 ≤ P := by linarith
  have hq0 : 0 ≤ Q := by linarith
  have hp1 : 0 ≤ P-1 := by linarith
  have hq1 : 0 ≤ Q-1 := by linarith
  have hnp : -P-1 ≤ 0 := by linarith
  have hnq : -Q-1 ≤ 0 := by linarith
  have hpp : 0 ≤ P*Q+P := by positivity
  have hpq : 0 ≤ P*Q+Q := by positivity
  have hall : 0 ≤ P*Q+P+Q := by positivity
  have hsum : 0 ≤ P+Q := by linarith
  refine ⟨?_,?_,?_,?_,?_,?_,?_⟩
  all_goals
    norm_num [normPQ,R0,R1,R2,R3,abs_mul,abs_neg,abs_of_nonneg hp0,
      abs_of_nonneg hq0,abs_of_nonneg hp1,abs_of_nonneg hq1,
      abs_of_nonpos hnp,abs_of_nonpos hnq,abs_of_nonneg hpp,
      abs_of_nonneg hpq,abs_of_nonneg hall,abs_of_nonneg hsum]
    ring

lemma energy_table {p q : ℕ} (hpq : Challenge.DistinctOddPrimes p q) :
    Challenge.energy (p*q) {1} = 4*((p:ℝ)-1)*((q:ℝ)-1) ∧
    Challenge.energy (p*q) {p,q} = 4*((p:ℝ)-1)*((q:ℝ)-1) ∧
    Challenge.energy (p*q) {p} = 2*p*((q:ℝ)-1) ∧
    Challenge.energy (p*q) {1,p} = 2*p*((q:ℝ)-1) ∧
    Challenge.energy (p*q) {q} = 2*q*((p:ℝ)-1) ∧
    Challenge.energy (p*q) {1,q} = 2*q*((p:ℝ)-1) ∧
    Challenge.energy (p*q) {1,p,q} = 2*((p*q:ℕ)-1:ℝ) := by
  have hp3 : 3 ≤ p := hpq.1.odd_iff.mp hpq.2.2.2.1
  have hq3 : 3 ≤ q := hpq.2.1.odd_iff.mp hpq.2.2.2.2
  have hpR : (3:ℝ) ≤ p := by exact_mod_cast hp3
  have hqR : (3:ℝ) ≤ q := by exact_mod_cast hq3
  obtain ⟨t1,tpq,tp,t1p,tq,t1q,tall⟩ := norm_table
    (P := (p:ℝ)-1) (Q := (q:ℝ)-1) (by linarith) (by linarith)
  have hpn := hpq.1.ne_one
  have hqn := hpq.2.1.ne_one
  have hne := hpq.2.2.1
  have e1 := energy_pq hpq {1} (proper_pq_subset hpq (by simp))
  have epq := energy_pq hpq {p,q} (proper_pq_subset hpq (by simp))
  have ep := energy_pq hpq {p} (proper_pq_subset hpq (by simp))
  have e1p := energy_pq hpq {1,p} (proper_pq_subset hpq (by simp))
  have eq := energy_pq hpq {q} (proper_pq_subset hpq (by simp))
  have e1q := energy_pq hpq {1,q} (proper_pq_subset hpq (by simp))
  have eall := energy_pq hpq {1,p,q} (proper_pq_subset hpq (by simp))
  simp only [Finset.mem_singleton,Finset.mem_insert,hpn,hqn,hne,Ne.symm hpn,
    Ne.symm hqn,Ne.symm hne,or_false,or_true,ite_true,ite_false] at e1 epq ep e1p eq e1q eall
  refine ⟨?_,?_,?_,?_,?_,?_,?_⟩
  · exact e1.trans t1
  · exact epq.trans tpq
  · simpa only [sub_add_cancel] using ep.trans tp
  · simpa only [sub_add_cancel] using e1p.trans t1p
  · simpa only [sub_add_cancel] using eq.trans tq
  · simpa only [sub_add_cancel] using e1q.trans t1q
  · simpa only [sub_add_cancel,Nat.cast_mul] using eall.trans tall

lemma oddSet_pq (p q : ℕ) : Challenge.oddSet p q 1 1 = {p,q} := by
  have hf : ((range 2 ×ˢ range 2).filter (fun ij => Odd (ij.1+ij.2))) =
      ({(0,1),(1,0)} : Finset (ℕ × ℕ)) := by decide +kernel
  simp [Challenge.oddSet,hf,Finset.pair_comm]

lemma evenSet_pq {p q : ℕ} (hpq : Challenge.DistinctOddPrimes p q) :
    (Challenge.evenSet p q 1 1).erase (p*q) = {1} := by
  have hN : p*q ≠ 1 := by
    simpa only [pow_one] using EqualParityMax.pow_product_ne_one hpq.1 hpq.2.1 hpq.2.2.1 (a:=1) (b:=1) le_rfl
  have hf : ((range 2 ×ˢ range 2).filter (fun ij => Even (ij.1+ij.2))) =
      ({(0,0),(1,1)} : Finset (ℕ × ℕ)) := by decide +kernel
  simp [Challenge.evenSet,hf]
  ext d
  simp only [Finset.mem_erase,Finset.mem_insert,Finset.mem_singleton]
  constructor
  · rintro ⟨hne,h | h⟩
    · exact h
    · exact (hne h).elim
  · intro h
    subst d
    exact ⟨Ne.symm hN,Or.inl rfl⟩

lemma maximum_pq {p q : ℕ} (hpq : Challenge.DistinctOddPrimes p q) :
    Challenge.MaxEnergy (p*q) (4*((p:ℝ)-1)*((q:ℝ)-1)) {{p,q},{1}} := by
  have h := EqualParityMax.maximum_one (m:=1) hpq (by decide)
  have hq3 : 3 ≤ q := hpq.2.1.odd_iff.mp hpq.2.2.2.2
  have hqR : (2:ℝ) < q := by exact_mod_cast (show 2 < q by omega)
  have hd : Challenge.deltaK 1 q = (q:ℝ)-2 := by
    unfold Challenge.deltaK
    apply (div_eq_iff (by linarith : (q:ℝ)+1 ≠ 0)).2
    norm_num
    ring
  have hV : (((p*q:ℕ):ℝ)+(3*(p:ℝ)-4)*Challenge.dClosed 1 q)/2-
      ((p:ℝ)-2)*Challenge.deltaK 1 q = 4*((p:ℝ)-1)*((q:ℝ)-1) := by
    rw [hd]
    norm_num [Challenge.dClosed,Finset.sum_range_succ]
    ring
  simpa only [pow_one,oddSet_pq,evenSet_pq hpq,hV] using h

lemma mult_maximum_pq {p q : ℕ} (hpq : Challenge.DistinctOddPrimes p q) :
    Challenge.MultMaxEnergy p q 1 1 (4*((p:ℝ)-1)*((q:ℝ)-1)) := by
  have hm := maximum_pq hpq
  have hD : Challenge.IsConnSet (p*q) {1} := hm.1 {1} (by simp)
  refine ⟨⟨{1},by simpa only [pow_one] using hD,?_,?_⟩,?_⟩
  · exact ⟨{0},{0},by simp,by simp,by simp⟩
  · simpa only [pow_one] using (energy_table hpq).1
  · intro D hD _hM
    simpa only [pow_one] using (hm.2 D (by simpa only [pow_one] using hD)).1

lemma totient_pq {p q : ℕ} (hpq : Challenge.DistinctOddPrimes p q) :
    (Nat.totient (p*q):ℝ) = ((p:ℝ)-1)*((q:ℝ)-1) := by
  rw [Nat.totient_mul (ICGGeneral.coprime_pq hpq.1 hpq.2.1 hpq.2.2.1),
    Nat.totient_prime hpq.1,Nat.totient_prime hpq.2.1]
  rw [Nat.cast_mul,Nat.cast_sub hpq.1.one_lt.le,Nat.cast_sub hpq.2.1.one_lt.le]
  norm_num

lemma maximum_135 : Challenge.MaxEnergy (5*3^3) 584
    {Challenge.oddSet 5 3 1 3,(Challenge.evenSet 5 3 1 3).erase (5*3^3)} := by
  have h := EqualParityMax.maximum_one (p:=5) (q:=3) (m:=3)
    (by norm_num [Challenge.DistinctOddPrimes]) (by decide)
  norm_num [Challenge.dClosed,Challenge.deltaK,Finset.sum_range_succ] at h
  exact h

lemma maximum_375 : Challenge.MaxEnergy (3*5^3) 1632
    {Challenge.oddSet 3 5 1 3,(Challenge.evenSet 3 5 1 3).erase (3*5^3)} := by
  have h := EqualParityMax.maximum_one (p:=3) (q:=5) (m:=3)
    (by norm_num [Challenge.DistinctOddPrimes]) (by decide)
  norm_num [Challenge.dClosed,Challenge.deltaK,Finset.sum_range_succ] at h
  exact h

#print axioms energy_table
#print axioms maximum_pq
#print axioms mult_maximum_pq
#print axioms maximum_135
#print axioms maximum_375
end RemarkPQ
end CodexPaper1
