import Research.Backfill.Paper1.RemarkPQBase

/-! Exact finite multiplicative-rectangle bounds connected to graphEnergy
through the frozen Proposition6. No Boolean spectral approximation is used.
Compilation and acceptance status is recorded separately. -/
set_option autoImplicit false
namespace CodexPaper1
open BackfillPaper1 Finset
namespace RemarkPQ

lemma mem_rectangle {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hne : p ≠ q)
    (A B : Finset ℕ) (i j : ℕ) :
    p^i*q^j ∈ (A ×ˢ B).image (fun ij => p^ij.1*q^ij.2) ↔ i ∈ A ∧ j ∈ B := by
  constructor
  · intro h
    obtain ⟨⟨a,b⟩,hab,he⟩ := Finset.mem_image.mp h
    obtain ⟨rfl,rfl⟩ := (ICGGeneral.pq_inj hp hq hne).mp he
    exact Finset.mem_product.mp hab
  · intro h
    exact Finset.mem_image.mpr ⟨(i,j),Finset.mem_product.mpr h,rfl⟩

lemma divMat_rectangle {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hne : p ≠ q)
    (A B : Finset ℕ) :
    Challenge.divMat p q ((A ×ˢ B).image (fun ij => p^ij.1*q^ij.2)) =
      fun i j => if i ∈ A ∧ j ∈ B then 1 else 0 := by
  funext i j
  unfold Challenge.divMat
  simp only [mem_rectangle hp hq hne]

set_option maxHeartbeats 2000000 in
lemma mult_upper_135 {D : Finset ℕ}
    (hD : Challenge.IsConnSet (5*3^3) D)
    (hM : Challenge.IsMultSet 5 3 1 3 D) :
    Challenge.energy (5*3^3) D ≤ 512 := by
  rcases hM with ⟨A,B,hA,hB,rfl⟩
  have hN : 5*3^3 ∉ (A ×ˢ B).image (fun ij => 5^ij.1*3^ij.2) :=
    fun h => Nat.self_notMem_properDivisors (hD.2 h)
  have he := check_Proposition6 5 3 1 3 (by norm_num) (by norm_num)
    (by norm_num) (by omega) (by omega)
    ((A ×ˢ B).image (fun ij => 5^ij.1*3^ij.2)) hD.2
  simp only [pow_one] at he
  rw [he,divMat_rectangle (by norm_num : Nat.Prime 5) (by norm_num : Nat.Prime 3) (by norm_num)]
  have hcorner : ¬(1 ∈ A ∧ 3 ∈ B) := by
    intro h
    apply hN
    simpa only [pow_one] using
      (mem_rectangle (by norm_num : Nat.Prime 5) (by norm_num : Nat.Prime 3)
        (by norm_num) A B 1 3).mpr h
  have hAf : A ∈ (range 2).powerset := Finset.mem_powerset.mpr hA
  have hBf : B ∈ (range 4).powerset := Finset.mem_powerset.mpr hB
  fin_cases hAf <;> fin_cases hBf
  all_goals norm_num at hcorner
  all_goals
    norm_num [Challenge.l1Mat,Challenge.triple,Challenge.tEntry,Finset.sum_range_succ]

lemma mult_maximum_135 : Challenge.MultMaxEnergy 5 3 1 3 512 := by
  have hD : Challenge.IsConnSet (5*3^3) {1,9} := by
    unfold Challenge.IsConnSet
    decide +kernel
  refine ⟨⟨{1,9},hD,?_,?_⟩,?_⟩
  · exact ⟨{0},{0,2},by decide +kernel,by decide +kernel,by decide +kernel⟩
  · have he := check_Proposition6 5 3 1 3 (by norm_num) (by norm_num)
      (by norm_num) (by omega) (by omega) {1,9} hD.2
    simp only [pow_one] at he
    simp only [pow_one]
    rw [he]
    norm_num [Challenge.l1Mat,Challenge.triple,Challenge.divMat,Challenge.tEntry,
      Finset.sum_range_succ]
  · intro D hD hM
    exact mult_upper_135 hD hM

lemma not_mult_maximizer_135 (D : Finset ℕ)
    (hmem : D ∈ ({Challenge.oddSet 5 3 1 3,
      (Challenge.evenSet 5 3 1 3).erase (5*3^3)} : Set (Finset ℕ))) :
    ¬Challenge.IsMultSet 5 3 1 3 D := by
  have hconn := maximum_135.1 D hmem
  have he : Challenge.energy (5*3^3) D = 584 :=
    (maximum_135.2 D hconn).2.mpr hmem
  intro hM
  have hbound := mult_upper_135 hconn hM
  rw [he] at hbound
  norm_num at hbound

set_option maxHeartbeats 2000000 in
lemma mult_upper_375 {D : Finset ℕ}
    (hD : Challenge.IsConnSet (3*5^3) D)
    (hM : Challenge.IsMultSet 3 5 1 3 D) :
    Challenge.energy (3*5^3) D ≤ 1472 := by
  rcases hM with ⟨A,B,hA,hB,rfl⟩
  have hN : 3*5^3 ∉ (A ×ˢ B).image (fun ij => 3^ij.1*5^ij.2) :=
    fun h => Nat.self_notMem_properDivisors (hD.2 h)
  have he := check_Proposition6 3 5 1 3 (by norm_num) (by norm_num)
    (by norm_num) (by omega) (by omega)
    ((A ×ˢ B).image (fun ij => 3^ij.1*5^ij.2)) hD.2
  simp only [pow_one] at he
  rw [he,divMat_rectangle (by norm_num : Nat.Prime 3) (by norm_num : Nat.Prime 5) (by norm_num)]
  have hcorner : ¬(1 ∈ A ∧ 3 ∈ B) := by
    intro h
    apply hN
    simpa only [pow_one] using
      (mem_rectangle (by norm_num : Nat.Prime 3) (by norm_num : Nat.Prime 5)
        (by norm_num) A B 1 3).mpr h
  have hAf : A ∈ (range 2).powerset := Finset.mem_powerset.mpr hA
  have hBf : B ∈ (range 4).powerset := Finset.mem_powerset.mpr hB
  fin_cases hAf <;> fin_cases hBf
  all_goals norm_num at hcorner
  all_goals
    norm_num [Challenge.l1Mat,Challenge.triple,Challenge.tEntry,Finset.sum_range_succ]

lemma mult_maximum_375 : Challenge.MultMaxEnergy 3 5 1 3 1472 := by
  have hD : Challenge.IsConnSet (3*5^3) {1,25} := by
    unfold Challenge.IsConnSet
    decide +kernel
  refine ⟨⟨{1,25},hD,?_,?_⟩,?_⟩
  · exact ⟨{0},{0,2},by decide +kernel,by decide +kernel,by decide +kernel⟩
  · have he := check_Proposition6 3 5 1 3 (by norm_num) (by norm_num)
      (by norm_num) (by omega) (by omega) {1,25} hD.2
    simp only [pow_one] at he
    simp only [pow_one]
    rw [he]
    norm_num [Challenge.l1Mat,Challenge.triple,Challenge.divMat,Challenge.tEntry,
      Finset.sum_range_succ]
  · intro D hD hM
    exact mult_upper_375 hD hM

lemma not_mult_maximizer_375 (D : Finset ℕ)
    (hmem : D ∈ ({Challenge.oddSet 3 5 1 3,
      (Challenge.evenSet 3 5 1 3).erase (3*5^3)} : Set (Finset ℕ))) :
    ¬Challenge.IsMultSet 3 5 1 3 D := by
  have hconn := maximum_375.1 D hmem
  have he : Challenge.energy (3*5^3) D = 1632 :=
    (maximum_375.2 D hconn).2.mpr hmem
  intro hM
  have hbound := mult_upper_375 hconn hM
  rw [he] at hbound
  norm_num at hbound

#print axioms mult_maximum_135
#print axioms mult_maximum_375
#print axioms not_mult_maximizer_135
#print axioms not_mult_maximizer_375
end RemarkPQ
end CodexPaper1
