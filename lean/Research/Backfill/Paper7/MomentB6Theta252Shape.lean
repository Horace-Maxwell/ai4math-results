import Research.Backfill.Paper7.MomentB6NineCount

/-! Proposed complete original theta252 shapes by concentration inequalities.
No finite rectangular enumeration, table, target count, or numerical subtraction.
Every ordered coordinate and both Q=0/1 boundary cases remain in the proof. -/
set_option autoImplicit false
noncomputable section
namespace Paper7MomentCounts
open BackfillPaper7.Challenge BackfillPaper7.Challenge.Legacy
open scoped BigOperators Classical

def b6Theta252SingleCapacity (i : Fin 6) : Fin 6 → ℕ :=
  fun k => if k = i then 14 else 0
#print axioms Paper7MomentCounts.b6Theta252SingleCapacity

theorem b6FeatureCatalog_theta252 (sm : ℤ × ℤ) (hsm : sm ∈ b6FeatureCatalog)
    (ht : sm.2 = 252) : sm = (20,252) := by
  simp only [b6FeatureCatalog,Finset.mem_insert,Finset.mem_singleton] at hsm
  rcases hsm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num at *
#print axioms Paper7MomentCounts.b6FeatureCatalog_theta252

theorem b6_theta252_complete_zq_shapes (z : Fin 6 → ℕ) (Q : ℕ)
    (hQ : Q ≤ ∑ i,z i) (hg : b6ZQAccept z Q)
    (ht : 12+3*((∑ i,z i : ℕ) : ℤ)+2*(Q : ℤ)+∑ i,(z i : ℤ)^2 = 252) :
    (∃ i,z = b6Theta252SingleCapacity i ∧ Q = 1) ∨
      (∃ i j,i ≠ j ∧ z = b6TwoPoint 13 1 i j ∧ Q = 14) := by
  have hload : (6+((∑ i,z i : ℕ) : ℤ)+(Q : ℤ))-max (Q : ℤ) 2 ≤ 20 := by
    obtain ⟨sm,hsm,hM,_hS,hl⟩ := hg.2.2
    have he := b6FeatureCatalog_theta252 sm hsm (hM.trans ht)
    rw [he] at hl
    simpa only [Prod.fst,Nat.cast_add,add_assoc] using hl
  have hlarge : 2 ≤ Q → (∑ i,z i) ≤ 14 := by
    intro htwo
    have htwoI : (2 : ℤ) ≤ Q := by exact_mod_cast htwo
    have hl := hload
    rw [max_eq_left htwoI] at hl
    exact_mod_cast (show ((∑ i,z i : ℕ) : ℤ) ≤ 14 by omega)
  have hsmall : Q ≤ 1 → (∑ i,z i)+Q ≤ 16 := by
    intro hone
    have honeI : (Q : ℤ) ≤ 2 := by exact_mod_cast (show Q ≤ 2 by omega)
    have hl := hload
    rw [max_eq_right honeI] at hl
    exact_mod_cast (show ((∑ i,z i : ℕ) : ℤ)+(Q : ℤ) ≤ 16 by omega)
  have hZ16 : (∑ i,z i) ≤ 16 := by
    by_cases htwo : 2 ≤ Q
    · have h := hlarge htwo; omega
    · have h := hsmall (by omega); omega
  have hQ14 : Q ≤ 14 := by
    by_cases htwo : 2 ≤ Q
    · have h := hlarge htwo; omega
    · omega
  have hQ0 : (0 : ℤ) ≤ Q := Int.natCast_nonneg Q
  have hQ14I : (Q : ℤ) ≤ 14 := by exact_mod_cast hQ14
  have hcap : (Q : ℤ) ≤ ((∑ i,z i : ℕ) : ℤ) := by exact_mod_cast hQ
  have hex : ∃ i : Fin 6,12 ≤ z i := by
    by_contra hn
    have hall : ∀ i,z i ≤ 11 := by
      intro i
      have hi : ¬ 12 ≤ z i := fun h => hn ⟨i,h⟩
      omega
    have hpoint (i : Fin 6) : (z i : ℤ)^2 ≤ 11*(z i : ℤ) := by
      have hi : (z i : ℤ) ≤ 11 := by exact_mod_cast hall i
      have hp := mul_nonneg (Int.natCast_nonneg (z i)) (sub_nonneg.mpr hi)
      nlinarith only [hp]
    have hs := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin 6))) => hpoint i)
    have hs' : (∑ i,(z i : ℤ)^2) ≤ 11*((∑ i,z i : ℕ) : ℤ) := by
      simpa only [Finset.mul_sum,Nat.cast_sum] using hs
    by_cases htwo : 2 ≤ Q
    · have hZ14I : ((∑ i,z i : ℕ) : ℤ) ≤ 14 := by exact_mod_cast hlarge htwo
      omega
    · have hW16I : ((∑ i,z i : ℕ) : ℤ)+(Q : ℤ) ≤ 16 := by
        exact_mod_cast hsmall (by omega)
      omega
  obtain ⟨i,hi12⟩ := hex
  let r : ℕ := ∑ j ∈ Finset.univ.erase i,z j
  let U : ℤ := ∑ j ∈ Finset.univ.erase i,(z j : ℤ)^2
  have hsplitN : r+z i = ∑ j,z j :=
    Finset.sum_erase_add Finset.univ z (Finset.mem_univ i)
  have hsplitZ : (r : ℤ)+(z i : ℤ) = ((∑ j,z j : ℕ) : ℤ) := by
    exact_mod_cast hsplitN
  have hsplitR : U+(z i : ℤ)^2 = ∑ j,(z j : ℤ)^2 :=
    Finset.sum_erase_add Finset.univ (fun j => (z j : ℤ)^2) (Finset.mem_univ i)
  have hU0 : 0 ≤ U := Finset.sum_nonneg (fun j _ => sq_nonneg (z j : ℤ))
  have hr0 : (0 : ℤ) ≤ r := Int.natCast_nonneg r
  have hm0 : (0 : ℤ) ≤ z i := Int.natCast_nonneg _
  have hm12 : (12 : ℤ) ≤ z i := by exact_mod_cast hi12
  have hr4 : (r : ℤ) ≤ 4 := by omega
  have hUsq : U ≤ (r : ℤ)^2 := by
    simpa only [r,U,Nat.cast_sum] using
      (Finset.sum_sq_le_sq_sum_of_nonneg (s := Finset.univ.erase i)
        (f := fun j => (z j : ℤ)) (fun j _ => Int.natCast_nonneg (z j)))
  have hmle14 : (z i : ℤ) ≤ 14 := by
    by_contra hn
    have hm15 : (15 : ℤ) ≤ z i := by omega
    have hp := mul_nonneg (sub_nonneg.mpr hm15)
      (add_nonneg hm0 (show (0 : ℤ) ≤ 15 by norm_num))
    nlinarith only [ht,hsplitZ,hsplitR,hU0,hr0,hQ0,hm15,hp]
  have hm13 : (13 : ℤ) ≤ z i := by
    by_contra hn
    have hm : (z i : ℤ) = 12 := by omega
    by_cases htwo : 2 ≤ Q
    · have hZ14 : (∑ k,z k) ≤ 14 := hlarge htwo
      have hr2 : (r : ℤ) ≤ 2 := by omega
      have hp := mul_nonneg (sub_nonneg.mpr hr2)
        (add_nonneg (show (0 : ℤ) ≤ 2 by norm_num) hr0)
      nlinarith only [ht,hsplitZ,hsplitR,hm,hUsq,hp,hr2,hQ14I]
    · have hQ1 : (Q : ℤ) ≤ 1 := by omega
      have hp := mul_nonneg (sub_nonneg.mpr hr4)
        (add_nonneg (show (0 : ℤ) ≤ 4 by norm_num) hr0)
      nlinarith only [ht,hsplitZ,hsplitR,hm,hUsq,hp,hr4,hQ1]
  have hmcase : z i = 13 ∨ z i = 14 := by omega
  rcases hmcase with hm | hm
  · have hmI : (z i : ℤ) = 13 := by exact_mod_cast hm
    have htwo : 2 ≤ Q := by
      by_contra hn
      have hQ1 : (Q : ℤ) ≤ 1 := by omega
      have hw := hsmall (by omega)
      have hr3 : (r : ℤ) ≤ 3 := by omega
      have hp := mul_nonneg (sub_nonneg.mpr hr3)
        (add_nonneg (show (0 : ℤ) ≤ 3 by norm_num) hr0)
      nlinarith only [ht,hsplitZ,hsplitR,hmI,hUsq,hp,hr3,hQ1]
    have hz14 := hlarge htwo
    have hr1 : (r : ℤ) ≤ 1 := by omega
    have hpr := mul_nonneg hr0 (sub_nonneg.mpr hr1)
    have he : 3*(r : ℤ)+2*(Q : ℤ)+U = 32 := by
      nlinarith only [ht,hsplitZ,hsplitR,hmI]
    have hr : r = 1 := by
      have hrI : (r : ℤ) = 1 := by
        nlinarith only [he,hUsq,hpr,hcap,hsplitZ,hmI,hr1]
      exact_mod_cast hrI
    have hq : Q = 14 := by
      rw [hr] at he hUsq
      norm_num at hUsq
      omega
    have hmass : (∑ k ∈ Finset.univ.erase i,z k) = 1 := hr
    obtain ⟨j,hjm,hj⟩ := b6_set_mass_one (Finset.univ.erase i) z hmass
    have hij : i ≠ j := Ne.symm (Finset.mem_erase.mp hjm).1
    have hZ : (∑ k,z k) = 13+1 := by omega
    exact Or.inr ⟨i,j,hij,b6_mass_at_two z 13 1 i j hij hm hj hZ,hq⟩
  · have hmI : (z i : ℤ) = 14 := by exact_mod_cast hm
    have he : 3*(r : ℤ)+2*(Q : ℤ)+U = 2 := by
      nlinarith only [ht,hsplitZ,hsplitR,hmI]
    have hr : r = 0 := by
      have hrI : (r : ℤ) = 0 := by omega
      exact_mod_cast hrI
    have hUz : U = 0 := by
      rw [hr] at hUsq
      norm_num at hUsq
      omega
    have hq : Q = 1 := by omega
    refine Or.inl ⟨i,?_,hq⟩
    funext k
    by_cases hki : k = i
    · subst k
      simpa [b6Theta252SingleCapacity] using hm
    · have hk : z k ≤ r := Finset.single_le_sum (fun _ _ => Nat.zero_le _)
        (Finset.mem_erase.mpr ⟨hki,Finset.mem_univ k⟩)
      have hz : z k = 0 := by omega
      simpa [b6Theta252SingleCapacity,hki] using hz
#print axioms Paper7MomentCounts.b6_theta252_complete_zq_shapes

theorem b6_candidate_theta252_shapes (x : PQ 6) (hg : b6CandidateGuard x)
    (htheta : theta x = 252) :
    (∃ i,(fun k => x.1 k+x.2 k) = b6Theta252SingleCapacity i ∧ qSum x = 1) ∨
      (∃ i j,i ≠ j ∧ (fun k => x.1 k+x.2 k) = b6TwoPoint 13 1 i j ∧ qSum x = 14) := by
  let z : Fin 6 → ℕ := fun i => x.1 i+x.2 i
  have hQ : qSum x ≤ ∑ i,z i := by
    apply Finset.sum_le_sum
    intro i _
    dsimp only [z]
    omega
  have ha : b6ZQAccept z (qSum x) :=
    (b6_candB1_on_zq_fibre z (qSum x) x (fun _ => rfl) rfl).mp
      ((b6_candB1_iff_guard x).mpr hg)
  have ht := b6_zq_theta (pqToZQ x)
  have hback : zqToPQ (pqToZQ x) = x := (pqEquivZQ 6).left_inv x
  rw [hback,htheta] at ht
  exact b6_theta252_complete_zq_shapes z (qSum x) hQ ha ht.symm
#print axioms Paper7MomentCounts.b6_candidate_theta252_shapes

end Paper7MomentCounts
