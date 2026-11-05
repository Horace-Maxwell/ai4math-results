import Research.Backfill.Paper7.MomentB4Type112ShortMiddle

/-! SOURCE ONLY. Exact endpoint sum/difference coordinates and recovery of
Q from one original catalogue member. Integer division is guarded by
nonnegativity and divisibility; no negative residual is silently truncated
into an accepted row. The original finite Q and order guards remain. -/
set_option autoImplicit false
noncomputable section
namespace Paper7MomentCanonicalNumeric
open Paper7MomentCounts Paper7MomentCertificate
open scoped BigOperators Classical

def b4Type112DoubleBase (S t D : ℕ) : ℤ :=
  24+12*(t : ℤ)+6*(S : ℤ)+4*(t : ℤ)^2+(S : ℤ)^2+(D : ℤ)^2
#print axioms Paper7MomentCanonicalNumeric.b4Type112DoubleBase

theorem type112_twice_theta_sum_difference
    (z : Fin 38) (t : Fin 19) (u : Fin 38) (Q : Fin 19) (hzu : z ≤ u) :
    2*(b4Theta (type112Row (z,t,u,Q)) Q.val+4) =
      b4Type112DoubleBase (z.val+u.val) t.val (u.val-z.val)+4*(Q.val : ℤ) := by
  have hz : z.val ≤ u.val := hzu
  norm_num [b4Theta,type112Row,Fin.sum_univ_four,b4Type112DoubleBase,Nat.cast_sub hz]
  ring
#print axioms Paper7MomentCanonicalNumeric.type112_twice_theta_sum_difference

def b4Type112CatalogResidual (S t D : ℕ) (M : ℤ) : ℤ :=
  2*M-b4Type112DoubleBase S t D
#print axioms Paper7MomentCanonicalNumeric.b4Type112CatalogResidual

def b4Type112RecoveredQ (S t D : ℕ) (M : ℤ) : ℕ :=
  (b4Type112CatalogResidual S t D M / 4).toNat
#print axioms Paper7MomentCanonicalNumeric.b4Type112RecoveredQ

theorem type112_residual_recovery_iff (S t D Q : ℕ) (M : ℤ) :
    2*M = b4Type112DoubleBase S t D+4*(Q : ℤ) ↔
      0 ≤ b4Type112CatalogResidual S t D M ∧
      b4Type112CatalogResidual S t D M % 4 = 0 ∧
      Q = b4Type112RecoveredQ S t D M := by
  simp only [b4Type112RecoveredQ,b4Type112CatalogResidual]
  constructor
  · intro h
    have hr : 2*M-b4Type112DoubleBase S t D = 4*(Q : ℤ) := by omega
    rw [hr]
    omega
  · rintro ⟨hr,hm,hQ⟩
    omega
#print axioms Paper7MomentCanonicalNumeric.type112_residual_recovery_iff

theorem type112_catalog_Q_unique (S t D Q₁ Q₂ : ℕ) (M : ℤ)
    (h₁ : 2*M = b4Type112DoubleBase S t D+4*(Q₁ : ℤ))
    (h₂ : 2*M = b4Type112DoubleBase S t D+4*(Q₂ : ℤ)) : Q₁ = Q₂ := by
  omega
#print axioms Paper7MomentCanonicalNumeric.type112_catalog_Q_unique

def b4Type112RecoveredGuard (S t D : ℕ) (sm : ℤ × ℤ) : Prop :=
  let Q := b4Type112RecoveredQ S t D sm.2
  0 ≤ b4Type112CatalogResidual S t D sm.2 ∧
  b4Type112CatalogResidual S t D sm.2 % 4 = 0 ∧
  Q ≤ 18 ∧ Q ≤ S+2*t ∧ 0 < S+2*t+Q ∧ S+2*t+Q ≤ 37 ∧
    sm.1 ≤ ((4+(S+2*t+Q) : ℕ) : ℤ) ∧
    ((4+(S+2*t+Q) : ℕ) : ℤ)-max (Q : ℤ) 2 ≤ sm.1
#print axioms Paper7MomentCanonicalNumeric.b4Type112RecoveredGuard

theorem type112_accept_iff_recovered_catalog
    (z : Fin 38) (t : Fin 19) (u : Fin 38) (Q : Fin 19) (hzu : z ≤ u) :
    B4CatalogRowAccept (type112Row (z,t,u,Q)) Q.val ↔
      ∃ sm ∈ b4FeatureCatalog,
        b4Type112RecoveredGuard (z.val+u.val) t.val (u.val-z.val) sm ∧
        Q.val = b4Type112RecoveredQ (z.val+u.val) t.val (u.val-z.val) sm.2 := by
  have hs : (∑ i, type112Row (z,t,u,Q) i) = z.val+u.val+2*t.val := by
    norm_num [type112Row,Fin.sum_univ_four]
    omega
  have hM := type112_twice_theta_sum_difference z t u Q hzu
  constructor
  · rintro ⟨hQ,hp,hn,sm,hm,hEq,hlo,hhi⟩
    have he : 2*sm.2 = b4Type112DoubleBase (z.val+u.val) t.val (u.val-z.val)+
        4*(Q.val : ℤ) := by rw [hEq]; exact hM
    have hr := (type112_residual_recovery_iff (z.val+u.val) t.val
      (u.val-z.val) Q.val sm.2).mp he
    refine ⟨sm,hm,?_,hr.2.2⟩
    unfold b4Type112RecoveredGuard
    rw [← hr.2.2]
    rw [hs] at hQ hp hn hlo hhi
    exact ⟨hr.1,hr.2.1,by have := Q.isLt; omega,hQ,hp,by omega,hlo,hhi⟩
  · rintro ⟨sm,hm,hg,hQ⟩
    unfold b4Type112RecoveredGuard at hg
    rw [← hQ] at hg
    rcases hg with ⟨hr,hd,_h18,hQsum,hp,hn,hlo,hhi⟩
    have he := (type112_residual_recovery_iff (z.val+u.val) t.val
      (u.val-z.val) Q.val sm.2).mpr ⟨hr,hd,hQ⟩
    refine ⟨?_,?_,?_,sm,hm,?_,?_,?_⟩
    · rw [hs]; exact hQsum
    · rw [hs]; exact hp
    · rw [hs]; omega
    · omega
    · rw [hs]; exact hlo
    · rw [hs]; exact hhi
#print axioms Paper7MomentCanonicalNumeric.type112_accept_iff_recovered_catalog

theorem type112_recovered_guard_t_lt_thirteen
    (z : Fin 38) (t : Fin 19) (u : Fin 38) (sm : ℤ × ℤ) (hzu : z ≤ u)
    (hm : sm ∈ b4FeatureCatalog)
    (hg : b4Type112RecoveredGuard (z.val+u.val) t.val (u.val-z.val) sm) :
    t.val < 13 := by
  have hQ : b4Type112RecoveredQ (z.val+u.val) t.val (u.val-z.val) sm.2 < 19 := by
    have := hg.2.2.1
    omega
  let Q : Fin 19 :=
    ⟨b4Type112RecoveredQ (z.val+u.val) t.val (u.val-z.val) sm.2,hQ⟩
  have ha := (type112_accept_iff_recovered_catalog z t u Q hzu).mpr
    ⟨sm,hm,hg,rfl⟩
  exact type112_accept_middle_lt_thirteen z t u Q ha
#print axioms Paper7MomentCanonicalNumeric.type112_recovered_guard_t_lt_thirteen

def b4Type112PlainWeight (z t u Q : ℕ) : ℕ :=
  ∑ k : Fin 10, if k.val ≤ t ∧ 2*k.val ≤ Q then
    min z (Q-2*k.val)+1-((Q-2*k.val)-u) else 0
#print axioms Paper7MomentCanonicalNumeric.b4Type112PlainWeight

theorem type112_row_weight_eq_plain
    (z : Fin 38) (t : Fin 19) (u : Fin 38) (Q : Fin 19) :
    b4Type112RowWeight (z,t,u,Q) = b4Type112PlainWeight z.val t.val u.val Q.val := rfl
#print axioms Paper7MomentCanonicalNumeric.type112_row_weight_eq_plain

theorem type112_weight_endpoint_decode (z t u Q : ℕ) (hzu : z ≤ u) :
    b4Type112PlainWeight z t u Q =
      b4Type112PlainWeight ((z+u-(u-z))/2) t ((z+u+(u-z))/2) Q := by
  have hz : (z+u-(u-z))/2 = z := by omega
  have hu : (z+u+(u-z))/2 = u := by omega
  rw [hz,hu]
#print axioms Paper7MomentCanonicalNumeric.type112_weight_endpoint_decode

theorem type112_recovered_fibre_sum (S t D : ℕ) (sm : ℤ × ℤ)
    (w : ℕ → ℕ) :
    (∑ Q : Fin 19, if b4Type112RecoveredGuard S t D sm ∧
      Q.val = b4Type112RecoveredQ S t D sm.2 then w Q.val else 0) =
        if b4Type112RecoveredGuard S t D sm then
          w (b4Type112RecoveredQ S t D sm.2) else 0 := by
  by_cases hg : b4Type112RecoveredGuard S t D sm
  · have hb : b4Type112RecoveredQ S t D sm.2 < 19 := by
      have := hg.2.2.1
      omega
    let q : Fin 19 := ⟨b4Type112RecoveredQ S t D sm.2,hb⟩
    have he (Q : Fin 19) : Q.val = b4Type112RecoveredQ S t D sm.2 ↔ Q = q := by
      change Q.val = q.val ↔ Q = q
      exact Fin.ext_iff.symm
    simp only [hg,true_and,ite_true]
    simp_rw [he]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    rfl
  · simp [hg]
#print axioms Paper7MomentCanonicalNumeric.type112_recovered_fibre_sum

end Paper7MomentCanonicalNumeric
