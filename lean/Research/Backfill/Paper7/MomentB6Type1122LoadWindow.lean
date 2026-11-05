import Research.Backfill.Paper7.MomentB6Type1122CompressedCount

/-! Pending analytic load windows for the original1122 fibre. The catalogue is
used as a set; its moment projection is injective by the existing witness API.
No candidate rectangle or numerical count is evaluated. -/
set_option autoImplicit false
noncomputable section
namespace Paper7MomentCounts
open BackfillPaper7.Challenge BackfillPaper7.Challenge.Legacy
open scoped BigOperators

theorem b6_type1122_catalog_moment_injective
    (x y : ℤ × ℤ) (hx : x ∈ b6FeatureCatalog) (hy : y ∈ b6FeatureCatalog)
    (hM : x.2=y.2) : x=y := by
  have hsx := (b6FeatureCatalog_witness x.1 x.2 hx).2.1
  have hsy := (b6FeatureCatalog_witness y.1 y.2 hy).2.1
  rw [hM] at hsx
  exact Prod.ext (hsx.symm.trans hsy) hM
#print axioms Paper7MomentCounts.b6_type1122_catalog_moment_injective

theorem b6_type1122_catalog_load_bounds (sm : ℤ × ℤ)
    (hsm : sm ∈ b6FeatureCatalog) : 9 ≤ sm.1 ∧ sm.1 ≤ 42 := by
  obtain ⟨hc,hS,_⟩ := b6FeatureCatalog_witness sm.1 sm.2 hsm
  refine ⟨?_,hS ▸ hc.2⟩
  rcases b6Feature_shape (b6FeatureWitness sm.2) hc with
    ⟨u,hu,hs,_⟩ | ⟨u,v,hu,hv,hs,_⟩ |
    ⟨u,v,w,hu,hv,hw,hs,_⟩ | ⟨u,v,w,t,hu,hv,hw,ht,hs,_⟩
  all_goals
    rw [hS] at hs
    push_cast at hs
    omega
#print axioms Paper7MomentCounts.b6_type1122_catalog_load_bounds

def b6Type1122LoadCenter (S : ℤ) : ℕ := (S-6).toNat
#print axioms Paper7MomentCounts.b6Type1122LoadCenter

theorem b6_type1122_load_center_cast (S : ℤ) (hS : 6 ≤ S) :
    (b6Type1122LoadCenter S : ℤ)=S-6 := by
  exact Int.toNat_of_nonneg (by omega)
#print axioms Paper7MomentCounts.b6_type1122_load_center_cast

def b6Type1122QLower (C Z : ℕ) : ℕ := C-Z
#print axioms Paper7MomentCounts.b6Type1122QLower

def b6Type1122QUpper (C Z : ℕ) : ℕ :=
  if Z ≤ C then min Z (36-Z) else min Z (min (36-Z) (C+2-Z))
#print axioms Paper7MomentCounts.b6Type1122QUpper

theorem b6_type1122_q_window_iff (C Z Q : ℕ) (hZ : Z ≤ 36)
    (hload : Z ≤ C+2) :
    (b6Type1122QLower C Z ≤ Q ∧ Q ≤ b6Type1122QUpper C Z) ↔
      (Q ≤ Z ∧ Z+Q ≤ 36 ∧ C ≤ Z+Q ∧ Z+Q ≤ C+max Q 2) := by
  unfold b6Type1122QLower b6Type1122QUpper
  by_cases hz : Z ≤ C
  · rw [ite_eq_left hz]
    constructor
    · rintro ⟨hl,hh⟩
      have hqz := (le_min_iff.mp hh).1
      have hqb := (le_min_iff.mp hh).2
      have hmax := le_max_left Q 2
      omega
    · rintro ⟨hqz,hqb,hlo,hhi⟩
      exact ⟨by omega,le_min hqz (by omega)⟩
  · rw [ite_eq_right hz]
    constructor
    · rintro ⟨hl,hh⟩
      have hqz := (le_min_iff.mp hh).1
      have hqb := (le_min_iff.mp (le_min_iff.mp hh).2).1
      have hql := (le_min_iff.mp (le_min_iff.mp hh).2).2
      have hmax := le_max_right Q 2
      omega
    · rintro ⟨hqz,hqb,hlo,hhi⟩
      have hq : Q ≤ 1 := by
        by_contra hn
        have h2 : 2 ≤ Q := by omega
        rw [max_eq_left h2] at hhi
        omega
      rw [max_eq_right (by omega : Q ≤ 2)] at hhi
      exact ⟨by omega,le_min hqz (le_min (by omega) (by omega))⟩
#print axioms Paper7MomentCounts.b6_type1122_q_window_iff

theorem b6_type1122_guard_at_catalog_iff (sm : ℤ × ℤ)
    (hsm : sm ∈ b6FeatureCatalog) (Z Q : ℕ) :
    b6FeatureGuard (Z+Q) Q sm.2 ↔
      b6Type1122LoadCenter sm.1 ≤ Z+Q ∧
      Z+Q ≤ b6Type1122LoadCenter sm.1+max Q 2 := by
  have hs := b6_type1122_catalog_load_bounds sm hsm
  have hC := b6_type1122_load_center_cast sm.1 (by omega)
  have hmax : ((max Q 2 : ℕ) : ℤ)=max (Q : ℤ) 2 := by
    exact Nat.cast_max Q 2
  constructor
  · rintro ⟨t,ht,hM,hlo,hhi⟩
    have he : t=sm := b6_type1122_catalog_moment_injective t sm ht hsm hM
    subst t
    push_cast at hlo hhi
    omega
  · rintro ⟨hlo,hhi⟩
    refine ⟨sm,hsm,rfl,?_,?_⟩ <;> push_cast <;> omega
#print axioms Paper7MomentCounts.b6_type1122_guard_at_catalog_iff

theorem b6_type1122_load_window_bounds (C Z Q : ℕ)
    (hQ : Q ≤ Z) (hb : Z+Q ≤ 36) (hlo : C ≤ Z+Q)
    (hhi : Z+Q ≤ C+max Q 2) :
    (C+1)/2 ≤ Z ∧ Z ≤ min 36 (C+2) ∧
      b6Type1122QLower C Z ≤ Q ∧ Q ≤ b6Type1122QUpper C Z := by
  have hz : Z ≤ 36 := by omega
  have hl : Z ≤ C+2 := by
    by_cases hq : Q ≤ 2
    · rw [max_eq_right hq] at hhi
      omega
    · rw [max_eq_left (by omega : 2 ≤ Q)] at hhi
      omega
  exact ⟨by omega,le_min hz hl,
    (b6_type1122_q_window_iff C Z Q hz hl).mpr ⟨hQ,hb,hlo,hhi⟩⟩
#print axioms Paper7MomentCounts.b6_type1122_load_window_bounds

/-- The bounds use the six labelled positions, with weights1,2,2,1. -/
theorem b6_type1122_weighted_square_bounds (a b c d : ℕ) :
    (a : ℤ)^2+2*(b : ℤ)^2+2*(c : ℤ)^2+(d : ℤ)^2 ≤
      ((a : ℤ)+2*(b : ℤ)+2*(c : ℤ)+(d : ℤ))^2 ∧
    ((a : ℤ)+2*(b : ℤ)+2*(c : ℤ)+(d : ℤ))^2 ≤
      6*((a : ℤ)^2+2*(b : ℤ)^2+2*(c : ℤ)^2+(d : ℤ)^2) := by
  constructor
  · have hab := mul_nonneg (Int.natCast_nonneg a) (Int.natCast_nonneg b)
    have hac := mul_nonneg (Int.natCast_nonneg a) (Int.natCast_nonneg c)
    have had := mul_nonneg (Int.natCast_nonneg a) (Int.natCast_nonneg d)
    have hbc := mul_nonneg (Int.natCast_nonneg b) (Int.natCast_nonneg c)
    have hbd := mul_nonneg (Int.natCast_nonneg b) (Int.natCast_nonneg d)
    have hcd := mul_nonneg (Int.natCast_nonneg c) (Int.natCast_nonneg d)
    nlinarith only [hab,hac,had,hbc,hbd,hcd,sq_nonneg (b : ℤ),sq_nonneg (c : ℤ)]
  · nlinarith only [sq_nonneg ((a : ℤ)-(d : ℤ)),
      sq_nonneg ((a : ℤ)-(b : ℤ)),sq_nonneg ((a : ℤ)-(c : ℤ)),
      sq_nonneg ((d : ℤ)-(b : ℤ)),sq_nonneg ((d : ℤ)-(c : ℤ)),
      sq_nonneg ((b : ℤ)-(c : ℤ))]
#print axioms Paper7MomentCounts.b6_type1122_weighted_square_bounds

theorem b6_type1122_moment_mass_bounds (z : Fin 4 → ℕ) (Q : ℕ) (M : ℤ)
    (hQ : Q ≤ b6Type1122Total z)
    (hM : M=12+3*(b6Type1122Total z : ℤ)+2*(Q : ℤ)+b6Type1122Squares z) :
    M ≤ 12+5*(b6Type1122Total z : ℤ)+(b6Type1122Total z : ℤ)^2 ∧
      ((b6Type1122Total z : ℤ)+9)^2 ≤ 6*M+9 := by
  have hs := b6_type1122_weighted_square_bounds (z 0) (z 1) (z 2) (z 3)
  have hqi : (Q : ℤ) ≤ b6Type1122Total z := by exact_mod_cast hQ
  have hqn := Int.natCast_nonneg Q
  dsimp [b6Type1122Total,b6Type1122Squares] at hM hqi ⊢
  constructor <;> nlinarith only [hs.1,hs.2,hM,hqi,hqn]
#print axioms Paper7MomentCounts.b6_type1122_moment_mass_bounds

/-- This filters only one analytically bounded mass interval per catalogue item. -/
def b6Type1122MassWindow (S M : ℤ) : Finset ℕ :=
  (Finset.Icc ((b6Type1122LoadCenter S+1)/2)
    (min 36 (b6Type1122LoadCenter S+2))).filter (fun Z =>
      M ≤ 12+5*(Z : ℤ)+(Z : ℤ)^2 ∧ ((Z : ℤ)+9)^2 ≤ 6*M+9)
#print axioms Paper7MomentCounts.b6Type1122MassWindow

theorem b6_type1122_mass_window_mem (S M : ℤ) (Z : ℕ) :
    Z ∈ b6Type1122MassWindow S M ↔
      ((b6Type1122LoadCenter S+1)/2 ≤ Z ∧
       Z ≤ min 36 (b6Type1122LoadCenter S+2)) ∧
      M ≤ 12+5*(Z : ℤ)+(Z : ℤ)^2 ∧ ((Z : ℤ)+9)^2 ≤ 6*M+9 := by
  simp only [b6Type1122MassWindow,Finset.mem_filter,Finset.mem_Icc]
#print axioms Paper7MomentCounts.b6_type1122_mass_window_mem

theorem b6_type1122_candidate_window (z : Fin 4 → ℕ) (Q : ℕ)
    (hg : b6Type1122Guard z Q) (hQ : Q ≤ b6Type1122Total z) :
    ∃ sm ∈ b6FeatureCatalog,
      sm.2=12+3*(b6Type1122Total z : ℤ)+2*(Q : ℤ)+b6Type1122Squares z ∧
      b6Type1122Total z ∈ b6Type1122MassWindow sm.1 sm.2 ∧
      Q ∈ Finset.Icc (b6Type1122QLower (b6Type1122LoadCenter sm.1) (b6Type1122Total z))
        (b6Type1122QUpper (b6Type1122LoadCenter sm.1) (b6Type1122Total z)) := by
  obtain ⟨sm,hsm,hM,hlo,hhi⟩ := hg.2.2
  have hfeature : b6FeatureGuard (b6Type1122Total z+Q) Q sm.2 :=
    ⟨sm,hsm,rfl,hlo,hhi⟩
  have hl := (b6_type1122_guard_at_catalog_iff sm hsm (b6Type1122Total z) Q).mp hfeature
  have hb := b6_type1122_load_window_bounds (b6Type1122LoadCenter sm.1)
    (b6Type1122Total z) Q hQ hg.2.1 hl.1 hl.2
  have hm := b6_type1122_moment_mass_bounds z Q sm.2 hQ hM
  exact ⟨sm,hsm,hM,(b6_type1122_mass_window_mem sm.1 sm.2 _).mpr
    ⟨⟨hb.1,hb.2.1⟩,hm⟩,Finset.mem_Icc.mpr hb.2.2⟩
#print axioms Paper7MomentCounts.b6_type1122_candidate_window

end Paper7MomentCounts
