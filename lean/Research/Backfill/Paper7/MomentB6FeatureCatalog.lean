import Research.Backfill.Paper7.EvenMomentFeature

/-! Source-only candidate by /root/moment_t9_recovery_0906.
Complete original b=6,N=42 positive spectral feature catalog. The proof uses
the original Counts/Perron condition and s2 bound, independently of the b4
catalog. No numerical labelled or canonical cardinality is assumed. -/
set_option autoImplicit false
noncomputable section
namespace Paper7MomentCounts
open BackfillPaper7.Challenge BackfillPaper7.Challenge.Legacy
open scoped BigOperators Classical

def B6FeatureCore (a : Counts) : Prop :=
  (∃ ρ : Fin 8, 3 ≤ value ρ ∧ a ρ = 1 ∧
    ∀ i, value ρ < value i → a i = 0) ∧ s2 6 (a, 0) ≤ 42
#print axioms Paper7MomentCounts.B6FeatureCore

def b6FeatureCatalog : Finset (ℤ × ℤ) :=
  {(9,72), (13,84), (17,96),
   (16,240), (20,252), (24,264), (25,312), (29,324),
   (33,336), (34,384), (38,396), (42,408),
   (25,600), (29,612), (33,624), (34,672), (38,684), (42,696), (41,840),
   (36,1260), (40,1272)}
#print axioms Paper7MomentCounts.b6FeatureCatalog

/-- The original Perron root can only be3,4,5 or6. -/
theorem b6Feature_shape (a : Counts) (ha : B6FeatureCore a) :
    (∃ u : ℕ, u ≤ 2 ∧ s2 6 (a, 0) = ((9 + 4*u : ℕ) : ℤ) ∧
      m4 6 (a, 0) = ((72 + 12*u : ℕ) : ℤ)) ∨
    (∃ u v : ℕ, u ≤ 2 ∧ v ≤ 2 ∧ s2 6 (a, 0) = ((16 + 4*u + 9*v : ℕ) : ℤ) ∧
      m4 6 (a, 0) = ((240 + 12*u + 72*v : ℕ) : ℤ)) ∨
    (∃ u v w : ℕ, u ≤ 2 ∧ v ≤ 2 ∧ w ≤ 2 ∧
      s2 6 (a, 0) = ((25 + 4*u + 9*v + 16*w : ℕ) : ℤ) ∧
      m4 6 (a, 0) = ((600 + 12*u + 72*v + 240*w : ℕ) : ℤ)) ∨
    (∃ u v w t : ℕ, u ≤ 2 ∧ v ≤ 2 ∧ w ≤ 2 ∧ t ≤ 2 ∧
      s2 6 (a, 0) = ((36 + 4*u + 9*v + 16*w + 25*t : ℕ) : ℤ) ∧
      m4 6 (a, 0) = ((1260 + 12*u + 72*v + 240*w + 600*t : ℕ) : ℤ)) := by
  have he : Even (6 : ℕ) := by decide
  rcases ha with ⟨⟨ρ, hρ, hpeak, habove⟩, hbound⟩
  have hterm : (value ρ : ℤ)^2 ≤ s2 6 (a, 0) := by
    have h := Finset.single_le_sum (s := (Finset.univ : Finset (Fin 8)))
      (f := fun i => ((a i).val : ℤ) * (value i : ℤ)^2)
      (fun i _ => mul_nonneg (Int.natCast_nonneg _) (sq_nonneg _)) (Finset.mem_univ ρ)
    simpa [s2, he, hpeak] using h
  have hρupper : value ρ ≤ 6 := by
    have hh := hterm.trans hbound
    fin_cases ρ <;> norm_num [value] at hh <;> norm_num [value]
  have hρcases : ρ = (1 : Fin 8) ∨ ρ = (2 : Fin 8) ∨
      ρ = (3 : Fin 8) ∨ ρ = (4 : Fin 8) := by
    have hv : ρ.val = 1 ∨ ρ.val = 2 ∨ ρ.val = 3 ∨ ρ.val = 4 := by
      unfold value at hρ hρupper
      omega
    rcases hv with h | h | h | h
    · exact Or.inl (Fin.ext h)
    · exact Or.inr (Or.inl (Fin.ext h))
    · exact Or.inr (Or.inr (Or.inl (Fin.ext h)))
    · exact Or.inr (Or.inr (Or.inr (Fin.ext h)))
  rcases hρcases with rfl | rfl | rfl | rfl
  · have hz (i : Fin 8) (hi : 2 ≤ i.val) : a i = 0 :=
      habove i (by unfold value; omega)
    refine Or.inl ⟨(a 0).val, by omega, ?_, ?_⟩
    · norm_num [s2, he, Fin.sum_univ_succ, value, hpeak, hz]
      ring
    · norm_num [m4, he, Fin.sum_univ_succ, value, hpeak, hz]
      ring
  · have hz (i : Fin 8) (hi : 3 ≤ i.val) : a i = 0 :=
      habove i (by unfold value; omega)
    refine Or.inr (Or.inl ⟨(a 0).val, (a 1).val, by omega, by omega, ?_, ?_⟩)
    · norm_num [s2, he, Fin.sum_univ_succ, value, hpeak, hz]
      ring
    · norm_num [m4, he, Fin.sum_univ_succ, value, hpeak, hz]
      ring
  · have hz (i : Fin 8) (hi : 4 ≤ i.val) : a i = 0 :=
      habove i (by unfold value; omega)
    refine Or.inr (Or.inr (Or.inl
      ⟨(a 0).val, (a 1).val, (a 2).val, by omega, by omega, by omega, ?_, ?_⟩))
    · norm_num [s2, he, Fin.sum_univ_succ, value, hpeak, hz]
      ring
    · norm_num [m4, he, Fin.sum_univ_succ, value, hpeak, hz]
      ring
  · have hz (i : Fin 8) (hi : 5 ≤ i.val) : a i = 0 :=
      habove i (by unfold value; omega)
    refine Or.inr (Or.inr (Or.inr
      ⟨(a 0).val, (a 1).val, (a 2).val, (a 3).val,
        by omega, by omega, by omega, by omega, ?_, ?_⟩))
    · norm_num [s2, he, Fin.sum_univ_succ, value, hpeak, hz]
      ring
    · norm_num [m4, he, Fin.sum_univ_succ, value, hpeak, hz]
      ring
#print axioms Paper7MomentCounts.b6Feature_shape

theorem b6Feature_mem_catalog (a : Counts) (ha : B6FeatureCore a) :
    (s2 6 (a, 0), m4 6 (a, 0)) ∈ b6FeatureCatalog := by
  have hbound := ha.2
  rcases b6Feature_shape a ha with
    ⟨u, hu, hs, hm⟩ | ⟨u, v, hu, hv, hs, hm⟩ |
    ⟨u, v, w, hu, hv, hw, hs, hm⟩ | ⟨u, v, w, t, hu, hv, hw, ht, hs, hm⟩
  · rw [hs, hm]
    rw [hs] at hbound
    interval_cases u <;> norm_num [b6FeatureCatalog] at hbound <;> norm_num [b6FeatureCatalog]
  · rw [hs, hm]
    rw [hs] at hbound
    interval_cases u <;> interval_cases v <;> norm_num [b6FeatureCatalog] at hbound <;>
      norm_num [b6FeatureCatalog]
  · rw [hs, hm]
    rw [hs] at hbound
    have hv1 : v ≤ 1 := by omega
    have hw1 : w ≤ 1 := by omega
    interval_cases u <;> interval_cases v <;> interval_cases w <;>
      norm_num [b6FeatureCatalog] at hbound <;> norm_num [b6FeatureCatalog]
  · rw [hs, hm]
    rw [hs] at hbound
    have hv0 : v = 0 := by omega
    have hw0 : w = 0 := by omega
    have ht0 : t = 0 := by omega
    subst v
    subst w
    subst t
    have hu1 : u ≤ 1 := by omega
    interval_cases u <;> norm_num [b6FeatureCatalog] at hbound <;> norm_num [b6FeatureCatalog]
#print axioms Paper7MomentCounts.b6Feature_mem_catalog

def b6FeatureWitness (M : ℤ) : Counts :=
  if M = 72 then ![0,1,0,0,0,0,0,0] else
  if M = 84 then ![1,1,0,0,0,0,0,0] else
  if M = 96 then ![2,1,0,0,0,0,0,0] else
  if M = 240 then ![0,0,1,0,0,0,0,0] else
  if M = 252 then ![1,0,1,0,0,0,0,0] else
  if M = 264 then ![2,0,1,0,0,0,0,0] else
  if M = 312 then ![0,1,1,0,0,0,0,0] else
  if M = 324 then ![1,1,1,0,0,0,0,0] else
  if M = 336 then ![2,1,1,0,0,0,0,0] else
  if M = 384 then ![0,2,1,0,0,0,0,0] else
  if M = 396 then ![1,2,1,0,0,0,0,0] else
  if M = 408 then ![2,2,1,0,0,0,0,0] else
  if M = 600 then ![0,0,0,1,0,0,0,0] else
  if M = 612 then ![1,0,0,1,0,0,0,0] else
  if M = 624 then ![2,0,0,1,0,0,0,0] else
  if M = 672 then ![0,1,0,1,0,0,0,0] else
  if M = 684 then ![1,1,0,1,0,0,0,0] else
  if M = 696 then ![2,1,0,1,0,0,0,0] else
  if M = 840 then ![0,0,1,1,0,0,0,0] else
  if M = 1260 then ![0,0,0,0,1,0,0,0] else
  if M = 1272 then ![1,0,0,0,1,0,0,0] else 0
#print axioms Paper7MomentCounts.b6FeatureWitness

def b6FeaturePeak (M : ℤ) : Fin 8 :=
  if M < 240 then 1 else if M < 600 then 2 else if M < 1260 then 3 else 4
#print axioms Paper7MomentCounts.b6FeaturePeak

theorem b6FeatureCatalog_witness (S M : ℤ) (h : (S, M) ∈ b6FeatureCatalog) :
    B6FeatureCore (b6FeatureWitness M) ∧
      s2 6 (b6FeatureWitness M, 0) = S ∧ m4 6 (b6FeatureWitness M, 0) = M := by
  have he : Even (6 : ℕ) := by decide
  suffices hc :
      3 ≤ value (b6FeaturePeak M) ∧ b6FeatureWitness M (b6FeaturePeak M) = 1 ∧
      (∀ i, value (b6FeaturePeak M) < value i → b6FeatureWitness M i = 0) ∧
      s2 6 (b6FeatureWitness M, 0) ≤ 42 ∧
      s2 6 (b6FeatureWitness M, 0) = S ∧ m4 6 (b6FeatureWitness M, 0) = M by
    exact ⟨⟨⟨b6FeaturePeak M, hc.1, hc.2.1, hc.2.2.1⟩, hc.2.2.2.1⟩,
      hc.2.2.2.2.1, hc.2.2.2.2.2⟩
  simp only [b6FeatureCatalog, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at h
  rcases h with
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩
  all_goals
    norm_num [b6FeatureWitness, b6FeaturePeak, value, s2, m4, he,
      Fin.sum_univ_succ, Fin.forall_fin_succ]
#print axioms Paper7MomentCounts.b6FeatureCatalog_witness

theorem b6FeatureCatalog_iff (S M : ℤ) :
    (S, M) ∈ b6FeatureCatalog ↔
      ∃ a : Counts, B6FeatureCore a ∧ s2 6 (a, 0) = S ∧ m4 6 (a, 0) = M := by
  constructor
  · intro h
    exact ⟨b6FeatureWitness M, b6FeatureCatalog_witness S M h⟩
  · rintro ⟨a, ha, rfl, rfl⟩
    exact b6Feature_mem_catalog a ha
#print axioms Paper7MomentCounts.b6FeatureCatalog_iff

end Paper7MomentCounts
