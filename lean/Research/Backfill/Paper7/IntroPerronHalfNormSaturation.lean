import Research.Backfill.Paper7.SunCycleSupport

/-! Exact opposite-side norm saturation at a real neighbor set, followed by
three real cycle edges. No coverage or constant-neighbor premise is assumed. -/
set_option autoImplicit false
noncomputable section
open scoped Classical Matrix BigOperators

namespace Paper7IntroHalfNorm
open SimpleGraph Matrix Paper7SunMoments

theorem perron_half_norm_neighbor_saturation
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (a c : V) (hca : G.Adj c a)
    (eps f : V → ℝ) (hs : ∀ v, eps v = 1 ∨ eps v = -1)
    (hflip : ∀ u v, G.Adj u v → eps u = -eps v)
    (hf : ∀ v, 0 < f v) (hAf : G.adjMatrix ℝ *ᵥ f = (3 : ℝ) • f)
    (hplus : (∑ v, if eps v = 1 then f v ^ 2 else 0) = (f ⬝ᵥ f) / 2)
    (hminus : (∑ v, if eps v = -1 then f v ^ 2 else 0) = (f ⬝ᵥ f) / 2)
    (β : ℝ)
    (hsum : 3 * f c - f a = ((G.degree c - 1 : ℕ) : ℝ) * β)
    (hnorm : (f ⬝ᵥ f) / 2 = f a ^ 2 + ((G.degree c - 1 : ℕ) : ℝ) * β ^ 2) :
    ∀ v, eps v = -eps c → v ≠ a → G.Adj c v ∧ f v = β := by
  let D := (G.neighborFinset c).erase a
  let S := Finset.univ.filter (fun v : V => eps v = -eps c)
  let R := S \ G.neighborFinset c
  have haN : a ∈ G.neighborFinset c := (G.mem_neighborFinset c a).mpr hca
  have hDcard : D.card = G.degree c - 1 := by
    simp only [D, Finset.card_erase_of_mem haN, G.card_neighborFinset_eq_degree]
  have hNS : G.neighborFinset c ⊆ S := by
    intro v hv
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ v, ?_⟩
    have he := hflip c v ((G.mem_neighborFinset c v).mp hv)
    linarith only [he]
  have hside : ∑ v ∈ S, f v ^ 2 = (f ⬝ᵥ f) / 2 := by
    rcases hs c with he | he
    · simpa only [S, Finset.sum_filter, he] using hminus
    · simpa only [S, Finset.sum_filter, he, neg_neg] using hplus
  have hrow : ∑ v ∈ G.neighborFinset c, f v = 3 * f c := by
    simpa only [G.adjMatrix_mulVec_apply, Pi.smul_apply, smul_eq_mul] using congrFun hAf c
  have hDsum : ∑ v ∈ D, f v = (D.card : ℝ) * β := by
    have he := Finset.sum_erase_add (G.neighborFinset c) f haN
    change (∑ v ∈ D, f v) + f a = ∑ v ∈ G.neighborFinset c, f v at he
    rw [hDcard]
    linarith only [he, hrow, hsum]
  have hsplit : (∑ v ∈ R, f v ^ 2) + (∑ v ∈ G.neighborFinset c, f v ^ 2) =
      ∑ v ∈ S, f v ^ 2 := Finset.sum_sdiff hNS
  have herase : (∑ v ∈ D, f v ^ 2) + f a ^ 2 =
      ∑ v ∈ G.neighborFinset c, f v ^ 2 :=
    Finset.sum_erase_add (G.neighborFinset c) (fun v => f v ^ 2) haN
  have hvariance : (∑ v ∈ D, (f v - β) ^ 2) =
      (∑ v ∈ D, f v ^ 2) - 2 * β * (∑ v ∈ D, f v) + (D.card : ℝ) * β ^ 2 := by
    calc
      _ = ∑ v ∈ D, (f v ^ 2 - (2 * β) * f v + β ^ 2) := by
        apply Finset.sum_congr rfl
        intro v _hv
        ring
      _ = _ := by
        simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib,
          ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul]
  have hnormD : (f ⬝ᵥ f) / 2 = f a ^ 2 + (D.card : ℝ) * β ^ 2 := by
    simpa only [hDcard] using hnorm
  have hzero : (∑ v ∈ D, (f v - β) ^ 2) + (∑ v ∈ R, f v ^ 2) = 0 := by
    rw [hvariance, hDsum]
    nlinarith only [hsplit, herase, hside, hnormD]
  have hDnonneg : 0 ≤ ∑ v ∈ D, (f v - β) ^ 2 :=
    Finset.sum_nonneg (fun v _hv => sq_nonneg (f v - β))
  have hRnonneg : 0 ≤ ∑ v ∈ R, f v ^ 2 :=
    Finset.sum_nonneg (fun v _hv => sq_nonneg (f v))
  have hDzero : (∑ v ∈ D, (f v - β) ^ 2) = 0 := by
    linarith only [hzero, hDnonneg, hRnonneg]
  have hRzero : (∑ v ∈ R, f v ^ 2) = 0 := by
    linarith only [hzero, hDnonneg, hRnonneg]
  intro v hv hva
  have hvS : v ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ v, hv⟩
  by_cases hvN : v ∈ G.neighborFinset c
  · have hvD : v ∈ D := Finset.mem_erase.mpr ⟨hva, hvN⟩
    have hle : (f v - β) ^ 2 ≤ ∑ u ∈ D, (f u - β) ^ 2 :=
      Finset.single_le_sum (fun u _hu => sq_nonneg (f u - β)) hvD
    have hz : (f v - β) ^ 2 = 0 := by
      linarith only [hle, hDzero, sq_nonneg (f v - β)]
    exact ⟨(G.mem_neighborFinset c v).mp hvN, sub_eq_zero.mp (sq_eq_zero_iff.mp hz)⟩
  · have hvR : v ∈ R := Finset.mem_sdiff.mpr ⟨hvS, hvN⟩
    have hle : f v ^ 2 ≤ ∑ u ∈ R, f u ^ 2 :=
      Finset.single_le_sum (fun u _hu => sq_nonneg (f u)) hvR
    have hp : 0 < f v ^ 2 := pow_pos (hf v) 2
    exfalso
    linarith only [hle, hRzero, hp]
#print axioms Paper7IntroHalfNorm.perron_half_norm_neighbor_saturation

theorem perron_half_norm_cycle_contradiction
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (a c : V) (hca : G.Adj c a)
    (eps f : V → ℝ) (hs : ∀ v, eps v = 1 ∨ eps v = -1)
    (hflip : ∀ u v, G.Adj u v → eps u = -eps v)
    (hf : ∀ v, 0 < f v) (hAf : G.adjMatrix ℝ *ᵥ f = (3 : ℝ) • f)
    (hplus : (∑ v, if eps v = 1 then f v ^ 2 else 0) = (f ⬝ᵥ f) / 2)
    (hminus : (∑ v, if eps v = -1 then f v ^ 2 else 0) = (f ⬝ᵥ f) / 2)
    (β : ℝ)
    (hsum : 3 * f c - f a = ((G.degree c - 1 : ℕ) : ℝ) * β)
    (hnorm : (f ⬝ᵥ f) / 2 = f a ^ 2 + ((G.degree c - 1 : ℕ) : ℝ) * β ^ 2)
    (hbad : 7 * β < 3 * f c)
    {r : V} (walk : G.Walk r r) (hw : walk.IsCycle)
    (hc : c ∈ walk.support) (ha : a ∉ walk.support) : False := by
  have hsat := perron_half_norm_neighbor_saturation
    G a c hca eps f hs hflip hf hAf hplus hminus β hsum hnorm
  obtain ⟨u, hu, _u', _hu', hcu, _hcu', _huu'⟩ := cycle_two_neighbors walk hw c hc
  obtain ⟨p, hp, q, hq, hup, huq, hpq⟩ := cycle_two_neighbors walk hw u hu
  have hexz : ∃ z ∈ walk.support, G.Adj u z ∧ z ≠ c := by
    by_cases hpc : p = c
    · refine ⟨q, hq, huq, ?_⟩
      intro hqc
      exact hpq (hpc.trans hqc.symm)
    · exact ⟨p, hp, hup, hpc⟩
  obtain ⟨z, hz, huz, hzc⟩ := hexz
  obtain ⟨p', hp', q', hq', hzp', hzq', hpq'⟩ := cycle_two_neighbors walk hw z hz
  have hexv : ∃ v ∈ walk.support, G.Adj z v ∧ v ≠ u := by
    by_cases hpu : p' = u
    · refine ⟨q', hq', hzq', ?_⟩
      intro hqu
      exact hpq' (hpu.trans hqu.symm)
    · exact ⟨p', hp', hzp', hpu⟩
  obtain ⟨v, hv, hzv, hvu⟩ := hexv
  have hua : u ≠ a := fun he => ha (he ▸ hu)
  have hva : v ≠ a := fun he => ha (he ▸ hv)
  have hsignu : eps u = -eps c := by linarith only [hflip c u hcu]
  have hsignv : eps v = -eps c := by
    linarith only [hflip c u hcu, hflip u z huz, hflip z v hzv]
  have hfu : f u = β := (hsat u hsignu hua).2
  have hfv : f v = β := (hsat v hsignv hva).2
  have hrow (x : V) : ∑ y ∈ G.neighborFinset x, f y = 3 * f x := by
    simpa only [G.adjMatrix_mulVec_apply, Pi.smul_apply, smul_eq_mul] using congrFun hAf x
  have htwo {x y z' : V} (hxy : G.Adj x y) (hxz : G.Adj x z') (hyz : y ≠ z') :
      f y + f z' ≤ 3 * f x := by
    have hsub : ({y, z'} : Finset V) ⊆ G.neighborFinset x := by
      intro j hj
      simp only [Finset.mem_insert, Finset.mem_singleton] at hj
      rcases hj with hjy | hjz
      · rw [hjy]
        exact (G.mem_neighborFinset x y).mpr hxy
      · rw [hjz]
        exact (G.mem_neighborFinset x z').mpr hxz
    have he : (∑ j ∈ ({y, z'} : Finset V), f j) ≤
        ∑ j ∈ G.neighborFinset x, f j :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub
        (fun j _hj _hnj => le_of_lt (hf j))
    have hsmall : (∑ j ∈ ({y, z'} : Finset V), f j) = f y + f z' := by simp [hyz]
    rw [hsmall, hrow x] at he
    exact he
  have hupper := htwo hcu.symm huz hzc.symm
  have hlower := htwo huz.symm hzv hvu.symm
  rw [hfu] at hupper
  rw [hfu, hfv] at hlower
  linarith only [hupper, hlower, hbad]
#print axioms Paper7IntroHalfNorm.perron_half_norm_cycle_contradiction

end Paper7IntroHalfNorm
