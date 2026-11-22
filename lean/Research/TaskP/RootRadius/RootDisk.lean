import Research.TaskP.RootRadius.DiskZero
import Research.TaskP.RootRadius.LogLimit

open Set Metric Filter Polynomial
open scoped Topology
namespace TaskP.GraphRootRadius.Proof
open Challenge

theorem root_disk {c : ℕ} (hc : 0 < c) {ε : ℝ} (hε : 0 < ε) :
    ∃ r : ℝ, 0 < r ∧ r < ε ∧ closedBall (1 : ℂ) r ⊆ Complex.slitPlane ∧
      ∀ v ∈ sphere (1:ℂ) r, v^c ≠ 1 := by
  let F := {v : ℂ | v^c = 1} \ {1}
  have hfin : ({v : ℂ | v^c = 1} : Set ℂ).Finite := by
    simpa [Polynomial.IsRoot.def, sub_eq_zero] using
      finite_setOfPred_isRoot (X_pow_sub_C_ne_zero hc (1:ℂ))
  have hF : Fᶜ ∈ 𝓝 (1:ℂ) := ((hfin.sdiff).isClosed.isOpen_compl).mem_nhds (by simp)
  obtain ⟨d,hd,hd'⟩ := nhds_basis_closedBall.mem_iff.mp
    (inter_mem (Complex.isOpen_slitPlane.mem_nhds Complex.one_mem_slitPlane) hF)
  let r := min d (ε/2)
  have hr : 0 < r := lt_min hd (by positivity)
  have hsub := (closedBall_subset_closedBall (min_le_left d (ε/2))).trans hd'
  refine ⟨r,hr,(min_le_right d (ε/2)).trans_lt (by linarith),fun v hv => (hsub hv).1, ?_⟩
  intro v hv he
  have h1 : v ≠ 1 := by
    rintro rfl
    exact hr.ne (by simpa using hv)
  exact (hsub (sphere_subset_closedBall hv)).2 ⟨he,by simpa using h1⟩

theorem good_disk {a c s : ℕ} (ha : 0 < a) (hc : 0 < c) (hs : 0 < s)
    {ω : ℂ} (hω : ω ≠ 0) (E : ℂ[X]) {r : ℝ}
    (hball : closedBall (1:ℂ) r ⊆ Complex.slitPlane) :
    ∀ᶠ m : ℕ in atTop, ∀ v ∈ closedBall (1:ℂ) r,
      (1+delta c s E (warg a c s m ω v)) ∈ Complex.slitPlane ∧
      (1-(warg a c s m ω v)^a) ∈ Complex.slitPlane := by
  apply compact_eventually (isCompact_closedBall 1 r)
  intro v hv
  have hw := warg_limit ha hc hs hω (Complex.slitPlane_ne_zero (hball hv)) (hm :=
    (tendsto_fst : Tendsto Prod.fst (atTop ×ˢ 𝓝 v) (atTop : Filter ℕ))) (hv := tendsto_snd)
  have hδ := (delta_limit (s := s) hc E hw).const_add 1
  have hO := (hw.pow a).const_sub 1
  simp only [add_zero] at hδ
  simp only [zero_pow ha.ne', sub_zero] at hO
  exact (hδ.eventually (Complex.isOpen_slitPlane.mem_nhds Complex.one_mem_slitPlane)).and
    (hO.eventually (Complex.isOpen_slitPlane.mem_nhds Complex.one_mem_slitPlane))

theorem residual_diff {a c s m : ℕ} {ω v : ℂ} (E : ℂ[X]) (hω : ω ≠ 0)
    (hv : v ∈ Complex.slitPlane)
    (hQ : 1+delta c s E (warg a c s m ω v) ∈ Complex.slitPlane)
    (hW : 1-(warg a c s m ω v)^a ∈ Complex.slitPlane) :
    DifferentiableAt ℂ (residual a c s E ω m) v := by
  have hz : ω*v ≠ 0 := mul_ne_zero hω (Complex.slitPlane_ne_zero hv)
  have hw : DifferentiableAt ℂ (warg a c s m ω) v := by
    unfold warg
    fun_prop
  have hδ : DifferentiableAt ℂ (fun v => delta c s E (warg a c s m ω v)) v := by
    unfold delta
    fun_prop
  have h1 := (hδ.const_add 1).clog hQ
  have h2 := ((hw.pow a).const_sub 1).clog hW
  exact ((h1.const_mul _).sub_const _).sub (((((Complex.differentiableAt_log hv).const_mul _).add_const _).add h2).div_const _)

theorem residual_zeros {a c s : ℕ} (ha : 0 < a) (hc : 0 < c) (hs : 0 < s)
    {ω : ℂ} (hω : ω^c = -1) (E : ℂ[X]) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ m : ℕ in atTop, ∃ v : ℂ, dist v 1 < ε ∧ v ∈ Complex.slitPlane ∧
      1+delta c s E (warg a c s m ω v) ∈ Complex.slitPlane ∧
      1-(warg a c s m ω v)^a ∈ Complex.slitPlane ∧ residual a c s E ω m v = 0 := by
  have hω0 : ω ≠ 0 := by rintro rfl; simp [zero_pow hc.ne'] at hω
  obtain ⟨r,hr,hrε,hsl,hbd⟩ := root_disk hc hε
  have hg := good_disk ha hc hs hω0 E hsl
  have hd : ∀ᶠ m : ℕ in atTop, DiffContOnCl ℂ (residual a c s E ω m) (ball (1:ℂ) r) := by
    filter_upwards [hg] with m h
    apply DifferentiableOn.diffContOnCl_ball _ Set.Subset.rfl
    exact fun v hv => (residual_diff E hω0 (hsl hv) (h v hv).1 (h v hv).2).differentiableWithinAt
  have hz := eventual_zero_of_dip hr hd (by
    simpa using residual_limit ha hc hs hω Complex.one_mem_slitPlane E tendsto_id
      (tendsto_const_nhds (x := (1 : ℂ)))) (by
    intro p hp
    refine ⟨_, ?_, residual_limit ha hc hs hω (hsl (sphere_subset_closedBall hp)) E
      tendsto_fst tendsto_snd⟩
    have ha' : (a:ℂ) ≠ 0 := by exact_mod_cast ha.ne'
    have hc' : (c:ℂ) ≠ 0 := by exact_mod_cast hc.ne'
    have hp' := hbd p hp
    simpa [ha', hc', sub_ne_zero, inv_pow] using hp')
  filter_upwards [hg,hz] with m h ⟨v,hv,he⟩
  exact ⟨v, (mem_closedBall.mp hv).trans_lt hrε, hsl hv, (h v hv).1, (h v hv).2, he⟩

end TaskP.GraphRootRadius.Proof
