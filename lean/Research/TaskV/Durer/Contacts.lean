import Research.TaskV.Durer.Challenge
import Mathlib.Tactic.NormNum

set_option maxHeartbeats 4000000

namespace DurerDV

private theorem point_eq {p q : V3} (hx : p.x=q.x) (hy : p.y=q.y) (hz : p.z=q.z) :
    p=q := by cases p; cases q; simp_all

private theorem arcZero (s : Solid) (f : Profile) (u : ℝ → ℝ)
    (hu : arcValid s f u) {t : ℝ} (ht : 0 ≤ t) (ht' : t ≤ f.length) (h : u t ≤ 0) :
    t=0 := by
  by_contra! hne
  have hpos := hu.2.1 (show 0 ∈ Set.Icc 0 f.length from ⟨le_rfl,f.length_pos.le⟩)
    (show t ∈ Set.Icc 0 f.length from ⟨ht,ht'⟩) (lt_of_le_of_ne ht (Ne.symm hne))
  linarith [hu.1]

private theorem adjacent (s : Solid) (u v : ℝ → ℝ)
    (hu : arcValid s s.upper u) (hv : arcValid s s.lower v)
    (i j : Chart) (p : V3) (h : rank j = rank i + 1)
    (hi : onChart s i p) (hj : onChart s j p) :
    flat s u v i p = flat s u v j p := by
  rcases hi with ⟨_,hi⟩
  rcases hj with ⟨_,hj⟩
  cases i <;> cases j <;> simp [rank] at h <;>
    dsimp at hi hj <;> simp [flat, perim, hi, hj, hu.1, hv.1] <;> ring

private theorem agree (s : Solid) (u v : ℝ → ℝ)
    (hu : arcValid s s.upper u) (hv : arcValid s s.lower v)
    (i j : Chart) (p q : V3) (h : welded s i j p q) :
    flat s u v i p = flat s u v j q := by
  rcases h with ⟨rfl,h⟩
  have step := adjacent s u v hu hv
  cases i <;> cases j
  case roof.roof =>
    rfl
  case roof.a =>
    have h0 := h .roof (by decide) (by decide)
    have h1 := h .a (by decide) (by decide)
    exact (step .roof .a p (by decide) h0 h1)
  case roof.b =>
    have h0 := h .roof (by decide) (by decide)
    have h1 := h .a (by decide) (by decide)
    have h2 := h .b (by decide) (by decide)
    exact (step .roof .a p (by decide) h0 h1).trans ((step .a .b p (by decide) h1 h2))
  case roof.c =>
    have h0 := h .roof (by decide) (by decide)
    have h1 := h .a (by decide) (by decide)
    have h2 := h .b (by decide) (by decide)
    have h3 := h .c (by decide) (by decide)
    exact (step .roof .a p (by decide) h0 h1).trans ((step .a .b p (by decide) h1 h2).trans ((step .b .c p (by decide) h2 h3)))
  case roof.d =>
    have h0 := h .roof (by decide) (by decide)
    have h1 := h .a (by decide) (by decide)
    have h2 := h .b (by decide) (by decide)
    have h3 := h .c (by decide) (by decide)
    have h4 := h .d (by decide) (by decide)
    exact (step .roof .a p (by decide) h0 h1).trans ((step .a .b p (by decide) h1 h2).trans ((step .b .c p (by decide) h2 h3).trans ((step .c .d p (by decide) h3 h4))))
  case roof.floor =>
    have h0 := h .roof (by decide) (by decide)
    have h1 := h .a (by decide) (by decide)
    have h2 := h .b (by decide) (by decide)
    have h3 := h .c (by decide) (by decide)
    have h4 := h .d (by decide) (by decide)
    have h5 := h .floor (by decide) (by decide)
    exact (step .roof .a p (by decide) h0 h1).trans ((step .a .b p (by decide) h1 h2).trans ((step .b .c p (by decide) h2 h3).trans ((step .c .d p (by decide) h3 h4).trans ((step .d .floor p (by decide) h4 h5)))))
  case a.roof =>
    have h0 := h .roof (by decide) (by decide)
    have h1 := h .a (by decide) (by decide)
    exact (step .roof .a p (by decide) h0 h1).symm
  case a.a =>
    rfl
  case a.b =>
    have h1 := h .a (by decide) (by decide)
    have h2 := h .b (by decide) (by decide)
    exact (step .a .b p (by decide) h1 h2)
  case a.c =>
    have h1 := h .a (by decide) (by decide)
    have h2 := h .b (by decide) (by decide)
    have h3 := h .c (by decide) (by decide)
    exact (step .a .b p (by decide) h1 h2).trans ((step .b .c p (by decide) h2 h3))
  case a.d =>
    have h1 := h .a (by decide) (by decide)
    have h2 := h .b (by decide) (by decide)
    have h3 := h .c (by decide) (by decide)
    have h4 := h .d (by decide) (by decide)
    exact (step .a .b p (by decide) h1 h2).trans ((step .b .c p (by decide) h2 h3).trans ((step .c .d p (by decide) h3 h4)))
  case a.floor =>
    have h1 := h .a (by decide) (by decide)
    have h2 := h .b (by decide) (by decide)
    have h3 := h .c (by decide) (by decide)
    have h4 := h .d (by decide) (by decide)
    have h5 := h .floor (by decide) (by decide)
    exact (step .a .b p (by decide) h1 h2).trans ((step .b .c p (by decide) h2 h3).trans ((step .c .d p (by decide) h3 h4).trans ((step .d .floor p (by decide) h4 h5))))
  case b.roof =>
    have h0 := h .roof (by decide) (by decide)
    have h1 := h .a (by decide) (by decide)
    have h2 := h .b (by decide) (by decide)
    exact (step .a .b p (by decide) h1 h2).symm.trans ((step .roof .a p (by decide) h0 h1).symm)
  case b.a =>
    have h1 := h .a (by decide) (by decide)
    have h2 := h .b (by decide) (by decide)
    exact (step .a .b p (by decide) h1 h2).symm
  case b.b =>
    rfl
  case b.c =>
    have h2 := h .b (by decide) (by decide)
    have h3 := h .c (by decide) (by decide)
    exact (step .b .c p (by decide) h2 h3)
  case b.d =>
    have h2 := h .b (by decide) (by decide)
    have h3 := h .c (by decide) (by decide)
    have h4 := h .d (by decide) (by decide)
    exact (step .b .c p (by decide) h2 h3).trans ((step .c .d p (by decide) h3 h4))
  case b.floor =>
    have h2 := h .b (by decide) (by decide)
    have h3 := h .c (by decide) (by decide)
    have h4 := h .d (by decide) (by decide)
    have h5 := h .floor (by decide) (by decide)
    exact (step .b .c p (by decide) h2 h3).trans ((step .c .d p (by decide) h3 h4).trans ((step .d .floor p (by decide) h4 h5)))
  case c.roof =>
    have h0 := h .roof (by decide) (by decide)
    have h1 := h .a (by decide) (by decide)
    have h2 := h .b (by decide) (by decide)
    have h3 := h .c (by decide) (by decide)
    exact (step .b .c p (by decide) h2 h3).symm.trans ((step .a .b p (by decide) h1 h2).symm.trans ((step .roof .a p (by decide) h0 h1).symm))
  case c.a =>
    have h1 := h .a (by decide) (by decide)
    have h2 := h .b (by decide) (by decide)
    have h3 := h .c (by decide) (by decide)
    exact (step .b .c p (by decide) h2 h3).symm.trans ((step .a .b p (by decide) h1 h2).symm)
  case c.b =>
    have h2 := h .b (by decide) (by decide)
    have h3 := h .c (by decide) (by decide)
    exact (step .b .c p (by decide) h2 h3).symm
  case c.c =>
    rfl
  case c.d =>
    have h3 := h .c (by decide) (by decide)
    have h4 := h .d (by decide) (by decide)
    exact (step .c .d p (by decide) h3 h4)
  case c.floor =>
    have h3 := h .c (by decide) (by decide)
    have h4 := h .d (by decide) (by decide)
    have h5 := h .floor (by decide) (by decide)
    exact (step .c .d p (by decide) h3 h4).trans ((step .d .floor p (by decide) h4 h5))
  case d.roof =>
    have h0 := h .roof (by decide) (by decide)
    have h1 := h .a (by decide) (by decide)
    have h2 := h .b (by decide) (by decide)
    have h3 := h .c (by decide) (by decide)
    have h4 := h .d (by decide) (by decide)
    exact (step .c .d p (by decide) h3 h4).symm.trans ((step .b .c p (by decide) h2 h3).symm.trans ((step .a .b p (by decide) h1 h2).symm.trans ((step .roof .a p (by decide) h0 h1).symm)))
  case d.a =>
    have h1 := h .a (by decide) (by decide)
    have h2 := h .b (by decide) (by decide)
    have h3 := h .c (by decide) (by decide)
    have h4 := h .d (by decide) (by decide)
    exact (step .c .d p (by decide) h3 h4).symm.trans ((step .b .c p (by decide) h2 h3).symm.trans ((step .a .b p (by decide) h1 h2).symm))
  case d.b =>
    have h2 := h .b (by decide) (by decide)
    have h3 := h .c (by decide) (by decide)
    have h4 := h .d (by decide) (by decide)
    exact (step .c .d p (by decide) h3 h4).symm.trans ((step .b .c p (by decide) h2 h3).symm)
  case d.c =>
    have h3 := h .c (by decide) (by decide)
    have h4 := h .d (by decide) (by decide)
    exact (step .c .d p (by decide) h3 h4).symm
  case d.d =>
    rfl
  case d.floor =>
    have h4 := h .d (by decide) (by decide)
    have h5 := h .floor (by decide) (by decide)
    exact (step .d .floor p (by decide) h4 h5)
  case floor.roof =>
    have h0 := h .roof (by decide) (by decide)
    have h1 := h .a (by decide) (by decide)
    have h2 := h .b (by decide) (by decide)
    have h3 := h .c (by decide) (by decide)
    have h4 := h .d (by decide) (by decide)
    have h5 := h .floor (by decide) (by decide)
    exact (step .d .floor p (by decide) h4 h5).symm.trans ((step .c .d p (by decide) h3 h4).symm.trans ((step .b .c p (by decide) h2 h3).symm.trans ((step .a .b p (by decide) h1 h2).symm.trans ((step .roof .a p (by decide) h0 h1).symm))))
  case floor.a =>
    have h1 := h .a (by decide) (by decide)
    have h2 := h .b (by decide) (by decide)
    have h3 := h .c (by decide) (by decide)
    have h4 := h .d (by decide) (by decide)
    have h5 := h .floor (by decide) (by decide)
    exact (step .d .floor p (by decide) h4 h5).symm.trans ((step .c .d p (by decide) h3 h4).symm.trans ((step .b .c p (by decide) h2 h3).symm.trans ((step .a .b p (by decide) h1 h2).symm)))
  case floor.b =>
    have h2 := h .b (by decide) (by decide)
    have h3 := h .c (by decide) (by decide)
    have h4 := h .d (by decide) (by decide)
    have h5 := h .floor (by decide) (by decide)
    exact (step .d .floor p (by decide) h4 h5).symm.trans ((step .c .d p (by decide) h3 h4).symm.trans ((step .b .c p (by decide) h2 h3).symm))
  case floor.c =>
    have h3 := h .c (by decide) (by decide)
    have h4 := h .d (by decide) (by decide)
    have h5 := h .floor (by decide) (by decide)
    exact (step .d .floor p (by decide) h4 h5).symm.trans ((step .c .d p (by decide) h3 h4).symm)
  case floor.d =>
    have h4 := h .d (by decide) (by decide)
    have h5 := h .floor (by decide) (by decide)
    exact (step .d .floor p (by decide) h4 h5).symm
  case floor.floor =>
    rfl

private theorem ordered (s : Solid) (u v : ℝ → ℝ)
    (hu : arcValid s s.upper u) (hv : arcValid s s.lower v)
    (i j : Chart) (p q : V3) (hp : onChart s i p) (hq : onChart s j q)
    (ord : rank i ≤ rank j) (e : flat s u v i p = flat s u v j q) :
    welded s i j p q := by
  have goodP := hp
  have goodQ := hq
  obtain ⟨⟨px, px', py, py', pbot, ptop⟩, pm⟩ := hp
  obtain ⟨⟨qx, qx', qy, qy', qbot, qtop⟩, qm⟩ := hq
  have aa := s.upper.length_pos
  have bb := s.lower.length_pos
  have cx := mul_nonpos_of_nonpos_of_nonneg s.c_max px
  have cy := mul_nonpos_of_nonpos_of_nonneg s.c_max qy
  have ex := congrArg Prod.fst e
  have ez := congrArg Prod.snd e
  have hpBody : body s p := ⟨px, px', py, py', pbot, ptop⟩
  have hqBody : body s q := ⟨qx, qx', qy, qy', qbot, qtop⟩
  cases i <;> cases j
  case roof.roof =>
    dsimp [flat, perim] at ex ez
    dsimp at pm qm
    have hxx : p.x=q.x := hu.2.1.injOn ⟨px,px'⟩ ⟨qx,qx'⟩ (by linarith only [ez])
    rw [hxx] at pm ex
    have same : p=q := by
      apply point_eq <;> linarith
    subst q
    refine ⟨rfl, ?_⟩
    intro k hk hk'
    cases k with
    | roof => exact goodP
    | a => norm_num [rank] at hk'
    | b => norm_num [rank] at hk'
    | c => norm_num [rank] at hk'
    | d => norm_num [rank] at hk'
    | floor => norm_num [rank] at hk'
  case roof.a =>
    dsimp [flat, perim] at ex ez
    dsimp at pm qm
    have q0 : q.x=0 := qm
    rw [q0] at qtop
    have p0 := arcZero s s.upper u hu px px' (by linarith only [qtop, ez])
    rw [p0,hu.1] at ez
    rw [p0] at ex pm
    have same : p=q := by
      apply point_eq <;> linarith
    subst q
    refine ⟨rfl, ?_⟩
    intro k hk hk'
    cases k with
    | roof => exact goodP
    | a => exact goodQ
    | b => norm_num [rank] at hk'
    | c => norm_num [rank] at hk'
    | d => norm_num [rank] at hk'
    | floor => norm_num [rank] at hk'
  case roof.b =>
    dsimp [flat, perim] at ex ez
    dsimp at pm qm
    have q0 : q.x=0 := by linarith only [ex, py', cx, qx]
    rw [q0] at qtop
    have p0 := arcZero s s.upper u hu px px' (by linarith only [qtop, ez])
    rw [p0,hu.1] at ez
    rw [p0] at ex pm
    have same : p=q := by
      apply point_eq <;> linarith
    subst q
    refine ⟨rfl, ?_⟩
    intro k hk hk'
    cases k with
    | roof => exact goodP
    | a => exact ⟨hpBody, p0⟩
    | b => exact goodQ
    | c => norm_num [rank] at hk'
    | d => norm_num [rank] at hk'
    | floor => norm_num [rank] at hk'
  case roof.c =>
    dsimp [flat, perim] at ex ez
    dsimp at pm qm
    exfalso
    linarith only [ex, aa, bb, cx, cy, px, px', py, py', qx, qx', qy, qy']
  case roof.d =>
    dsimp [flat, perim] at ex ez
    dsimp at pm qm
    exfalso
    linarith only [ex, aa, bb, cx, cy, px, px', py, py', qx, qx', qy, qy']
  case roof.floor =>
    dsimp [flat, perim] at ex ez
    dsimp at pm qm
    exfalso
    linarith only [ex, aa, bb, cx, cy, px, px', py, py', qx, qx', qy, qy']
  case a.roof =>
    norm_num [rank] at ord
  case a.a =>
    dsimp [flat, perim] at ex ez
    dsimp at pm qm
    have same : p=q := by
      apply point_eq <;> linarith
    subst q
    refine ⟨rfl, ?_⟩
    intro k hk hk'
    cases k with
    | roof => norm_num [rank] at hk
    | a => exact goodP
    | b => norm_num [rank] at hk'
    | c => norm_num [rank] at hk'
    | d => norm_num [rank] at hk'
    | floor => norm_num [rank] at hk'
  case a.b =>
    dsimp [flat, perim] at ex ez
    dsimp at pm qm
    have same : p=q := by
      apply point_eq <;> linarith
    subst q
    refine ⟨rfl, ?_⟩
    intro k hk hk'
    cases k with
    | roof => norm_num [rank] at hk
    | a => exact goodP
    | b => exact goodQ
    | c => norm_num [rank] at hk'
    | d => norm_num [rank] at hk'
    | floor => norm_num [rank] at hk'
  case a.c =>
    dsimp [flat, perim] at ex ez
    dsimp at pm qm
    exfalso
    linarith only [ex, aa, bb, cx, cy, px, px', py, py', qx, qx', qy, qy']
  case a.d =>
    dsimp [flat, perim] at ex ez
    dsimp at pm qm
    exfalso
    linarith only [ex, aa, bb, cx, cy, px, px', py, py', qx, qx', qy, qy']
  case a.floor =>
    dsimp [flat, perim] at ex ez
    dsimp at pm qm
    exfalso
    linarith only [ex, aa, bb, cx, cy, px, px', py, py', qx, qx', qy, qy']
  case b.roof =>
    norm_num [rank] at ord
  case b.a =>
    norm_num [rank] at ord
  case b.b =>
    dsimp [flat, perim] at ex ez
    dsimp at pm qm
    have same : p=q := by
      apply point_eq <;> linarith
    subst q
    refine ⟨rfl, ?_⟩
    intro k hk hk'
    cases k with
    | roof => norm_num [rank] at hk
    | a => norm_num [rank] at hk
    | b => exact goodP
    | c => norm_num [rank] at hk'
    | d => norm_num [rank] at hk'
    | floor => norm_num [rank] at hk'
  case b.c =>
    dsimp [flat, perim] at ex ez
    dsimp at pm qm
    have same : p=q := by
      apply point_eq <;> linarith
    subst q
    refine ⟨rfl, ?_⟩
    intro k hk hk'
    cases k with
    | roof => norm_num [rank] at hk
    | a => norm_num [rank] at hk
    | b => exact goodP
    | c => exact goodQ
    | d => norm_num [rank] at hk'
    | floor => norm_num [rank] at hk'
  case b.d =>
    dsimp [flat, perim] at ex ez
    dsimp at pm qm
    exfalso
    linarith only [ex, aa, bb, cx, cy, px, px', py, py', qx, qx', qy, qy']
  case b.floor =>
    dsimp [flat, perim] at ex ez
    dsimp at pm qm
    exfalso
    linarith only [ex, aa, bb, cx, cy, px, px', py, py', qx, qx', qy, qy']
  case c.roof =>
    norm_num [rank] at ord
  case c.a =>
    norm_num [rank] at ord
  case c.b =>
    norm_num [rank] at ord
  case c.c =>
    dsimp [flat, perim] at ex ez
    dsimp at pm qm
    have same : p=q := by
      apply point_eq <;> linarith
    subst q
    refine ⟨rfl, ?_⟩
    intro k hk hk'
    cases k with
    | roof => norm_num [rank] at hk
    | a => norm_num [rank] at hk
    | b => norm_num [rank] at hk
    | c => exact goodP
    | d => norm_num [rank] at hk'
    | floor => norm_num [rank] at hk'
  case c.d =>
    dsimp [flat, perim] at ex ez
    dsimp at pm qm
    have same : p=q := by
      apply point_eq <;> linarith
    subst q
    refine ⟨rfl, ?_⟩
    intro k hk hk'
    cases k with
    | roof => norm_num [rank] at hk
    | a => norm_num [rank] at hk
    | b => norm_num [rank] at hk
    | c => exact goodP
    | d => exact goodQ
    | floor => norm_num [rank] at hk'
  case c.floor =>
    dsimp [flat, perim] at ex ez
    dsimp at pm qm
    have p0 : p.y=0 := by linarith only [ex, qx', cy, py]
    rw [p0] at pbot
    have q0 := arcZero s s.lower v hv qy qy' (by linarith only [pbot, ez])
    rw [q0,hv.1] at ez
    rw [q0] at ex qm
    have same : p=q := by
      apply point_eq <;> linarith
    subst q
    refine ⟨rfl, ?_⟩
    intro k hk hk'
    cases k with
    | roof => norm_num [rank] at hk
    | a => norm_num [rank] at hk
    | b => norm_num [rank] at hk
    | c => exact goodP
    | d => exact ⟨hpBody, p0⟩
    | floor => exact goodQ
  case d.roof =>
    norm_num [rank] at ord
  case d.a =>
    norm_num [rank] at ord
  case d.b =>
    norm_num [rank] at ord
  case d.c =>
    norm_num [rank] at ord
  case d.d =>
    dsimp [flat, perim] at ex ez
    dsimp at pm qm
    have same : p=q := by
      apply point_eq <;> linarith
    subst q
    refine ⟨rfl, ?_⟩
    intro k hk hk'
    cases k with
    | roof => norm_num [rank] at hk
    | a => norm_num [rank] at hk
    | b => norm_num [rank] at hk
    | c => norm_num [rank] at hk
    | d => exact goodP
    | floor => norm_num [rank] at hk'
  case d.floor =>
    dsimp [flat, perim] at ex ez
    dsimp at pm qm
    have p0 : p.y=0 := pm
    rw [p0] at pbot
    have q0 := arcZero s s.lower v hv qy qy' (by linarith only [pbot, ez])
    rw [q0,hv.1] at ez
    rw [q0] at ex qm
    have same : p=q := by
      apply point_eq <;> linarith
    subst q
    refine ⟨rfl, ?_⟩
    intro k hk hk'
    cases k with
    | roof => norm_num [rank] at hk
    | a => norm_num [rank] at hk
    | b => norm_num [rank] at hk
    | c => norm_num [rank] at hk
    | d => exact goodP
    | floor => exact goodQ
  case floor.roof =>
    norm_num [rank] at ord
  case floor.a =>
    norm_num [rank] at ord
  case floor.b =>
    norm_num [rank] at ord
  case floor.c =>
    norm_num [rank] at ord
  case floor.d =>
    norm_num [rank] at ord
  case floor.floor =>
    dsimp [flat, perim] at ex ez
    dsimp at pm qm
    have hyy : p.y=q.y := hv.2.1.injOn ⟨py,py'⟩ ⟨qy,qy'⟩ (by linarith only [ez])
    rw [hyy] at pm ex
    have same : p=q := by
      apply point_eq <;> linarith
    subst q
    refine ⟨rfl, ?_⟩
    intro k hk hk'
    cases k with
    | roof => norm_num [rank] at hk
    | a => norm_num [rank] at hk
    | b => norm_num [rank] at hk
    | c => norm_num [rank] at hk
    | d => norm_num [rank] at hk
    | floor => exact goodP

theorem contacts (s : Solid) (u v : ℝ → ℝ)
    (hu : arcValid s s.upper u) (hv : arcValid s s.lower v)
    (i j : Chart) (p q : V3) (hp : onChart s i p) (hq : onChart s j q) :
    flat s u v i p = flat s u v j q ↔ welded s i j p q := by
  refine ⟨fun e => ?_, agree s u v hu hv i j p q⟩
  rcases le_total (rank i) (rank j) with h | h
  · exact ordered s u v hu hv i j p q hp hq h e
  · obtain ⟨hs, hh⟩ := ordered s u v hu hv j i q p hq hp h e.symm
    subst q
    exact ⟨rfl, by simpa only [min_comm (rank i), max_comm (rank i)] using hh⟩

end DurerDV
