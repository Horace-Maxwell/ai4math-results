import Research.TaskT.HellyFive.FiniteKernels

namespace TaskT.HellyFive.FiberProjection

open Set FiniteGeometry

def positiveCorner {r : ℕ} (z : Grid r) : Prop :=
  z ≠ 0 ∧ ∀ i, z i = 0 ∨ z i = 1

def signedCorner {r : ℕ} (z : Grid r) : Prop :=
  z = 0 ∨ positiveCorner z ∨ positiveCorner (-z)

def body (r : ℕ) : Set (Space r) :=
  convexHull ℝ (embed '' {z : Grid r | signedCorner z})

private theorem signed_bounds {r : ℕ} {z : Grid r} (hz : signedCorner z) :
    (∀ i, -1 ≤ z i ∧ z i ≤ 1) ∧ (∀ i j, z i - z j ≤ 1) := by
  rcases hz with rfl | ⟨_,h⟩ | ⟨_,h⟩
  · simp
  · constructor
    · intro i; rcases h i with hi | hi <;> omega
    · intro i j; rcases h i with hi | hi <;> rcases h j with hj | hj <;> omega
  · simp only [Pi.neg_apply] at h
    constructor
    · intro i; rcases h i with hi | hi <;> omega
    · intro i j; rcases h i with hi | hi <;> rcases h j with hj | hj <;> omega

theorem body_bounds {r : ℕ} {x : Space r} (hx : x ∈ body r) :
    (∀ i, -1 ≤ x i ∧ x i ≤ 1) ∧ (∀ i j, x i - x j ≤ 1) := by
  constructor
  · intro i
    let f : Space r →ₗ[ℝ] ℝ := LinearMap.proj i
    have hc : Convex ℝ ({y | (-1 : ℝ) ≤ f y} ∩ {y | f y ≤ (1 : ℝ)}) :=
      (convex_halfSpace_ge f.isLinear _).inter (convex_halfSpace_le f.isLinear _)
    apply convexHull_min _ hc hx
    rintro _ ⟨z,hz,rfl⟩
    change (-1 : ℝ) ≤ (z i : ℝ) ∧ (z i : ℝ) ≤ 1
    exact_mod_cast (signed_bounds hz).1 i
  · intro i j
    let f : Space r →ₗ[ℝ] ℝ := (LinearMap.proj i : Space r →ₗ[ℝ] ℝ) - (LinearMap.proj j : Space r →ₗ[ℝ] ℝ)
    change f x ≤ (1 : ℝ)
    apply convexHull_min (t := {y | f y ≤ (1 : ℝ)}) _ (convex_halfSpace_le f.isLinear _) hx
    rintro _ ⟨z,hz,rfl⟩
    change (z i : ℝ) - (z j : ℝ) ≤ 1
    exact_mod_cast (signed_bounds hz).2 i j

theorem body_grid_iff {r : ℕ} (z : Grid r) : embed z ∈ body r ↔ signedCorner z := by
  constructor
  · intro hz
    obtain ⟨hb,hd⟩ := body_bounds hz
    have bounds (i : Fin r) : -1 ≤ z i ∧ z i ≤ 1 := by
      exact_mod_cast (show -1 ≤ (z i : ℝ) ∧ (z i : ℝ) ≤ 1 from hb i)
    have dif (i j : Fin r) : z i - z j ≤ 1 := by
      exact_mod_cast (show (z i : ℝ) - (z j : ℝ) ≤ 1 from hd i j)
    by_cases h0 : z = 0
    · exact Or.inl h0
    by_cases hp : ∃ i, z i = 1
    · obtain ⟨i,hi⟩ := hp
      exact Or.inr (Or.inl ⟨h0, fun j => by have := dif i j; have := bounds j; omega⟩)
    · refine Or.inr (Or.inr ⟨by simpa, fun j => ?_⟩)
      change -z j = 0 ∨ -z j = 1
      have hne : z j ≠ 1 := fun hj => hp ⟨j,hj⟩
      have := bounds j
      omega
  · intro hz
    exact subset_convexHull ℝ _ ⟨z,hz,rfl⟩

/-- Generating layers, including the real points of each of the three base polytopes. -/
def layers {r : ℕ} (p q s : Set (Space 4)) : Set (Space 4 × Space r) :=
  {v | (v.1 ∈ p ∧ v.2 = 0) ∨
       (v.1 ∈ q ∧ ∃ z : Grid r, positiveCorner z ∧ v.2 = embed z) ∨
       (v.1 ∈ s ∧ ∃ z : Grid r, positiveCorner (-z) ∧ v.2 = embed z)}

def lifted (r : ℕ) : Set (Space 4 × Space r) :=
  convexHull ℝ (layers (r := r) (poly WitnessFour.vertices)
    (poly CorePositive.vertices) (poly CoreNegative.vertices))

theorem lifted_snd {r : ℕ} {v : Space 4 × Space r} (hv : v ∈ lifted r) : v.2 ∈ body r := by
  let f : Space 4 × Space r →ₗ[ℝ] Space r := LinearMap.snd ℝ _ _
  apply convexHull_min (t := f ⁻¹' body r) _ ((convex_convexHull ℝ _).linear_preimage f) hv
  intro x hx
  change x.2 ∈ body r
  rcases hx with ⟨_,h⟩ | ⟨_,z,h,hz⟩ | ⟨_,z,h,hz⟩
  · rw [h]
    exact subset_convexHull ℝ _ ⟨0,Or.inl rfl,by ext i; simp [embed]⟩
  · rw [hz]; exact (body_grid_iff z).2 (Or.inr (Or.inl h))
  · rw [hz]; exact (body_grid_iff z).2 (Or.inr (Or.inr h))

theorem lifted_grid_snd {r : ℕ} {v : Space 4} {z : Grid r}
    (h : (v,embed z) ∈ lifted r) : signedCorner z :=
  (body_grid_iff z).1 (lifted_snd h)


private theorem poly_nonempty_of_card {v : Finset (Grid 4)} (hv : 0 < v.card) :
    (poly v).Nonempty := by
  obtain ⟨x,hx⟩ := Finset.card_pos.mp hv
  exact ⟨_,subset_convexHull ℝ _ ⟨x,hx,rfl⟩⟩

theorem lifted_grid_projection_exact {r : ℕ} (z : Grid r) :
    (∃ x : Space 4, (x,embed z) ∈ lifted r) ↔ signedCorner z := by
  constructor
  · rintro ⟨x,hx⟩
    exact lifted_grid_snd hx
  · rintro (rfl | hz | hz)
    · obtain ⟨x,hx⟩ := poly_nonempty_of_card (v := WitnessFour.vertices)
          (by rw [WitnessFour.counts.1]; decide)
      exact ⟨x,subset_convexHull ℝ _ (Or.inl ⟨hx,by ext i; simp [embed]⟩ : (x,embed (0 : Grid r)) ∈ layers _ _ _)⟩
    · obtain ⟨x,hx⟩ := poly_nonempty_of_card (v := CorePositive.vertices)
          (by rw [CorePositive.counts.1]; decide)
      exact ⟨x,subset_convexHull ℝ _ (Or.inr (Or.inl ⟨hx,z,hz,rfl⟩) : (x,embed z) ∈ layers _ _ _)⟩
    · obtain ⟨x,hx⟩ := poly_nonempty_of_card (v := CoreNegative.vertices)
          (by rw [CoreNegative.counts.1]; decide)
      exact ⟨x,subset_convexHull ℝ _ (Or.inr (Or.inr ⟨hx,z,hz,rfl⟩) : (x,embed z) ∈ layers _ _ _)⟩

private theorem mix_eq_top {a b X Y t : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hs : a+b=1) (hx : X ≤ t) (hy : Y ≤ t) (he : a*X+b*Y=t) : X=t := by
  by_contra hn
  have h := mul_lt_mul_of_pos_left (lt_of_le_of_ne hx hn) ha
  have h' := mul_le_mul_of_nonneg_left hy hb.le
  nlinarith [congrArg (fun z : ℝ => z*t) hs]

theorem positive_extreme {r : ℕ} {z : Grid r} (hz : positiveCorner z) :
    embed z ∈ (body r).extremePoints ℝ := by
  refine ⟨(body_grid_iff z).2 (Or.inr (Or.inl hz)), ?_⟩
  intro x hx y hy hs
  obtain ⟨a,b,ha,hb,hs,hxy⟩ := hs
  have ev (i : Fin r) : a*x i+b*y i=z i := congrFun hxy i
  have h1 : ∃ i, z i=1 := by
    by_contra! h
    exact hz.1 (funext fun i => (hz.2 i).resolve_right (h i))
  obtain ⟨i,hi⟩ := h1
  have top (j : Fin r) (hj : z j = 1) : x j = 1 :=
    mix_eq_top ha hb hs ((body_bounds hx).1 j).2 ((body_bounds hy).1 j).2 (by simpa [hj] using ev j)
  funext j
  change x j = (z j : ℝ)
  rcases hz.2 j with hj | hj
  · have he : a*(x i-x j)+b*(y i-y j)=1 := by
      have hi' := ev i
      have hj' := ev j
      rw [hi,Int.cast_one] at hi'
      rw [hj,Int.cast_zero] at hj'
      linarith
    have hh := mix_eq_top ha hb hs ((body_bounds hx).2 i j) ((body_bounds hy).2 i j) he
    rw [hj,Int.cast_zero]
    linarith [top i hi]
  · simpa [hj] using top j hj

private theorem embed_neg {r : ℕ} (z : Grid r) : embed (-z) = -(embed z) := by
  ext i; simp [embed]

private theorem neg_body {r : ℕ} {x : Space r} (hx : x ∈ body r) : -x ∈ body r := by
  let f : Space r →ₗ[ℝ] Space r := -LinearMap.id
  apply convexHull_min (t := f ⁻¹' body r) _ ((convex_convexHull ℝ _).linear_preimage f) hx
  rintro _ ⟨z,hz,rfl⟩
  change -(embed z) ∈ body r
  rw [← embed_neg,body_grid_iff]
  rcases hz with rfl | hp | hm
  · exact Or.inl (neg_zero)
  · exact Or.inr (Or.inr (by simpa using hp))
  · exact Or.inr (Or.inl hm)

theorem negative_extreme {r : ℕ} {z : Grid r} (hz : positiveCorner (-z)) :
    embed z ∈ (body r).extremePoints ℝ := by
  refine ⟨(body_grid_iff z).2 (Or.inr (Or.inr hz)), ?_⟩
  intro x hx y hy hs
  obtain ⟨a,b,ha,hb,hs,hxy⟩ := hs
  have eq : -x = embed (-z) := (positive_extreme hz).2 (neg_body hx) (neg_body hy)
    ⟨a,b,ha,hb,hs,by rw [smul_neg,smul_neg,← neg_add, hxy,embed_neg]⟩
  rw [embed_neg] at eq
  exact neg_injective eq

private theorem different_sign {r : ℕ} {z : Grid r} (h : positiveCorner z) :
    ¬positiveCorner (-z) := by
  intro h'
  apply h.1
  funext i
  have hi := h.2 i
  have hj := h'.2 i
  change -z i=0 ∨ -z i=1 at hj
  change z i = 0
  omega

/-- Over an extreme projection point, taking the convex hull cannot grow an already convex fiber. -/
private theorem hull_fiber {r : ℕ} {w : Space r} {K : Set (Space 4)}
    {S : Set (Space 4 × Space r)}
    (hew : w ∈ (body r).extremePoints ℝ) (hK : Convex ℝ K)
    (hproj : ∀ v ∈ S, v.2 ∈ body r) (hgen : ∀ v ∈ S, v.2 = w → v.1 ∈ K)
    {x : Space 4} (hx : (x,w) ∈ convexHull ℝ S) : x ∈ K := by
  let T : Set (Space 4 × Space r) := {v | v.2 ∈ body r ∧ (v.2 = w → v.1 ∈ K)}
  have hc : Convex ℝ T := by
    intro u hu v hv a b ha hb hs
    change u.2 ∈ body r ∧ (u.2 = w → u.1 ∈ K) at hu
    change v.2 ∈ body r ∧ (v.2 = w → v.1 ∈ K) at hv
    change (a • u.2 + b • v.2) ∈ body r ∧ (a • u.2 + b • v.2 = w → a • u.1+b • v.1 ∈ K)
    refine ⟨(convex_convexHull ℝ _) hu.1 hv.1 ha hb hs, ?_⟩
    rcases ha.eq_or_lt with ha | ha
    · have ea : a = 0 := ha.symm; subst a
      simp_all
    rcases hb.eq_or_lt with hb | hb
    · have eb : b = 0 := hb.symm; subst b
      simp_all
    intro he
    have eqs := (mem_extremePoints.mp hew).2 u.2 hu.1 v.2 hv.1 ⟨a,b,ha,hb,hs,he⟩
    exact hK (hu.2 eqs.1) (hv.2 eqs.2) ha.le hb.le hs
  have hsub : S ⊆ T := fun v hv => ⟨hproj v hv,hgen v hv⟩
  exact (convexHull_min hsub hc hx).2 rfl

private theorem layers_proj {r : ℕ} {v : Space 4 × Space r}
    (hv : v ∈ layers (poly WitnessFour.vertices) (poly CorePositive.vertices) (poly CoreNegative.vertices)) :
    v.2 ∈ body r :=
  lifted_snd (subset_convexHull ℝ _ hv)

theorem positive_fiber {r : ℕ} {z : Grid r} (hz : positiveCorner z) (x : Space 4) :
    (x,embed z) ∈ lifted r ↔ x ∈ poly CorePositive.vertices := by
  constructor
  · apply hull_fiber (positive_extreme hz) (convex_convexHull ℝ _) (fun _ => layers_proj)
    intro v hve he
    rcases hve with ⟨_,h0⟩ | ⟨hk,_⟩ | ⟨_,j,hj,hv⟩
    · exfalso
      apply hz.1
      apply embed_inj
      rw [← he,h0]
      ext i; simp [embed]
    · exact hk
    · have ej := embed_inj (hv.symm.trans he)
      exact (different_sign hz (ej ▸ hj)).elim
  · intro hx
    exact subset_convexHull ℝ _ (Or.inr (Or.inl ⟨hx,z,hz,rfl⟩) : (x,embed z) ∈ layers _ _ _)

theorem negative_fiber {r : ℕ} {z : Grid r} (hz : positiveCorner (-z)) (x : Space 4) :
    (x,embed z) ∈ lifted r ↔ x ∈ poly CoreNegative.vertices := by
  constructor
  · apply hull_fiber (negative_extreme hz) (convex_convexHull ℝ _) (fun _ => layers_proj)
    intro v hve he
    rcases hve with ⟨_,h0⟩ | ⟨_,j,hj,hv⟩ | ⟨hk,_⟩
    · exfalso
      apply hz.1
      have hh : z = 0 := by
        apply embed_inj
        rw [← he,h0]
        ext i; simp [embed]
      rw [hh,neg_zero]
    · have ej := embed_inj (hv.symm.trans he)
      exact (different_sign (ej ▸ hj) hz).elim
    · exact hk
  · intro hx
    exact subset_convexHull ℝ _ (Or.inr (Or.inr ⟨hx,z,hz,rfl⟩) : (x,embed z) ∈ layers _ _ _)

theorem lifted_fst {r : ℕ} {v : Space 4 × Space r} (hv : v ∈ lifted r) :
    v.1 ∈ poly WitnessFour.vertices := by
  let f : Space 4 × Space r →ₗ[ℝ] Space 4 := LinearMap.fst ℝ _ _
  apply convexHull_min (t := f ⁻¹' poly WitnessFour.vertices) _
    ((convex_convexHull ℝ _).linear_preimage f) hv
  rintro u (⟨hu,_⟩ | ⟨hu,_⟩ | ⟨hu,_⟩)
  · exact hu
  · exact positive_subset hu
  · exact negative_subset hu

theorem zero_fiber (r : ℕ) (x : Space 4) :
    (x,0) ∈ lifted r ↔ x ∈ poly WitnessFour.vertices :=
  ⟨fun hx => lifted_fst hx, fun hx =>
    subset_convexHull ℝ _ (Or.inl ⟨hx,rfl⟩ : (x,(0 : Space r)) ∈ layers _ _ _)⟩

private theorem extreme_lift {r : ℕ} {u : Space r} {x : Space 4} {K : Set (Space 4)}
    (hu : u ∈ (body r).extremePoints ℝ)
    (hK : ∀ y : Space 4, (y,u) ∈ lifted r ↔ y ∈ K)
    (hx : x ∈ K.extremePoints ℝ) : (x,u) ∈ (lifted r).extremePoints ℝ := by
  refine ⟨(hK x).2 hx.1, ?_⟩
  rintro ⟨p,s⟩ hp ⟨q,t⟩ hq ⟨a,b,ha,hb,hs,he⟩
  have ef : a • p + b • q = x := congrArg Prod.fst he
  have es : a • s + b • t = u := congrArg Prod.snd he
  have eqs := (mem_extremePoints.mp hu).2 s (lifted_snd hp) t (lifted_snd hq) ⟨a,b,ha,hb,hs,es⟩
  obtain ⟨rfl,rfl⟩ := eqs
  exact Prod.ext (hx.2 ((hK p).1 hp) ((hK q).1 hq) ⟨a,b,ha,hb,hs,ef⟩) rfl

theorem positive_lattice_extreme {r : ℕ} {z : Grid r} (hz : positiveCorner z)
    {x : Grid 4} (hx : (embed x,embed z) ∈ lifted r) :
    (embed x,embed z) ∈ (lifted r).extremePoints ℝ := by
  apply extreme_lift (positive_extreme hz) (positive_fiber hz)
  rw [CorePositive.geometry.1]
  exact ⟨x,positive_grid.mp ((positive_fiber hz _).1 hx),rfl⟩

theorem negative_lattice_extreme {r : ℕ} {z : Grid r} (hz : positiveCorner (-z))
    {x : Grid 4} (hx : (embed x,embed z) ∈ lifted r) :
    (embed x,embed z) ∈ (lifted r).extremePoints ℝ := by
  apply extreme_lift (negative_extreme hz) (negative_fiber hz)
  rw [CoreNegative.geometry.1]
  exact ⟨x,negative_grid.mp ((negative_fiber hz _).1 hx),rfl⟩

private theorem central_slice_bound {r : ℕ} {p : Space 4}
    (he : p ∈ (poly WitnessFour.vertices).extremePoints ℝ) (i : Fin r)
    (c : ℝ)
    (hp : p ∈ poly CorePositive.vertices → 0 ≤ c)
    (hn : p ∈ poly CoreNegative.vertices → c ≤ 0)
    {y : Space r} (hy : (p,y) ∈ lifted r) : 0 ≤ c*y i := by
  let T : Set (Space 4 × Space r) := {v | v.1 ∈ poly WitnessFour.vertices ∧
    (v.1 = p → 0 ≤ c*v.2 i)}
  have hc : Convex ℝ T := by
    intro u hu v hv a b ha hb hs
    change u.1 ∈ poly WitnessFour.vertices ∧ (u.1=p → 0 ≤ c*u.2 i) at hu
    change v.1 ∈ poly WitnessFour.vertices ∧ (v.1=p → 0 ≤ c*v.2 i) at hv
    change (a • u.1+b • v.1) ∈ poly WitnessFour.vertices ∧
      (a • u.1+b • v.1=p → 0 ≤ c*(a*u.2 i+b*v.2 i))
    refine ⟨(convex_convexHull ℝ _) hu.1 hv.1 ha hb hs, ?_⟩
    rcases ha.eq_or_lt with ha | ha
    · have ea : a=0 := ha.symm; subst a; simp_all
    rcases hb.eq_or_lt with hb | hb
    · have eb : b=0 := hb.symm; subst b; simp_all
    intro eq
    have eqs := (mem_extremePoints.mp he).2 u.1 hu.1 v.1 hv.1 ⟨a,b,ha,hb,hs,eq⟩
    nlinarith [mul_nonneg ha.le (hu.2 eqs.1), mul_nonneg hb.le (hv.2 eqs.2)]
  have hsub : layers (r := r) (poly WitnessFour.vertices) (poly CorePositive.vertices)
      (poly CoreNegative.vertices) ⊆ T := by
    rintro ⟨u,t⟩ (⟨hu,ht⟩ | ⟨hu,z,hz,ht⟩ | ⟨hu,z,hz,ht⟩)
    · change t = 0 at ht; subst t; exact ⟨hu, fun _ => by simp⟩
    · refine ⟨positive_subset hu, ?_⟩
      change u = p → 0 ≤ c*t i
      intro ep
      subst u
      change t = embed z at ht
      rw [ht]
      exact mul_nonneg (hp hu) (by change 0 ≤ (z i : ℝ); rcases hz.2 i with h | h <;> simp [h])
    · refine ⟨negative_subset hu, ?_⟩
      change u = p → 0 ≤ c*t i
      intro ep
      subst u
      change t = embed z at ht
      rw [ht]
      apply mul_nonneg_of_nonpos_of_nonpos (hn hu)
      have hsign := hz.2 i
      change -z i = 0 ∨ -z i = 1 at hsign
      change (z i : ℝ) ≤ 0
      exact_mod_cast (show z i ≤ 0 by omega)
  exact (convexHull_min hsub hc hy).2 rfl

theorem central_extreme {r : ℕ} {p : Space 4}
    (hp : p ∈ (poly WitnessFour.vertices).extremePoints ℝ) :
    (p,(0 : Space r)) ∈ (lifted r).extremePoints ℝ := by
  refine ⟨(zero_fiber r p).2 hp.1, ?_⟩
  rintro ⟨u,s⟩ hu ⟨v,t⟩ hv ⟨a,b,ha,hb,hs,he⟩
  have ef : a • u + b • v = p := congrArg Prod.fst he
  have es : a • s + b • t = 0 := congrArg Prod.snd he
  have eqs := (mem_extremePoints.mp hp).2 u (lifted_fst hu) v (lifted_fst hv) ⟨a,b,ha,hb,hs,ef⟩
  rw [eqs.1] at hu ⊢
  rw [eqs.2] at hv
  refine Prod.ext rfl ?_
  change s = 0
  funext i
  change s i = 0
  have ee : a*s i+b*t i=0 := congrFun es i
  by_cases hneg : p ∈ poly CoreNegative.vertices
  · have hpos : p ∉ poly CorePositive.vertices :=
      fun h => disjoint_at_old_extreme hp ⟨h,hneg⟩
    have B {y : Space r} (h : (p,y) ∈ lifted r) : y i ≤ 0 := by
      have h' := central_slice_bound hp i (-1) (fun h => (hpos h).elim) (by norm_num) h
      linarith
    have h' := mul_nonpos_of_nonneg_of_nonpos hb.le (B hv)
    nlinarith [mul_nonneg ha.le (neg_nonneg.mpr (B hu))]
  · have B {y : Space r} (h : (p,y) ∈ lifted r) : 0 ≤ y i := by
      have h' := central_slice_bound hp i 1 (by norm_num) (fun h => (hneg h).elim) h
      linarith
    have h' := mul_nonneg hb.le (B hv)
    nlinarith [B hu]

theorem central_extreme_iff (r : ℕ) (p : Space 4) :
    (p,(0 : Space r)) ∈ (lifted r).extremePoints ℝ ↔
    p ∈ (poly WitnessFour.vertices).extremePoints ℝ := by
  refine ⟨?_,central_extreme⟩
  intro hp
  refine ⟨(zero_fiber r p).1 hp.1, ?_⟩
  intro u hu v hv
  rintro ⟨a,b,ha,hb,hs,he⟩
  have ec : a • (u,(0 : Space r)) + b • (v,0) = (p,0) := Prod.ext he (by simp)
  exact congrArg Prod.fst (hp.2 ((zero_fiber r _).2 hu) ((zero_fiber r _).2 hv) ⟨a,b,ha,hb,hs,ec⟩)

theorem nonvertex_grid_iff {r : ℕ} (x : Grid 4) (z : Grid r) :
    ((embed x,embed z) ∈ lifted r ∧ (embed x,embed z) ∉ (lifted r).extremePoints ℝ) ↔
      z = 0 ∧ x ∈ WitnessFour.centers := by
  have e0 : embed (0 : Grid r) = 0 := by ext i; simp [embed]
  constructor
  · rintro ⟨h,hn⟩
    rcases lifted_grid_snd h with rfl | hz | hz
    · rw [e0] at h hn
      refine ⟨rfl, ?_⟩
      rw [← Finset.mem_coe,← WitnessFour.geometry.2]
      exact ⟨(zero_fiber r _).1 h, fun he => hn (central_extreme he)⟩
    · exact (hn (positive_lattice_extreme hz h)).elim
    · exact (hn (negative_lattice_extreme hz h)).elim
  · rintro ⟨rfl,hx⟩
    rw [← Finset.mem_coe,← WitnessFour.geometry.2] at hx
    rw [e0,zero_fiber,central_extreme_iff]
    exact hx

end TaskT.HellyFive.FiberProjection
