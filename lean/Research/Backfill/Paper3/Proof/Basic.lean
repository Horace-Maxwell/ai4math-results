import Research.Backfill.Paper3.Challenge

/-!
# Paper 3 back-fill: basic facts

`i_γ` as `N_{≤⌊γdn⌋}`, invariance under isomorphism, and the ordered-pair form
`2 e_G(A) = #{(u, v) : u, v ∈ A, u ~ v}` of the edge count, with its consequences for disjoint
sums (`⊕g`), copies (`⊥ □ G`) and `K_{d,d}`.
-/

set_option autoImplicit false

namespace P3Basic

open Finset SimpleGraph BackfillPaper3.Challenge

section General

variable {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]

/-- For `γ ≥ 0`, the real threshold `γ d n` can be replaced by its floor. -/
theorem iGamma_eq_iCount_floor (G : SimpleGraph V) [DecidableRel G.Adj] (d : ℕ) {γ : ℝ}
    (hγ : 0 ≤ γ) : iGamma G d γ = iCount G ⌊γ * d * (Fintype.card V : ℝ)⌋₊ := by
  unfold iGamma iCount
  congr 1
  apply Finset.filter_congr
  intro A _
  have h0 : (0 : ℝ) ≤ γ * d * (Fintype.card V : ℝ) := by positivity
  exact (Nat.le_floor_iff h0).symm

/-- If `γ d n` is a natural number `t`, then `i_γ(G) = N_{≤t}(G)`. -/
theorem iGamma_eq_iCount (G : SimpleGraph V) [DecidableRel G.Adj] (d : ℕ) {γ : ℝ} (t : ℕ)
    (h : γ * d * (Fintype.card V : ℝ) = t) : iGamma G d γ = iCount G t := by
  unfold iGamma iCount
  congr 1
  apply Finset.filter_congr
  intro A _
  rw [h]
  exact Nat.cast_le

/-- `e_G(A)` is invariant under graph isomorphism. -/
theorem edgesIn_map_iso {G : SimpleGraph V} {H : SimpleGraph W} [DecidableRel G.Adj]
    [DecidableRel H.Adj] (e : G ≃g H) (A : Finset V) :
    edgesIn H (A.map e.toEquiv.toEmbedding) = edgesIn G A := by
  unfold edgesIn
  rw [← Finset.card_map e.toEquiv.toEmbedding.sym2Map]
  congr 1
  ext z
  induction z using Sym2.ind with
  | h x y =>
    obtain ⟨x', rfl⟩ := e.surjective x
    obtain ⟨y', rfl⟩ := e.surjective y
    rw [Finset.mem_map]
    constructor
    · intro hz
      rw [Finset.mem_filter, SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet,
        Finset.mk_mem_sym2_iff] at hz
      refine ⟨s(x', y'), ?_, rfl⟩
      rw [Finset.mem_filter, SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet,
        Finset.mk_mem_sym2_iff]
      exact ⟨e.map_adj_iff.mp hz.1, (Finset.mem_map' e.toEquiv.toEmbedding).1 hz.2.1,
        (Finset.mem_map' e.toEquiv.toEmbedding).1 hz.2.2⟩
    · rintro ⟨w, hw, hwz⟩
      induction w using Sym2.ind with
      | h p q =>
        rw [Finset.mem_filter, SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet,
          Finset.mk_mem_sym2_iff] at hw
        have hwz' : s(e p, e q) = s(e x', e y') := hwz
        rw [Finset.mem_filter, SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet,
          Finset.mk_mem_sym2_iff]
        rcases Sym2.eq_iff.mp hwz' with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · rw [← h1, ← h2]
          exact ⟨e.map_adj_iff.mpr hw.1, (Finset.mem_map' e.toEquiv.toEmbedding).2 hw.2.1,
            (Finset.mem_map' e.toEquiv.toEmbedding).2 hw.2.2⟩
        · rw [← h1, ← h2]
          exact ⟨(e.map_adj_iff.mpr hw.1).symm, (Finset.mem_map' e.toEquiv.toEmbedding).2 hw.2.2,
            (Finset.mem_map' e.toEquiv.toEmbedding).2 hw.2.1⟩

/-- `N_{≤t}` is invariant under graph isomorphism. -/
theorem iCount_iso {G : SimpleGraph V} {H : SimpleGraph W} [DecidableRel G.Adj]
    [DecidableRel H.Adj] (e : G ≃g H) (t : ℕ) : iCount G t = iCount H t := by
  unfold iCount
  apply Finset.card_bij (fun A _ => A.map e.toEquiv.toEmbedding)
  · intro A hA
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hA ⊢
    rw [edgesIn_map_iso]
    exact hA
  · intro A _ B _ h
    exact Finset.map_injective _ h
  · intro B hB
    refine ⟨B.map e.symm.toEquiv.toEmbedding, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hB ⊢
      rw [edgesIn_map_iso e.symm]
      exact hB
    · rw [Finset.map_map]
      conv_rhs => rw [← Finset.map_refl (s := B)]
      congr 1
      ext x
      exact e.apply_symm_apply x

/-- `i_γ` is invariant under graph isomorphism (`γ ≥ 0`). -/
theorem iGamma_iso {G : SimpleGraph V} {H : SimpleGraph W} [DecidableRel G.Adj]
    [DecidableRel H.Adj] (e : G ≃g H) (d : ℕ) {γ : ℝ} (hγ : 0 ≤ γ) :
    iGamma G d γ = iGamma H d γ := by
  rw [iGamma_eq_iCount_floor G d hγ, iGamma_eq_iCount_floor H d hγ,
    Fintype.card_congr e.toEquiv]
  exact iCount_iso e _

/-- `G` restricted to the vertex set `A`, as a graph on `V`. -/
def restr (G : SimpleGraph V) (A : Finset V) : SimpleGraph V where
  Adj u v := G.Adj u v ∧ u ∈ A ∧ v ∈ A
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.2, h.2.1⟩⟩
  loopless := ⟨fun _ h => h.1.ne rfl⟩

instance (G : SimpleGraph V) [DecidableRel G.Adj] (A : Finset V) : DecidableRel (restr G A).Adj :=
  fun u v => inferInstanceAs (Decidable (G.Adj u v ∧ u ∈ A ∧ v ∈ A))

theorem edgeFinset_restr (G : SimpleGraph V) [DecidableRel G.Adj] (A : Finset V) :
    (restr G A).edgeFinset = G.edgeFinset.filter (· ∈ A.sym2) := by
  ext z
  induction z using Sym2.ind with
  | h u v =>
    rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet, Finset.mem_filter,
      SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet, Finset.mk_mem_sym2_iff]
    rfl

/-- `2 e_G(A)` is the number of ordered pairs of adjacent vertices of `A`. -/
theorem two_mul_edgesIn (G : SimpleGraph V) [DecidableRel G.Adj] (A : Finset V) :
    2 * edgesIn G A = #(univ.filter fun p : V × V => G.Adj p.1 p.2 ∧ p.1 ∈ A ∧ p.2 ∈ A) := by
  rw [edgesIn, ← edgeFinset_restr, two_mul_card_edgeFinset]
  rfl

/-- A vertex set of `V ⊕ W` is a pair of vertex sets. -/
def finsetSumEquiv (V W : Type*) [DecidableEq V] [DecidableEq W] :
    Finset (V ⊕ W) ≃ Finset V × Finset W where
  toFun A := (A.toLeft, A.toRight)
  invFun p := p.1.disjSum p.2
  left_inv A := Finset.toLeft_disjSum_toRight
  right_inv p := by simp

omit [DecidableEq V] [DecidableEq W] in
/-- Splitting a double sum over `V ⊕ W` into its four blocks. -/
theorem sum_sum_sumType {M : Type*} [AddCommMonoid M] (f : V ⊕ W → V ⊕ W → M) (a b c e : M)
    (ha : ∑ x, ∑ y, f (.inl x) (.inl y) = a) (hb : ∑ x, ∑ y, f (.inl x) (.inr y) = b)
    (hc : ∑ x, ∑ y, f (.inr x) (.inl y) = c) (he : ∑ x, ∑ y, f (.inr x) (.inr y) = e) :
    ∑ p, ∑ q, f p q = a + b + (c + e) := by
  rw [← ha, ← hb, ← hc, ← he]
  simp only [Fintype.sum_sum_type, Finset.sum_add_distrib]
  abel

omit [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W] in
/-- `Σ_x Σ_y [x ∈ S ∧ y ∈ T] = |S| |T|`. -/
theorem sum_sum_ite_mem {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (S : Finset α) (T : Finset β) :
    ∑ x, ∑ y, (if x ∈ S ∧ y ∈ T then 1 else 0 : ℕ) = #S * #T := by
  rw [← Fintype.sum_prod_type', Finset.sum_boole, Nat.cast_id, ← Finset.card_product]
  congr 1
  ext p
  simp

/-- `e_{G ⊕ F}(S ⊔ T) = e_G(S) + e_F(T)`. -/
theorem edgesIn_sum (G : SimpleGraph V) (F : SimpleGraph W) [DecidableRel G.Adj]
    [DecidableRel F.Adj] (S : Finset V) (T : Finset W) :
    edgesIn (G ⊕g F) (S.disjSum T) = edgesIn G S + edgesIn F T := by
  have h := two_mul_edgesIn (G ⊕g F) (S.disjSum T)
  have hG := two_mul_edgesIn G S
  have hF := two_mul_edgesIn F T
  have key : #(univ.filter fun p : (V ⊕ W) × (V ⊕ W) =>
        (G ⊕g F).Adj p.1 p.2 ∧ p.1 ∈ S.disjSum T ∧ p.2 ∈ S.disjSum T) =
      #(univ.filter fun p : V × V => G.Adj p.1 p.2 ∧ p.1 ∈ S ∧ p.2 ∈ S) +
        #(univ.filter fun p : W × W => F.Adj p.1 p.2 ∧ p.1 ∈ T ∧ p.2 ∈ T) := by
    simp only [Finset.card_filter, Fintype.sum_prod_type]
    rw [sum_sum_sumType _ _ 0 0 _ (Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_)
      (Finset.sum_eq_zero fun x _ => Finset.sum_eq_zero fun y _ => ?_)
      (Finset.sum_eq_zero fun x _ => Finset.sum_eq_zero fun y _ => ?_)
      (Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_), add_zero, zero_add]
    all_goals simp
  omega

/-- A vertex set of `m` copies of a graph on `W` is a family of `m` vertex sets of `W`. -/
def fibresEquiv (m : ℕ) (W : Type*) [Fintype W] [DecidableEq W] :
    Finset (Fin m × W) ≃ (Fin m → Finset W) where
  toFun A i := univ.filter fun w => (i, w) ∈ A
  invFun f := univ.filter fun p => p.2 ∈ f p.1
  left_inv A := by ext ⟨i, w⟩; simp
  right_inv f := by funext i; ext w; simp

/-- `e_{mG}(A) = Σ_i e_G(A_i)`. -/
theorem edgesIn_copies (m : ℕ) (G : SimpleGraph W) [DecidableRel G.Adj] (f : Fin m → Finset W) :
    edgesIn (copies m G) ((fibresEquiv m W).symm f) = ∑ i, edgesIn G (f i) := by
  have h := two_mul_edgesIn (copies m G) ((fibresEquiv m W).symm f)
  have hi : ∀ i, 2 * edgesIn G (f i) =
      #(univ.filter fun p : W × W => G.Adj p.1 p.2 ∧ p.1 ∈ f i ∧ p.2 ∈ f i) :=
    fun i => two_mul_edgesIn G (f i)
  have key : #(univ.filter fun p : (Fin m × W) × (Fin m × W) =>
        (copies m G).Adj p.1 p.2 ∧ p.1 ∈ (fibresEquiv m W).symm f ∧
          p.2 ∈ (fibresEquiv m W).symm f) =
      ∑ i, #(univ.filter fun p : W × W => G.Adj p.1 p.2 ∧ p.1 ∈ f i ∧ p.2 ∈ f i) := by
    simp only [Finset.card_filter]
    rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Fintype.sum_prod_type, Finset.sum_eq_single i]
    · refine Finset.sum_congr rfl fun y _ => ?_
      simp [fibresEquiv]
    · intro j _ hj
      refine Finset.sum_eq_zero fun y _ => ?_
      simp [fibresEquiv, Ne.symm hj]
    · simp
  have : 2 * edgesIn (copies m G) ((fibresEquiv m W).symm f) = 2 * ∑ i, edgesIn G (f i) := by
    rw [h, key, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => (hi i).symm
  omega

/-- `e_{K_{d,d}}(S ⊔ T) = |S| |T|`. -/
theorem edgesIn_Kdd (d : ℕ) (S T : Finset (Fin d)) : edgesIn (Kdd d) (S.disjSum T) = #S * #T := by
  have h := two_mul_edgesIn (Kdd d) (S.disjSum T)
  have key : #(univ.filter fun p : (Fin d ⊕ Fin d) × (Fin d ⊕ Fin d) =>
        (Kdd d).Adj p.1 p.2 ∧ p.1 ∈ S.disjSum T ∧ p.2 ∈ S.disjSum T) = 2 * (#S * #T) := by
    simp only [Finset.card_filter, Fintype.sum_prod_type]
    rw [sum_sum_sumType _ 0 (#S * #T) (#T * #S) 0
      (Finset.sum_eq_zero fun x _ => Finset.sum_eq_zero fun y _ => ?_)
      ((Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_).trans (sum_sum_ite_mem S T))
      ((Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_).trans (sum_sum_ite_mem T S))
      (Finset.sum_eq_zero fun x _ => Finset.sum_eq_zero fun y _ => ?_)]
    · ring
    all_goals simp
  omega

end General

theorem check_IGammaFloor : IGammaFloor :=
  fun _ _ _ G _ d _ hγ => iGamma_eq_iCount_floor G d hγ

theorem check_IGammaIso : IGammaIso :=
  fun _ _ _ _ _ _ _ _ _ _ ⟨e⟩ d _ hγ => iGamma_iso e d hγ

#print axioms check_IGammaFloor
#print axioms check_IGammaIso

end P3Basic
