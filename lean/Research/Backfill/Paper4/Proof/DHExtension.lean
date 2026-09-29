import Research.Backfill.Paper4.Proof.DHExtensionCore

/-! Pendant and twin extensions for the frozen distance-hereditary definition.
All induced vertex sets and both twin types are included.
Compilation and acceptance evidence is recorded separately. -/
set_option autoImplicit false

namespace CodexPaper4
open BackfillPaper4
namespace DHExtension

noncomputable def foldVertex {V : Type*} (v t : V) (ht : t ≠ v) : V → ({v}ᶜ : Set V) := by
  classical
  exact fun x => if h : x = v then ⟨t, ht⟩ else ⟨x, h⟩

theorem fold_delete {V : Type*} (G : SimpleGraph V) {v t : V}
    (ht : t ≠ v) (hc : G.Connected)
    (hfold : ∀ x, G.Adj v x → x = t ∨ G.Adj t x) :
    (G.induce {v}ᶜ).Connected ∧
      ∀ x y : ({v}ᶜ : Set V), (G.induce {v}ᶜ).dist x y = G.dist x.val y.val := by
  classical
  apply DHExtensionCore.induce_retract G {v}ᶜ (foldVertex v t ht) hc
  · intro x
    have hx : x.val ≠ v := x.property
    simp [foldVertex, hx]
  · intro x y hxy
    by_cases hx : x = v
    · subst x
      have hy : y ≠ v := hxy.ne'
      rcases hfold y hxy with hyt | hty
      · left
        subst y
        simp [foldVertex, ht]
      · right
        simpa [foldVertex, hy] using hty
    · by_cases hy : y = v
      · subst y
        rcases hfold x hxy.symm with hxt | htx
        · left
          subst x
          simp [foldVertex, ht]
        · right
          simpa [foldVertex, hx] using htx.symm
      · right
        simpa [foldVertex, hx, hy] using hxy

def avoidEmbedding {V : Type*} (G : SimpleGraph V) (v : V) (s : Set V)
    (hv : v ∉ s) : G.induce s ↪g G.induce {v}ᶜ where
  toFun x := ⟨x.val, by
    change x.val ≠ v
    intro h
    exact hv (h ▸ x.property)⟩
  inj' := by
    intro x y h
    exact Subtype.ext (congrArg (fun z : ({v}ᶜ : Set V) => z.val) h)
  map_rel_iff' := by intro x y; rfl

def deletedInduceEmbedding {V : Type*} (G : SimpleGraph V) (v : V) (s : Set V)
    (hv : v ∈ s) :
    (G.induce s).induce ({(⟨v, hv⟩ : s)}ᶜ) ↪g G.induce {v}ᶜ where
  toFun x := ⟨x.val.val, by
    change x.val.val ≠ v
    intro h
    have hx : x.val ≠ (⟨v, hv⟩ : s) := x.property
    exact hx (Subtype.ext h)⟩
  inj' := by
    intro x y h
    exact Subtype.ext (Subtype.ext (congrArg (fun z : ({v}ᶜ : Set V) => z.val) h))
  map_rel_iff' := by intro x y; rfl

theorem pendant_dist {V : Type*} (G : SimpleGraph V) {v p : V}
    (hc : G.Connected) (hp : ∀ x, G.Adj v x ↔ x = p)
    (x : V) (hx : x ≠ v) : G.dist v x = 1 + G.dist p x := by
  have hvp : G.Adj v p := (hp p).mpr rfl
  have hu := hc.dist_triangle (u := v) (v := p) (w := x)
  have h1 : G.dist v p = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr hvp
  have hl : 1 + G.dist p x ≤ G.dist v x := by
    obtain ⟨w, hw⟩ := hc.exists_walk_length_eq_dist v x
    cases w with
    | nil => exact (hx rfl).elim
    | @cons a b c hab w =>
      have hbp : b = p := (hp b).mp hab
      subst b
      have hle := SimpleGraph.dist_le w
      simp only [SimpleGraph.Walk.length_cons] at hw
      omega
  omega

theorem pendant_extension {V : Type*} (G : SimpleGraph V) (v : V)
    (hc : G.Connected) (hv : Challenge.IsPendant G v)
    (hb : Challenge.IsDistanceHereditary (G.induce {v}ᶜ)) :
    Challenge.IsDistanceHereditary G := by
  classical
  obtain ⟨p, hpN⟩ := hv
  have hp : ∀ x, G.Adj v x ↔ x = p := by
    intro x
    change x ∈ G.neighborSet v ↔ x ∈ ({p} : Set V)
    rw [hpN]
  have hvp : G.Adj v p := (hp p).mpr rfl
  have hpv : p ≠ v := hvp.ne'
  have hbase := fold_delete G hpv hc (fun x hx => Or.inl ((hp x).mp hx))
  refine ⟨hc, ?_⟩
  intro s hs x y
  by_cases hvs : v ∈ s
  · let vs : s := ⟨v, hvs⟩
    by_cases hsingle : ∀ z : s, z = vs
    · have hxy : x = y := (hsingle x).trans (hsingle y).symm
      subst y
      simp only [SimpleGraph.dist_self]
    · obtain ⟨z, hz⟩ := not_forall.mp hsingle
      have hne : vs ≠ z := Ne.symm hz
      obtain ⟨w, hvw⟩ := (hs vs z).nonempty_neighborSet_left hne
      have hwp : w.val = p := (hp w.val).mp hvw
      have hps : p ∈ s := hwp ▸ w.property
      let ps : s := ⟨p, hps⟩
      have hpsvs : ps ≠ vs := by
        intro h
        exact hpv (congrArg Subtype.val h)
      have hplocal : ∀ z : s, (G.induce s).Adj vs z ↔ z = ps := by
        intro z
        simpa only [SimpleGraph.induce_adj, Subtype.ext_iff] using hp z.val
      have hlocal := fold_delete (G.induce s) hpsvs hs
        (fun z hz => Or.inl ((hplocal z).mp hz))
      have hdist : ∀ a b : s, a ≠ vs → b ≠ vs →
          (G.induce s).dist a b = G.dist a.val b.val := by
        intro a b ha hb'
        let aa : ({vs}ᶜ : Set s) := ⟨a, ha⟩
        let bb : ({vs}ᶜ : Set s) := ⟨b, hb'⟩
        have h1 := hlocal.2 aa bb
        have h2 := DHExtensionCore.embedding_dist_eq hb
          (deletedInduceEmbedding G v s hvs) hlocal.1 aa bb
        have h3 := hbase.2
          ((deletedInduceEmbedding G v s hvs) aa)
          ((deletedInduceEmbedding G v s hvs) bb)
        exact h1.symm.trans (h2.trans h3)
      by_cases hx : x = vs
      · subst x
        by_cases hy : y = vs
        · subst y
          simp only [SimpleGraph.dist_self]
        · have hyv : y.val ≠ v := by
            intro h
            exact hy (Subtype.ext h)
          calc
            (G.induce s).dist vs y = 1 + (G.induce s).dist ps y :=
              pendant_dist (G.induce s) hs hplocal y hy
            _ = 1 + G.dist p y.val := congrArg (1 + ·) (hdist ps y hpsvs hy)
            _ = G.dist v y.val := (pendant_dist G hc hp y.val hyv).symm
      · by_cases hy : y = vs
        · subst y
          have hxv : x.val ≠ v := by
            intro h
            exact hx (Subtype.ext h)
          calc
            (G.induce s).dist x vs = (G.induce s).dist vs x :=
              (G.induce s).dist_comm
            _ = 1 + (G.induce s).dist ps x := pendant_dist (G.induce s) hs hplocal x hx
            _ = 1 + G.dist p x.val := congrArg (1 + ·) (hdist ps x hpsvs hx)
            _ = G.dist v x.val := (pendant_dist G hc hp x.val hxv).symm
            _ = G.dist x.val v := G.dist_comm
        · exact hdist x y hx hy
  · have h1 := DHExtensionCore.embedding_dist_eq hb (avoidEmbedding G v s hvs) hs x y
    have h2 := hbase.2 ((avoidEmbedding G v s hvs) x) ((avoidEmbedding G v s hvs) y)
    exact h1.trans h2

theorem twins_adj {V : Type*} {G : SimpleGraph V} {v t x : V}
    (ht : Challenge.AreTwins G v t) (hxv : x ≠ v) (hxt : x ≠ t) :
    G.Adj v x ↔ G.Adj t x := by
  have h := Set.ext_iff.mp ht.2 x
  change (G.Adj v x ∧ x ≠ t) ↔ (G.Adj t x ∧ x ≠ v) at h
  exact ⟨fun hvx => (h.mp ⟨hvx, hxt⟩).1, fun htx => (h.mpr ⟨htx, hxv⟩).1⟩

theorem twins_fold {V : Type*} {G : SimpleGraph V} {v t : V}
    (ht : Challenge.AreTwins G v t) :
    ∀ x, G.Adj v x → x = t ∨ G.Adj t x := by
  intro x hx
  by_cases hxt : x = t
  · exact Or.inl hxt
  · exact Or.inr ((twins_adj ht hx.ne' hxt).mp hx)

theorem twins_swap_adj {V : Type*} [DecidableEq V] {G : SimpleGraph V} {v t : V}
    (ht : Challenge.AreTwins G v t) (x y : V) :
    G.Adj (Equiv.swap v t x) (Equiv.swap v t y) ↔ G.Adj x y := by
  by_cases hxv : x = v
  · subst x
    by_cases hyv : y = v
    · subst y
      simp only [Equiv.swap_apply_left, SimpleGraph.irrefl, iff_self]
    · by_cases hyt : y = t
      · subst y
        simpa only [Equiv.swap_apply_left, Equiv.swap_apply_right] using G.adj_comm t v
      · simpa only [Equiv.swap_apply_left, Equiv.swap_apply_of_ne_of_ne hyv hyt] using
          (twins_adj ht hyv hyt).symm
  · by_cases hxt : x = t
    · subst x
      by_cases hyv : y = v
      · subst y
        simpa only [Equiv.swap_apply_left, Equiv.swap_apply_right] using G.adj_comm v t
      · by_cases hyt : y = t
        · subst y
          simp only [Equiv.swap_apply_right, SimpleGraph.irrefl, iff_self]
        · simpa only [Equiv.swap_apply_right, Equiv.swap_apply_of_ne_of_ne hyv hyt] using
            twins_adj ht hyv hyt
    · by_cases hyv : y = v
      · subst y
        simp only [Equiv.swap_apply_left, Equiv.swap_apply_of_ne_of_ne hxv hxt]
        exact (G.adj_comm x t).trans ((twins_adj ht hxv hxt).symm.trans (G.adj_comm v x))
      · by_cases hyt : y = t
        · subst y
          simp only [Equiv.swap_apply_right, Equiv.swap_apply_of_ne_of_ne hxv hxt]
          exact (G.adj_comm x v).trans ((twins_adj ht hxv hxt).trans (G.adj_comm t x))
        · simp only [Equiv.swap_apply_of_ne_of_ne hxv hxt,
            Equiv.swap_apply_of_ne_of_ne hyv hyt, iff_self]

noncomputable def twinSwap {V : Type*} {G : SimpleGraph V} {v t : V}
    (ht : Challenge.AreTwins G v t) : G ≃g G := by
  classical
  exact { toEquiv := Equiv.swap v t
          map_rel_iff' := by intro x y; exact twins_swap_adj ht x y }

theorem twinSwap_v {V : Type*} {G : SimpleGraph V} {v t : V}
    (ht : Challenge.AreTwins G v t) : twinSwap ht v = t := by
  classical
  change Equiv.swap v t v = t
  exact Equiv.swap_apply_left _ _

theorem twinSwap_t {V : Type*} {G : SimpleGraph V} {v t : V}
    (ht : Challenge.AreTwins G v t) : twinSwap ht t = v := by
  classical
  change Equiv.swap v t t = v
  exact Equiv.swap_apply_right _ _

theorem twinSwap_other {V : Type*} {G : SimpleGraph V} {v t x : V}
    (ht : Challenge.AreTwins G v t) (hxv : x ≠ v) (hxt : x ≠ t) :
    twinSwap ht x = x := by
  classical
  change Equiv.swap v t x = x
  exact Equiv.swap_apply_of_ne_of_ne hxv hxt

theorem twins_dist_other {V : Type*} {G : SimpleGraph V} {v t x : V}
    (hc : G.Connected) (ht : Challenge.AreTwins G v t)
    (hxv : x ≠ v) (hxt : x ≠ t) : G.dist v x = G.dist t x := by
  have h := DHExtensionCore.iso_dist_eq (twinSwap ht) hc v x
  rw [twinSwap_v ht, twinSwap_other ht hxv hxt] at h
  exact h.symm

theorem twins_dist_two {V : Type*} {G : SimpleGraph V} {v t : V}
    (hc : G.Connected) (ht : Challenge.AreTwins G v t) (hn : ¬ G.Adj v t) :
    G.dist v t = 2 := by
  obtain ⟨z, hvz⟩ := (hc v t).nonempty_neighborSet_left ht.1
  have hzt : z ≠ t := by
    intro h
    exact hn (h ▸ hvz)
  have htz : G.Adj t z := (twins_adj ht hvz.ne' hzt).mp hvz
  have h1 : G.dist v z = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr hvz
  have h2 : G.dist z t = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr htz.symm
  have hu := hc.dist_triangle (u := v) (v := z) (w := t)
  have hl := hc.one_lt_dist_of_ne_of_not_adj ht.1 hn
  omega

theorem twins_induce {V : Type*} {G : SimpleGraph V} {v t : V}
    (ht : Challenge.AreTwins G v t) (s : Set V) (hv : v ∈ s) (htt : t ∈ s) :
    Challenge.AreTwins (G.induce s) (⟨v, hv⟩ : s) (⟨t, htt⟩ : s) := by
  refine ⟨?_, ?_⟩
  · intro h
    exact ht.1 (congrArg Subtype.val h)
  · ext x
    simpa only [Set.mem_sdiff, SimpleGraph.mem_neighborSet, Set.mem_singleton_iff,
      SimpleGraph.induce_adj, Subtype.ext_iff] using Set.ext_iff.mp ht.2 x.val

noncomputable def swapAvoidEmbedding {V : Type*} {G : SimpleGraph V} {v t : V}
    (ht : Challenge.AreTwins G v t) (s : Set V) (hnt : t ∉ s) :
    G.induce s ↪g G.induce {v}ᶜ where
  toFun x := ⟨twinSwap ht x.val, by
    change twinSwap ht x.val ≠ v
    intro h
    have hxt : x.val = t := (twinSwap ht).injective (h.trans (twinSwap_t ht).symm)
    exact hnt (hxt ▸ x.property)⟩
  inj' := by
    intro x y h
    exact Subtype.ext ((twinSwap ht).injective (congrArg Subtype.val h))
  map_rel_iff' := by
    intro x y
    exact (twinSwap ht).map_adj_iff

theorem twins_extension {V : Type*} (G : SimpleGraph V) (v t : V)
    (hc : G.Connected) (ht : Challenge.AreTwins G v t)
    (hb : Challenge.IsDistanceHereditary (G.induce {v}ᶜ)) :
    Challenge.IsDistanceHereditary G := by
  classical
  have hbase := fold_delete G ht.1.symm hc (twins_fold ht)
  refine ⟨hc, ?_⟩
  intro s hs x y
  by_cases hvs : v ∈ s
  · by_cases hts : t ∈ s
    · let vs : s := ⟨v, hvs⟩
      let ts : s := ⟨t, hts⟩
      have htw : Challenge.AreTwins (G.induce s) vs ts := twins_induce ht s hvs hts
      have hlocal := fold_delete (G.induce s) htw.1.symm hs (twins_fold htw)
      have hdist : ∀ a b : s, a ≠ vs → b ≠ vs →
          (G.induce s).dist a b = G.dist a.val b.val := by
        intro a b ha hb'
        let aa : ({vs}ᶜ : Set s) := ⟨a, ha⟩
        let bb : ({vs}ᶜ : Set s) := ⟨b, hb'⟩
        have h1 := hlocal.2 aa bb
        have h2 := DHExtensionCore.embedding_dist_eq hb
          (deletedInduceEmbedding G v s hvs) hlocal.1 aa bb
        have h3 := hbase.2
          ((deletedInduceEmbedding G v s hvs) aa)
          ((deletedInduceEmbedding G v s hvs) bb)
        exact h1.symm.trans (h2.trans h3)
      have hpair : (G.induce s).dist vs ts = G.dist v t := by
        by_cases ha : G.Adj v t
        · have ha' : (G.induce s).Adj vs ts := ha
          exact (SimpleGraph.dist_eq_one_iff_adj.mpr ha').trans
            (SimpleGraph.dist_eq_one_iff_adj.mpr ha).symm
        · have ha' : ¬ (G.induce s).Adj vs ts := ha
          exact (twins_dist_two hs htw ha').trans (twins_dist_two hc ht ha).symm
      have hfrom : ∀ z : s, (G.induce s).dist vs z = G.dist v z.val := by
        intro z
        by_cases hzv : z = vs
        · subst z
          simp only [vs, SimpleGraph.dist_self]
        · by_cases hzt : z = ts
          · subst z
            exact hpair
          · have hzv' : z.val ≠ v := by
              intro h
              exact hzv (Subtype.ext h)
            have hzt' : z.val ≠ t := by
              intro h
              exact hzt (Subtype.ext h)
            calc
              (G.induce s).dist vs z = (G.induce s).dist ts z :=
                twins_dist_other hs htw hzv hzt
              _ = G.dist t z.val := hdist ts z htw.1.symm hzv
              _ = G.dist v z.val := (twins_dist_other hc ht hzv' hzt').symm
      by_cases hx : x = vs
      · subst x
        exact hfrom y
      · by_cases hy : y = vs
        · subst y
          calc
            (G.induce s).dist x vs = (G.induce s).dist vs x := (G.induce s).dist_comm
            _ = G.dist v x.val := hfrom x
            _ = G.dist x.val v := G.dist_comm
        · exact hdist x y hx hy
    · have h1 := DHExtensionCore.embedding_dist_eq hb (swapAvoidEmbedding ht s hts) hs x y
      have h2 := hbase.2 ((swapAvoidEmbedding ht s hts) x) ((swapAvoidEmbedding ht s hts) y)
      have h3 := DHExtensionCore.iso_dist_eq (twinSwap ht) hc x.val y.val
      exact h1.trans (h2.trans h3)
  · have h1 := DHExtensionCore.embedding_dist_eq hb (avoidEmbedding G v s hvs) hs x y
    have h2 := hbase.2 ((avoidEmbedding G v s hvs) x) ((avoidEmbedding G v s hvs) y)
    exact h1.trans h2

end DHExtension

theorem check_BandeltMulder_extension : Challenge.BandeltMulder_extension := by
  intro V _ G v hc he hb
  rcases he with hp | ⟨t, ht⟩
  · exact DHExtension.pendant_extension G v hc hp hb
  · exact DHExtension.twins_extension G v t hc ht hb

#print axioms check_BandeltMulder_extension

end CodexPaper4
