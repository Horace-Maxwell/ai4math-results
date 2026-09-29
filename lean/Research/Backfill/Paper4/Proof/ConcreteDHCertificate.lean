import Research.Backfill.Paper4.Challenge
import Research.HKOTriameter

/-! Soundness of finite cut-or-descent certificates for distance-hereditary graphs.
The conclusion uses every connected induced subgraph in the frozen definition.
Concrete certificate data and full frozen target checks are supplied in separate modules.
Compilation and acceptance evidence is recorded separately. -/
set_option autoImplicit false

namespace CodexPaper4.ConcreteDHCertificate
open BackfillPaper4

variable {V : Type*}

/-- A witnessed separation of the induced graph on `S`. -/
def Cut [DecidableEq V] (G : SimpleGraph V) (S C : Finset V) : Prop :=
  C ⊆ S ∧ C.Nonempty ∧ (S \ C).Nonempty ∧
    ∀ x ∈ C, ∀ y ∈ S \ C, ¬ G.Adj x y

/-- Every nonzero table distance has a decreasing adjacent step inside `S`. -/
def Descent (G : SimpleGraph V) (D : V → V → ℕ) (S : Finset V) : Prop :=
  ∀ x ∈ S, ∀ y ∈ S, D x y ≠ 0 →
    ∃ z ∈ S, G.Adj x z ∧ D z y + 1 = D x y

/-- A certificate for every actual finite vertex subset, including the empty subset. -/
def Valid [DecidableEq V] (G : SimpleGraph V) (D : V → V → ℕ)
    (cut : Finset V → Finset V) : Prop :=
  ∀ S : Finset V, Cut G S (cut S) ∨ Descent G D S

/-- A separating cut contradicts connectivity of the corresponding induced graph.
The membership equivalence allows application to an arbitrary set via `Set.toFinset`. -/
theorem cut_not_connected [DecidableEq V] (G : SimpleGraph V) (s : Set V)
    (S C : Finset V) (hmem : ∀ x, x ∈ S ↔ x ∈ s) (hcut : Cut G S C) :
    ¬ (G.induce s).Connected := by
  intro hconn
  rcases hcut with ⟨hCS, ⟨x, hx⟩, ⟨y, hy⟩, hsep⟩
  have hxS : x ∈ S := hCS hx
  have hyS : y ∈ S := (Finset.mem_sdiff.mp hy).1
  have hyC : y ∉ C := (Finset.mem_sdiff.mp hy).2
  have hclosed : ∀ {a b : s}, (G.induce s).Adj a b →
      (a : V) ∈ C → (b : V) ∈ C := by
    intro a b hab ha
    by_contra hb
    have hbS : (b : V) ∈ S := (hmem b).mpr b.property
    exact hsep a ha b (Finset.mem_sdiff.mpr ⟨hbS, hb⟩) hab
  have hwalk : ∀ {a b : s}, (G.induce s).Walk a b →
      (a : V) ∈ C → (b : V) ∈ C := by
    intro a b p
    induction p with
    | nil => exact fun ha => ha
    | @cons a b c hab p ih => exact fun ha => ih (hclosed hab ha)
  let a : s := ⟨x, (hmem x).mp hxS⟩
  let b : s := ⟨y, (hmem y).mp hyS⟩
  obtain ⟨p⟩ := hconn a b
  exact hyC (hwalk p hx)

/-- Complete semantic bridge: valid finite certificates imply the frozen DH definition.
All concrete distance assumptions are equalities with the actual graph metric. -/
theorem isDistanceHereditary [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (D : V → V → ℕ) (cut : Finset V → Finset V)
    (hc : G.Connected) (hd : ∀ x y, G.dist x y = D x y)
    (hcert : Valid G D cut) : Challenge.IsDistanceHereditary G := by
  classical
  refine ⟨hc, ?_⟩
  intro s hs
  have hmem : ∀ x, x ∈ s.toFinset ↔ x ∈ s := by
    intro x
    exact Set.mem_toFinset
  have hdesc : Descent G D s.toFinset := by
    rcases hcert s.toFinset with hcut | hdesc
    · exact False.elim (cut_not_connected G s s.toFinset (cut s.toFinset) hmem hcut hs)
    · exact hdesc
  have hself : ∀ x : s, D x.val x.val = 0 := by
    intro x
    rw [← hd]
    exact SimpleGraph.dist_self
  have hzero : ∀ x y : s, D x.val y.val = 0 → x = y := by
    intro x y hxy
    apply Subtype.ext
    apply hc.dist_eq_zero_iff.mp
    rw [hd]
    exact hxy
  have hstep : ∀ x y : s, D x.val y.val ≠ 0 →
      ∃ z : s, (G.induce s).Adj x z ∧ D z.val y.val + 1 = D x.val y.val := by
    intro x y hxy
    obtain ⟨z, hz, hxz, hzy⟩ :=
      hdesc x.val ((hmem x.val).mpr x.property)
        y.val ((hmem y.val).mpr y.property) hxy
    exact ⟨⟨z, (hmem z).mp hz⟩, hxz, hzy⟩
  have hlip : ∀ u v w : s, (G.induce s).Adj u v →
      D u.val w.val ≤ D v.val w.val + 1 := by
    intro u v w huv
    have htri := hc.dist_triangle (u := u.val) (v := v.val) (w := w.val)
    have hone : G.dist u.val v.val = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr huv
    rw [hone, hd u.val w.val, hd v.val w.val] at htri
    omega
  have hdist : ∀ u v : s, (G.induce s).dist u v = D u.val v.val :=
    HKOTriameter.dist_eq_of_certificate (G.induce s) (fun u v => D u.val v.val)
      hself hzero hstep hlip
  intro u v
  exact (hdist u v).trans (hd u.val v.val).symm

#print axioms isDistanceHereditary

end CodexPaper4.ConcreteDHCertificate
