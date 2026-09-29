import Research.Backfill.Paper4.Challenge
import Research.Backfill.Paper4.Proof.MedianMetricTransport

/-!
# Counting automorphisms and labelled copies of a finite graph

(Written by Claude, 2026-09-28, while Codex was out of quota.)

* `orbit_card`: the labelled graphs on `V` isomorphic to `H`, times the automorphisms of `H`,
  number `|V|!`.
* `autFix H bs`: the automorphisms of `H` (as permutations) fixing every vertex of `bs`.
  `card_step` is the orbit–stabilizer step: if the automorphisms fixing `bs` move `b` exactly
  onto the finite set `O`, then `|autFix H bs| = |O| · |autFix H (b :: bs)|`.
* `col D bs r`: a vertex colour from a table `D` (the distance table) and the list `bs`,
  refined `r` times, each time by a hash of the multiset of pairs (table entry, colour). Only its
  invariance is used: it is invariant under every automorphism fixing `bs`; this certifies that
  an automorphism cannot move `b` outside `O` (`closed_of_col`), and that only the identity
  fixes `bs` when the colours are pairwise distinct (`card_one_of_col`).
-/

set_option autoImplicit false

namespace ClaudePaper4.AutCount

open Finset SimpleGraph

variable {V : Type} [Fintype V] [DecidableEq V]

/-! ## Labelled copies -/

theorem orbit_card (H : SimpleGraph V) :
    Nat.card {G : SimpleGraph V // Nonempty (G ≃g H)} * Nat.card (H ≃g H) =
      (Fintype.card V).factorial := by
  classical
  let π : Equiv.Perm V → SimpleGraph V := fun σ => H.comap σ
  have hπ : ∀ σ τ : Equiv.Perm V, π σ = π τ ↔ ∀ x y, H.Adj (σ x) (σ y) ↔ H.Adj (τ x) (τ y) := by
    intro σ τ
    constructor
    · intro h x y
      have := congrArg (fun G : SimpleGraph V => G.Adj x y) h
      simpa [π] using this
    · intro h
      ext x y
      simpa [π] using h x y
  have himage : univ.image π = univ.filter (fun G : SimpleGraph V => Nonempty (G ≃g H)) := by
    ext G
    simp only [mem_image, mem_univ, true_and, mem_filter]
    constructor
    · rintro ⟨σ, rfl⟩
      exact ⟨Iso.comap σ H⟩
    · rintro ⟨e⟩
      refine ⟨e.toEquiv, ?_⟩
      ext x y
      simp only [π, comap_adj]
      exact e.map_adj_iff
  -- every fibre of `π` over its image has as many elements as the fibre over `H`
  have hfib : ∀ G ∈ univ.image π, #{σ ∈ (univ : Finset (Equiv.Perm V)) | π σ = G} =
      #{σ ∈ (univ : Finset (Equiv.Perm V)) | π σ = H} := by
    intro G hG
    obtain ⟨τ, -, rfl⟩ := mem_image.mp hG
    refine card_nbij' (fun σ => σ * τ⁻¹) (fun ρ => ρ * τ) ?_ ?_ ?_ ?_
    · intro σ hσ
      simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hσ ⊢
      have h := (hπ σ τ).mp hσ
      ext x y
      simp only [π, comap_adj, Equiv.Perm.coe_mul, Function.comp_apply]
      simpa using h (τ⁻¹ x) (τ⁻¹ y)
    · intro ρ hρ
      simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hρ ⊢
      refine (hπ _ τ).mpr fun x y => ?_
      have := congrArg (fun G : SimpleGraph V => G.Adj (τ x) (τ y)) hρ
      simpa [π] using this
    · intro σ _
      simp
    · intro ρ _
      simp
  have hH : #{σ ∈ (univ : Finset (Equiv.Perm V)) | π σ = H} = Nat.card (H ≃g H) := by
    rw [← Nat.card_eq_finsetCard]
    refine Nat.card_congr
      { toFun := fun σ => { toEquiv := σ.1, map_rel_iff' := ?_ }
        invFun := fun e => ⟨e.toEquiv, ?_⟩
        left_inv := fun σ => rfl
        right_inv := fun e => rfl }
    · intro x y
      have h := σ.2
      simp only [mem_filter, mem_univ, true_and] at h
      have := congrArg (fun G : SimpleGraph V => G.Adj x y) h
      simpa [π] using this
    · simp only [mem_filter, mem_univ, true_and]
      ext x y
      simp only [π, comap_adj]
      exact e.map_adj_iff
  have htot := card_eq_sum_card_image π (univ : Finset (Equiv.Perm V))
  rw [sum_congr rfl hfib, sum_const, smul_eq_mul, hH, card_univ, Fintype.card_perm, himage] at htot
  rw [htot, Nat.card_eq_fintype_card, Fintype.card_subtype]

/-! ## Automorphisms fixing a list of vertices -/

/-- `σ` is an automorphism of `H`. -/
def IsAut (H : SimpleGraph V) (σ : Equiv.Perm V) : Prop :=
  ∀ x y, H.Adj (σ x) (σ y) ↔ H.Adj x y

/-- The automorphisms of `H` fixing every vertex of `bs`. -/
noncomputable def autFix (H : SimpleGraph V) (bs : List V) : Finset (Equiv.Perm V) := by
  classical
  exact univ.filter fun σ => IsAut H σ ∧ ∀ c ∈ bs, σ c = c

theorem mem_autFix {H : SimpleGraph V} {bs : List V} {σ : Equiv.Perm V} :
    σ ∈ autFix H bs ↔ IsAut H σ ∧ ∀ c ∈ bs, σ c = c := by
  classical
  unfold autFix
  simp only [mem_filter, mem_univ, true_and]

omit [Fintype V] [DecidableEq V] in
theorem isAut_mul {H : SimpleGraph V} {σ τ : Equiv.Perm V} (hσ : IsAut H σ) (hτ : IsAut H τ) :
    IsAut H (σ * τ) := fun x y => by
  simp only [Equiv.Perm.coe_mul, Function.comp_apply]
  exact (hσ _ _).trans (hτ x y)

omit [Fintype V] [DecidableEq V] in
theorem isAut_inv {H : SimpleGraph V} {σ : Equiv.Perm V} (hσ : IsAut H σ) : IsAut H σ⁻¹ :=
  fun x y => by
    have h := hσ (σ⁻¹ x) (σ⁻¹ y)
    simp only [Equiv.Perm.coe_inv, Equiv.apply_symm_apply] at h
    exact h.symm

theorem natCard_aut (H : SimpleGraph V) : Nat.card (H ≃g H) = #(autFix H []) := by
  rw [← Nat.card_eq_finsetCard]
  refine Nat.card_congr
    { toFun := fun e => ⟨e.toEquiv, mem_autFix.mpr ⟨fun x y => e.map_adj_iff, by simp⟩⟩
      invFun := fun σ => { toEquiv := σ.1, map_rel_iff' := fun {x y} => (mem_autFix.mp σ.2).1 x y }
      left_inv := fun e => rfl
      right_inv := fun σ => rfl }

/-- The orbit–stabilizer step. -/
theorem card_step (H : SimpleGraph V) (bs : List V) (b : V) (O : Finset V)
    (hreach : ∀ x ∈ O, ∃ τ ∈ autFix H bs, τ b = x)
    (hclosed : ∀ σ ∈ autFix H bs, σ b ∈ O) :
    #(autFix H bs) = #O * #(autFix H (b :: bs)) := by
  classical
  rw [card_eq_sum_card_fiberwise (f := fun σ : Equiv.Perm V => σ b) (t := O)
    (fun σ hσ => hclosed σ hσ)]
  rw [← smul_eq_mul, ← sum_const]
  refine sum_congr rfl fun x hx => ?_
  obtain ⟨τ, hτ, hτb⟩ := hreach x hx
  obtain ⟨hτa, hτf⟩ := mem_autFix.mp hτ
  refine card_nbij' (fun σ => τ⁻¹ * σ) (fun ρ => τ * ρ) ?_ ?_ ?_ ?_
  · intro σ hσ
    simp only [coe_filter, Set.mem_ofPred_eq] at hσ
    obtain ⟨hσ, hσb⟩ := hσ
    obtain ⟨hσa, hσf⟩ := mem_autFix.mp hσ
    refine mem_autFix.mpr ⟨isAut_mul (isAut_inv hτa) hσa, ?_⟩
    intro c hc
    rcases List.mem_cons.mp hc with rfl | hc
    · simp only [Equiv.Perm.coe_mul, Function.comp_apply, hσb, ← hτb, Equiv.Perm.coe_inv,
        Equiv.symm_apply_apply]
    · simp only [Equiv.Perm.coe_mul, Function.comp_apply, hσf c hc]
      rw [Equiv.Perm.inv_eq_iff_eq, hτf c hc]
  · intro ρ hρ
    obtain ⟨hρa, hρf⟩ := mem_autFix.mp hρ
    simp only [coe_filter, Set.mem_ofPred_eq]
    refine ⟨mem_autFix.mpr ⟨isAut_mul hτa hρa, fun c hc => ?_⟩, ?_⟩
    · simp only [Equiv.Perm.coe_mul, Function.comp_apply, hρf c (List.mem_cons_of_mem b hc),
        hτf c hc]
    · simp only [Equiv.Perm.coe_mul, Function.comp_apply, hρf b List.mem_cons_self, hτb]
  · intro σ _
    simp
  · intro ρ _
    simp

theorem card_one (H : SimpleGraph V) (bs : List V) (h : ∀ σ ∈ autFix H bs, σ = 1) :
    #(autFix H bs) = 1 := by
  rw [card_eq_one]
  refine ⟨1, ?_⟩
  ext σ
  simp only [mem_singleton]
  constructor
  · exact h σ
  · rintro rfl
    exact mem_autFix.mpr ⟨fun x y => Iff.rfl, fun c _ => rfl⟩

/-! ## Witnesses given as vectors -/

/-- One explicit automorphism, given as a vector, fixing `bs` and sending `b` to `x`. -/
theorem wit (H : SimpleGraph V) (bs : List V) (b x : V) (w : V → V) (hbij : Function.Bijective w)
    (hadj : ∀ x y, H.Adj (w x) (w y) ↔ H.Adj x y) (hfix : ∀ c ∈ bs, w c = c) (hb : w b = x) :
    ∃ τ ∈ autFix H bs, τ b = x :=
  ⟨Equiv.ofBijective w hbij, mem_autFix.mpr ⟨hadj, hfix⟩, hb⟩

/-! ## Invariant colours -/

/-- A mixing function (any function would do for soundness). -/
def hmix (d c : ℕ) : ℕ := ((d + 1) * 7919 + c) ^ 3 % 1000000007

/-- The list of table entries from `x` to the vertices of `bs`, coded as a number. -/
def col0 (D : V → V → ℕ) (bs : List V) (x : V) : ℕ :=
  (bs.map (D x)).foldl (fun a d => a * 16 + d + 1) 0

/-- `r` rounds of refinement of `col0` by a hash of the multiset of pairs (table entry, colour):
a sum of `hmix` values, taken mod a prime. A collision could only make a certificate fail. -/
def col (D : V → V → ℕ) (bs : List V) : ℕ → V → ℕ
  | 0, x => col0 D bs x
  | r + 1, x => (col D bs r x * 1000003 + ∑ y, hmix (D x y) (col D bs r y)) % 1000000007

omit [DecidableEq V] in
theorem col_inv (D : V → V → ℕ) (bs : List V) (σ : Equiv.Perm V)
    (hD : ∀ x y, D (σ x) (σ y) = D x y) (hfix : ∀ c ∈ bs, σ c = c) :
    ∀ r x, col D bs r (σ x) = col D bs r x := by
  intro r
  induction r with
  | zero =>
    intro x
    simp only [col, col0]
    congr 1
    refine List.map_congr_left fun c hc => ?_
    calc D (σ x) c = D (σ x) (σ c) := by rw [hfix c hc]
      _ = D x c := hD x c
  | succ r ih =>
    intro x
    simp only [col]
    rw [ih x, ← Equiv.sum_comp σ (fun y => hmix (D (σ x) y) (col D bs r y))]
    simp only [hD, ih]

omit [Fintype V] [DecidableEq V] in
/-- The distance table of a connected graph is invariant under its automorphisms. -/
theorem table_inv (H : SimpleGraph V) (D : V → V → ℕ) (hD : ∀ x y, H.dist x y = D x y)
    (hc : H.Connected) (σ : Equiv.Perm V) (hσ : IsAut H σ) : ∀ x y, D (σ x) (σ y) = D x y := by
  intro x y
  let e : H ≃g H := { toEquiv := σ, map_rel_iff' := fun {a b} => hσ a b }
  rw [← hD, ← hD]
  exact CodexPaper4.MedianMetricTransport.dist_eq e hc x y

theorem closed_of_col (H : SimpleGraph V) (D : V → V → ℕ) (hD : ∀ x y, H.dist x y = D x y)
    (hc : H.Connected) (bs : List V) (r : ℕ) (b : V) (O : Finset V)
    (hcol : ∀ x, col D bs r x = col D bs r b → x ∈ O) :
    ∀ σ ∈ autFix H bs, σ b ∈ O := by
  intro σ hσ
  obtain ⟨hσa, hσf⟩ := mem_autFix.mp hσ
  exact hcol (σ b) (col_inv D bs σ (table_inv H D hD hc σ hσa) hσf r b)

theorem card_one_of_col (H : SimpleGraph V) (D : V → V → ℕ) (hD : ∀ x y, H.dist x y = D x y)
    (hc : H.Connected) (bs : List V) (r : ℕ)
    (hsep : ∀ x y, col D bs r x = col D bs r y → x = y) :
    #(autFix H bs) = 1 := by
  refine card_one H bs fun σ hσ => ?_
  obtain ⟨hσa, hσf⟩ := mem_autFix.mp hσ
  ext x
  simpa using hsep (σ x) x (col_inv D bs σ (table_inv H D hD hc σ hσa) hσf r x)

#print axioms orbit_card
#print axioms card_step
#print axioms card_one_of_col

end ClaudePaper4.AutCount
