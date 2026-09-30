import Research.Backfill.Paper8.Proof.Orb.Orbits

/-!
# Paper 8, orbits: switchings (Lemma 3.3(e) and Lemma 3.4)

For a switching `s` of `T(a)` the numbers `A_b`, `S_b` are integers, so off `B` we have
`G_s(θ) ∏_{b∈B}(θ² - b) = g(θ)` with `g ∈ ℚ[x]`; if `G_s` vanishes at one root of an orbit
factor `f`, then `f ∣ g` and `G_s` vanishes at every root of `f` (Lemma 3.3(e)). If all
`σ_i = σ`, then `S_b = σ k_b` and `F(t) = 1` give `G_s(θ) = σθ + P_s(t)` with `P_s(t) ∈ ℚ(t)`,
and Lemma 3.4 follows from Lemma 3.3(a), (b), (e).
-/

set_option autoImplicit false

open Polynomial BackfillPaper8 BackfillPaper8.Challenge

namespace P8Orb

noncomputable section

section Switch

variable {k : ℕ} (a : Fin k → ℕ)

theorem card_Ib (b : ℕ) : (Ib a b).card = kb (branchMS a) b := by
  rw [kb, branchMS, Multiset.count_map, Ib, Finset.card_def, Finset.filter_val]
  congr 1
  exact Multiset.filter_congr (fun _ _ => eq_comm)

theorem switching_int {s : TV a → ℝ} (hs : IsSwitching s) :
    ∃ s' : TV a → ℤ, ∀ v, s v = s' v := by
  have hne : (-1 : ℝ) ≠ 1 := by norm_num
  refine ⟨fun v => if s v = 1 then 1 else -1, fun v => ?_⟩
  rcases hs v with h | h
  · simp [h]
  · simp [h, hne]

theorem Ab_int {s : TV a → ℝ} (hs : IsSwitching s) (b : ℕ) : ∃ z : ℤ, Ab a s b = z := by
  obtain ⟨s', hs'⟩ := switching_int a hs
  refine ⟨s' none * kb (branchMS a) b + ∑ i ∈ Ib a b, ∑ j, s' (some ⟨i, some j⟩), ?_⟩
  simp only [Challenge.Ab, sc, Lamb, lam, hs']
  push_cast
  ring

theorem Sb_int {s : TV a → ℝ} (hs : IsSwitching s) (b : ℕ) : ∃ z : ℤ, Sb a s b = z := by
  obtain ⟨s', hs'⟩ := switching_int a hs
  refine ⟨∑ i ∈ Ib a b, s' (some ⟨i, none⟩), ?_⟩
  simp only [Sb, sig, hs']
  push_cast
  ring

/-- `G_s(θ) ∏_{b∈B}(θ² - b) = ∑_{b∈B} (A_b + S_b θ) ∏_{b'≠b}(θ² - b')` off `B`. -/
theorem Gs_mul_prod (s : TV a → ℝ) (θ : ℝ)
    (hθ : ∀ b ∈ Bset (branchMS a), θ ^ 2 ≠ (b : ℝ)) :
    Gs a s θ * ∏ b ∈ Bset (branchMS a), (θ ^ 2 - (b : ℝ)) =
      ∑ b ∈ Bset (branchMS a), (Ab a s b + Sb a s b * θ) *
        ∏ b' ∈ (Bset (branchMS a)).erase b, (θ ^ 2 - (b' : ℝ)) := by
  unfold Gs
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl (fun b hb => ?_)
  rw [← Finset.mul_prod_erase _ _ hb]
  have h : θ ^ 2 - (b : ℝ) ≠ 0 := sub_ne_zero.2 (hθ b hb)
  field_simp

end Switch

/-- The numerator of `G_s`, with rational coefficients `qA b`, `qS b`. -/
def gPoly (m : Multiset ℕ) (qA qS : ℕ → ℚ) : ℚ[X] :=
  ∑ b ∈ Bset m, (C (qA b) + C (qS b) * X) * ∏ b' ∈ (Bset m).erase b, (X ^ 2 - C (b' : ℚ))

theorem aeval_gPoly (m : Multiset ℕ) (qA qS : ℕ → ℚ) (θ : ℝ) :
    aeval θ (gPoly m qA qS) = ∑ b ∈ Bset m, ((qA b : ℝ) + (qS b : ℝ) * θ) *
      ∏ b' ∈ (Bset m).erase b, (θ ^ 2 - (b' : ℝ)) := by
  simp [gPoly, map_sum, map_prod]

section Switch2

variable {k : ℕ} (a : Fin k → ℕ)

/-- Lemma 3.3(e): if `G_s` vanishes at a root of an orbit factor `f`, it vanishes at every root
of `f`. -/
theorem Gs_eq_zero_of_root {s : TV a → ℝ} (hs : IsSwitching s) {f : ℚ[X]}
    (hf : IsOrbitFactor (branchMS a) f) {θ θ' : ℝ} (hθ : aeval θ f = 0) (hθ' : aeval θ' f = 0)
    (hG : Gs a s θ = 0) : Gs a s θ' = 0 := by
  choose qA hqA using Ab_int a hs
  choose qS hqS using Sb_int a hs
  have hne : ∀ x : ℝ, aeval x f = 0 → ∀ b ∈ Bset (branchMS a), x ^ 2 ≠ (b : ℝ) :=
    fun x hx => ne_of_aeval_secular_eq_zero _ (isSecular_of_root hf hx)
  have key : ∀ x : ℝ, aeval x f = 0 →
      Gs a s x * ∏ b ∈ Bset (branchMS a), (x ^ 2 - (b : ℝ)) =
        aeval x (gPoly (branchMS a) (fun b => (qA b : ℚ)) (fun b => (qS b : ℚ))) := by
    intro x hx
    rw [Gs_mul_prod a s x (hne x hx), aeval_gPoly]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    rw [hqA b, hqS b]
    push_cast
    ring
  have h1 : aeval θ (gPoly (branchMS a) (fun b => (qA b : ℚ)) (fun b => (qS b : ℚ))) = 0 := by
    rw [← key θ hθ, hG, zero_mul]
  have hfmin : f = minpoly ℚ θ := minpoly.eq_of_irreducible_of_monic hf.2.1 hθ hf.1
  obtain ⟨g, hg⟩ := hfmin ▸ minpoly.dvd ℚ θ h1
  have h3 : aeval θ' (gPoly (branchMS a) (fun b => (qA b : ℚ)) (fun b => (qS b : ℚ))) = 0 := by
    rw [hg, map_mul, hθ', zero_mul]
  rw [← key θ' hθ'] at h3
  rcases mul_eq_zero.1 h3 with h4 | h4
  · exact h4
  · exfalso
    obtain ⟨b, hb, hb0⟩ := Finset.prod_eq_zero_iff.1 h4
    exact hne θ' hθ' b hb (sub_eq_zero.1 hb0)

/-- Lemma 3.4, first part: with all `σ_i = σ`, `G_s(θ) = σθ + P_s(θ²)` at secular `θ`. -/
theorem Gs_eq_of_sig {s : TV a → ℝ} {σ : ℝ} (hσ : ∀ i, sig a s i = σ) {θ : ℝ}
    (hθ : IsSecular (branchMS a) θ) : Gs a s θ = σ * θ + Ps a s (θ ^ 2) := by
  have hF := sum_kb_div_eq_one (branchMS a) hθ
  have hSb : ∀ b, Sb a s b = (kb (branchMS a) b : ℝ) * σ := by
    intro b
    simp only [Sb, hσ, Finset.sum_const, nsmul_eq_mul, card_Ib]
  unfold Gs Ps
  simp only [hSb, add_div, Finset.sum_add_distrib]
  rw [add_comm]
  congr 1
  calc ∑ b ∈ Bset (branchMS a), (kb (branchMS a) b : ℝ) * σ * θ / (θ ^ 2 - (b : ℝ))
      = σ * θ * ∑ b ∈ Bset (branchMS a), (kb (branchMS a) b : ℝ) / (θ ^ 2 - (b : ℝ)) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun b _ => by ring)
    _ = σ * θ := by rw [hF, mul_one]

theorem Ps_mem {s : TV a → ℝ} (hs : IsSwitching s) (t : ℝ) : Ps a s t ∈ QAdj t := by
  unfold Ps
  refine IntermediateField.sum_mem _ (fun b _ => ?_)
  obtain ⟨z, hz⟩ := Ab_int a hs b
  rw [hz]
  exact div_mem (intCast_mem _ z)
    (sub_mem (IntermediateField.mem_adjoin_simple_self ℚ t) (natCast_mem _ b))

end Switch2

end

end P8Orb
