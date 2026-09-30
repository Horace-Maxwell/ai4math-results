import Research.Backfill.Paper8.Proof.Rows.Secular

/-!
# Paper 8, rows: the value of `G` on the two rows (equations (4.1) and (4.2))

`G_s(θ) = s_c F(t) + ∑_b Λ_b/(t - b) + θ ∑_b S_b/(t - b)` with `F(t) = 1` at a secular `θ`
(`P8Rows.F_eq_one_of_isSecular`); `Λ_0 = 0`. For the leaf row `S_b = k_b` and the leaf sums are
the standard ones except on `I_β`; for the bare row `S_0 = k_0 - 2m`. Also: the constants of
these formulas lie in `ℚ(t)`.
-/

set_option autoImplicit false

open BackfillPaper8.Challenge

namespace P8Rows

variable {k : ℕ} (a : Fin k → ℕ)

theorem Gs_eq (s : TV a → ℝ) (θ : ℝ) :
    Gs a s θ = sc a s * ∑ b ∈ Bset (branchMS a), (kb (branchMS a) b : ℝ) / (θ ^ 2 - b) +
      ∑ b ∈ Bset (branchMS a), Lamb a s b / (θ ^ 2 - b) +
      θ * ∑ b ∈ Bset (branchMS a), Sb a s b / (θ ^ 2 - b) := by
  unfold Gs BackfillPaper8.Challenge.Ab
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  ring

theorem lam_bare (s : TV a → ℝ) (i : Fin k) (hi : a i = 0) : lam a s i = 0 := by
  unfold lam
  exact Finset.sum_eq_zero (fun j _ => absurd j.isLt (by omega))

theorem Lamb_zero (s : TV a → ℝ) : Lamb a s 0 = 0 := by
  unfold Lamb
  exact Finset.sum_eq_zero (fun i hi => lam_bare a s i ((mem_Ib a 0 i).1 hi))

theorem sum_Lamb_filter (s : TV a → ℝ) (t : ℝ) :
    ∑ b ∈ Bset (branchMS a), Lamb a s b / (t - b) =
      ∑ b ∈ (Bset (branchMS a)).filter (fun b => 1 ≤ b), Lamb a s b / (t - b) := by
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  split_ifs with h
  · rfl
  · have : b = 0 := by omega
    subst this
    rw [Lamb_zero, zero_div]

theorem Lamb_std (s : TV a → ℝ) (b : ℕ) (hs : ∀ i, a i = b → lam a s i = (lamStd a i : ℝ)) :
    Lamb a s b = (LamStdB a b : ℝ) := by
  unfold Lamb LamStdB
  push_cast
  exact Finset.sum_congr rfl (fun i hi => hs i ((mem_Ib a b i).1 hi))

theorem Sb_of_sig_one (s : TV a → ℝ) (b : ℕ) (hs : ∀ i, a i = b → sig a s i = 1) :
    Sb a s b = kb (branchMS a) b := by
  unfold Sb
  rw [Finset.sum_congr rfl (fun i hi => hs i ((mem_Ib a b i).1 hi)), Finset.sum_const,
    card_Ib]
  simp

/-- Equation (4.1): the value of `G` on a member of the leaf row of `β`. -/
theorem Gs_leaf (β : ℕ) (hβ : β ∈ Bset (branchMS a)) (hβ1 : 1 ≤ β) (ε Λ : ℤ)
    (s : TV a → ℝ) (hs : IsLeafRowMember a β ε Λ s) (θ : ℝ)
    (hθ : IsSecular (branchMS a) θ) :
    Gs a s θ = θ + ε + Ubeta a β (θ ^ 2) + Λ / (θ ^ 2 - β) := by
  classical
  obtain ⟨-, hsc, hsig, hlam, hΛ, -, -⟩ := hs
  have hF := F_eq_one_of_isSecular _ hθ
  have hS : ∀ b, Sb a s b = kb (branchMS a) b := fun b => Sb_of_sig_one a s b (fun i _ => hsig i)
  rw [Gs_eq, hsc]
  simp_rw [hS]
  rw [hF, sum_Lamb_filter]
  set B' := (Bset (branchMS a)).filter (fun b => 1 ≤ b) with hB'
  have hβ' : β ∈ B' := Finset.mem_filter.2 ⟨hβ, hβ1⟩
  unfold Ubeta Ufun
  rw [← hB', ← Finset.add_sum_erase B' _ hβ', ← Finset.add_sum_erase B' _ hβ']
  have hrest : ∑ b ∈ B'.erase β, Lamb a s b / (θ ^ 2 - b) =
      ∑ b ∈ B'.erase β, (LamStdB a b : ℝ) / (θ ^ 2 - b) := by
    refine Finset.sum_congr rfl (fun b hb => ?_)
    obtain ⟨hbβ, hbB'⟩ := Finset.mem_erase.1 hb
    have hb1 : 1 ≤ b := (Finset.mem_filter.1 hbB').2
    rw [Lamb_std a s b (fun i hi => hlam i (by omega) (by omega))]
  have hLβ : Lamb a s β = Λ := hΛ
  rw [hrest, hLβ]
  ring

theorem Sb_zero_bare (ε : ℤ) (mm : ℕ) (s : TV a → ℝ) (hs : IsBareRowMember a ε mm s) :
    Sb a s 0 = kb (branchMS a) 0 - 2 * mm := by
  classical
  obtain ⟨hsw, -, -, hcard⟩ := hs
  unfold Sb
  have h1 : ∀ i ∈ Ib a 0, sig a s i = if sig a s i = -1 then -1 else 1 := by
    intro i _
    rcases hsw (some ⟨i, none⟩) with h | h
    · have h' : sig a s i = 1 := h
      rw [h']
      norm_num
    · have h' : sig a s i = -1 := h
      rw [h']
      norm_num
  rw [Finset.sum_congr rfl h1, Finset.sum_ite, Finset.sum_const, Finset.sum_const, hcard]
  have := Finset.card_filter_add_card_filter_not (s := Ib a 0) (fun i => sig a s i = -1)
  rw [hcard, card_Ib] at this
  rw [← this]
  push_cast
  ring

/-- Equation (4.2): the value of `G` on a member of the bare row. -/
theorem Gs_bare (h0 : 1 ≤ kb (branchMS a) 0) (ε : ℤ) (mm : ℕ) (s : TV a → ℝ)
    (hs : IsBareRowMember a ε mm s) (θ : ℝ) (hθ : IsSecular (branchMS a) θ) :
    Gs a s θ = ε + Ufun a (θ ^ 2) + θ - 2 * (mm : ℝ) / θ := by
  classical
  have h0B : 0 ∈ Bset (branchMS a) := by
    unfold Bset
    rw [Multiset.mem_toFinset]
    exact Multiset.count_pos.1 h0
  have hθ0 : θ ≠ 0 := ne_zero_of_isSecular _ hθ h0B
  have hF := F_eq_one_of_isSecular _ hθ
  have hS0 := Sb_zero_bare a ε mm s hs
  obtain ⟨-, hsc, hstd, -⟩ := hs
  have hSsum : ∑ b ∈ Bset (branchMS a), Sb a s b / (θ ^ 2 - b) = 1 - 2 * mm / θ ^ 2 := by
    rw [← Finset.add_sum_erase _ _ h0B]
    rw [← Finset.add_sum_erase _ _ h0B] at hF
    have hrest : ∑ b ∈ (Bset (branchMS a)).erase 0, Sb a s b / (θ ^ 2 - b) =
        ∑ b ∈ (Bset (branchMS a)).erase 0, (kb (branchMS a) b : ℝ) / (θ ^ 2 - b) := by
      refine Finset.sum_congr rfl (fun b hb => ?_)
      have hb0 : b ≠ 0 := (Finset.mem_erase.1 hb).1
      rw [Sb_of_sig_one a s b (fun i hi => (hstd i (by omega)).1)]
    rw [hrest, hS0]
    rw [Nat.cast_zero, sub_zero] at hF ⊢
    have ht : θ ^ 2 ≠ 0 := pow_ne_zero 2 hθ0
    rw [sub_div]
    linarith
  have hLsum : ∑ b ∈ Bset (branchMS a), Lamb a s b / (θ ^ 2 - b) = Ufun a (θ ^ 2) := by
    rw [sum_Lamb_filter]
    unfold Ufun
    refine Finset.sum_congr rfl (fun b hb => ?_)
    have hb1 : 1 ≤ b := (Finset.mem_filter.1 hb).2
    rw [Lamb_std a s b (fun i hi => (hstd i (by omega)).2)]
  rw [Gs_eq, hsc, hF, hSsum, hLsum]
  field_simp
  ring

/-! ### Membership in `ℚ(t)` -/

theorem natCast_mem_QAdj (t : ℝ) (n : ℕ) : (n : ℝ) ∈ QAdj t := natCast_mem _ n

theorem intCast_mem_QAdj (t : ℝ) (n : ℤ) : (n : ℝ) ∈ QAdj t := intCast_mem _ n

theorem self_mem_QAdj (t : ℝ) : t ∈ QAdj t := IntermediateField.mem_adjoin_simple_self ℚ t

theorem Ufun_mem (t : ℝ) : Ufun a t ∈ QAdj t := by
  unfold Ufun
  exact sum_mem (fun b _ => div_mem (intCast_mem_QAdj t _)
    (sub_mem (self_mem_QAdj t) (natCast_mem_QAdj t b)))

theorem Ubeta_mem (β : ℕ) (t : ℝ) : Ubeta a β t ∈ QAdj t := by
  unfold Ubeta
  exact sub_mem (Ufun_mem a t) (div_mem (intCast_mem_QAdj t _)
    (sub_mem (self_mem_QAdj t) (natCast_mem_QAdj t β)))

end P8Rows
