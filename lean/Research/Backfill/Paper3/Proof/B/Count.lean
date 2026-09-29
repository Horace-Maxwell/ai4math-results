import Research.Backfill.Paper3.Proof.B.Switch

/-!
# Counting vertex sets of `S_d`

A vertex set of `K_{d,d}` or `S_d` is a pair `(S, T)` of subsets of the two sides. From the
2-switch identity, `e_{S_d}(S ⊔ T) + [a₁ ∈ S ∧ b₁ ∈ T] + [a₂ ∈ S ∧ b₂ ∈ T] =
|S||T| + [a₁, a₂ ∈ S] + [b₁, b₂ ∈ T]`. We characterise the sets with `e_{S_d} = 0` and the sets
with `e_{S_d} ≤ 1 < e_{K_{d,d}}` (the four families of the paper) and count both.
-/

set_option autoImplicit false

namespace P3B

open Finset SimpleGraph BackfillPaper3.Challenge

/-! ## Generic counting lemmas -/

/-- `N_{≤t}(G)` for a graph on `V ⊕ W` as a double sum over the two sides. -/
theorem iCount_eq_sum_sum {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    (G : SimpleGraph (V ⊕ W)) [DecidableRel G.Adj] (t : ℕ) :
    iCount G t = ∑ S : Finset V, ∑ T : Finset W,
      if edgesIn G (S.disjSum T) ≤ t then 1 else 0 := by
  rw [iCount, Finset.card_filter, ← Fintype.sum_prod_type']
  refine Fintype.sum_equiv (P3Basic.finsetSumEquiv V W) _ _ (fun A => ?_)
  simp only [P3Basic.finsetSumEquiv, Equiv.coe_fn_mk, Finset.toLeft_disjSum_toRight]

theorem ite_or4 {A B C D : Prop} [Decidable A] [Decidable B] [Decidable C] [Decidable D]
    [Decidable (A ∨ B ∨ C ∨ D)] (hAB : ¬ (A ∧ B)) (hAC : ¬ (A ∧ C)) (hAD : ¬ (A ∧ D))
    (hBC : ¬ (B ∧ C)) (hBD : ¬ (B ∧ D)) (hCD : ¬ (C ∧ D)) :
    (if A ∨ B ∨ C ∨ D then 1 else 0 : ℕ) =
      (if A then 1 else 0) + (if B then 1 else 0) + (if C then 1 else 0) + (if D then 1 else 0) := by
  by_cases hA : A <;> by_cases hB : B <;> by_cases hC : C <;> by_cases hD : D <;> simp_all

theorem sum_sum_ite_eq_and {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] (a : α)
    (Q : β → Prop) [DecidablePred Q] :
    (∑ x : α, ∑ y : β, if x = a ∧ Q y then 1 else 0 : ℕ) = #(univ.filter Q) := by
  rw [Finset.card_filter, Finset.sum_comm]
  refine Finset.sum_congr rfl fun y _ => ?_
  simp only [ite_and, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

theorem sum_sum_ite_and_eq {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β] (b : β)
    (R : α → Prop) [DecidablePred R] :
    (∑ x : α, ∑ y : β, if y = b ∧ R x then 1 else 0 : ℕ) = #(univ.filter R) := by
  rw [Finset.card_filter]
  refine Finset.sum_congr rfl fun x _ => ?_
  simp only [ite_and, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

theorem of_ite_eq_one {P : Prop} [Decidable P] (h : (if P then 1 else 0 : ℕ) = 1) : P := by
  by_contra hP
  rw [ite_eq_right hP] at h
  exact absurd h (by norm_num)

theorem not_of_ite_eq_zero {P : Prop} [Decidable P] (h : (if P then 1 else 0 : ℕ) = 0) : ¬ P := by
  intro hP
  rw [ite_eq_left hP] at h
  exact absurd h (by norm_num)

theorem ite_le_one (P : Prop) [Decidable P] : (if P then 1 else 0 : ℕ) ≤ 1 := by
  split_ifs <;> omega

theorem mul_eq_two_cases {s t : ℕ} (h : s * t = 2) : (s = 1 ∧ t = 2) ∨ (s = 2 ∧ t = 1) := by
  have hs : s ≤ 2 := by
    rcases Nat.eq_zero_or_pos t with ht | ht
    · rw [ht, Nat.mul_zero] at h
      omega
    · nlinarith
  interval_cases s <;> omega

theorem mul_eq_one_cases {s t : ℕ} (h : s * t = 1) : s = 1 ∧ t = 1 := by
  have hs : s ≤ 1 := by
    rcases Nat.eq_zero_or_pos t with ht | ht
    · rw [ht, Nat.mul_zero] at h
      omega
    · nlinarith
  interval_cases s <;> omega

theorem eq_singleton_of_card_one {α : Type*} {s : Finset α} {a : α} (h : #s = 1) (ha : a ∈ s) :
    s = {a} := by
  obtain ⟨x, rfl⟩ := Finset.card_eq_one.mp h
  rw [Finset.mem_singleton] at ha
  rw [ha]

/-! ## Subsets of `Fin d` -/

section FinCounts

variable {d : ℕ}

theorem card_filter_card_eq_one (d : ℕ) :
    #(univ.filter fun S : Finset (Fin d) => #S = 1) = d := by
  have h : (univ.filter fun S : Finset (Fin d) => #S = 1) = Finset.powersetCard 1 univ := by
    ext S
    simp [Finset.mem_powersetCard]
  rw [h, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin, Nat.choose_one_right]

/-- `#{T : p ∈ T, q ∉ T, |T| = 2} = d - 2`. -/
theorem card_filter_pair {p q : Fin d} (hpq : p ≠ q) :
    #(univ.filter fun T : Finset (Fin d) => p ∈ T ∧ q ∉ T ∧ #T = 2) = d - 2 := by
  have himg : (univ.filter fun T : Finset (Fin d) => p ∈ T ∧ q ∉ T ∧ #T = 2) =
      ((univ.erase p).erase q).image fun j => ({p, j} : Finset (Fin d)) := by
    ext T
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image,
      Finset.mem_erase, ne_eq, and_true]
    constructor
    · rintro ⟨hp, hq, hT⟩
      obtain ⟨x, y, hxy, rfl⟩ := Finset.card_eq_two.mp hT
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hp hq
      rcases hp with rfl | rfl
      · exact ⟨y, ⟨fun h => hq.2 h.symm, fun h => hxy h.symm⟩, rfl⟩
      · exact ⟨x, ⟨fun h => hq.1 h.symm, hxy⟩, Finset.pair_comm _ _⟩
    · rintro ⟨j, ⟨hjq, hjp⟩, rfl⟩
      refine ⟨Finset.mem_insert_self _ _, ?_, Finset.card_pair (Ne.symm hjp)⟩
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨Ne.symm hpq, fun h => hjq h.symm⟩
  rw [himg, Finset.card_image_of_injOn]
  · rw [Finset.card_erase_of_mem, Finset.card_erase_of_mem (Finset.mem_univ p), Finset.card_univ,
      Fintype.card_fin]
    · omega
    · simp [Ne.symm hpq]
  · intro i hi j hj hij
    simp only [Finset.coe_erase, Set.mem_sdiff, Set.mem_singleton_iff, Finset.coe_univ,
      Set.mem_univ, true_and] at hi hj
    have hi' : i ∈ ({p, j} : Finset (Fin d)) := by
      rw [← show ({p, i} : Finset (Fin d)) = {p, j} from hij]
      exact Finset.mem_insert_of_mem (Finset.mem_singleton_self i)
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi'
    rcases hi' with h | h
    · exact absurd h hi.1
    · exact h

/-- `#{S : a, b ∈ S} = 2^{d-2}` for `a ≠ b`. -/
theorem card_filter_mem_mem {a b : Fin d} (hab : a ≠ b) :
    #(univ.filter fun S : Finset (Fin d) => a ∈ S ∧ b ∈ S) = 2 ^ (d - 2) := by
  have h : (univ.filter fun S : Finset (Fin d) => a ∈ S ∧ b ∈ S) = Finset.Icc {a, b} univ := by
    ext S
    simp [Finset.insert_subset_iff]
  rw [h, Finset.card_Icc_finset (Finset.subset_univ _), Finset.card_univ, Fintype.card_fin,
    Finset.card_pair hab]

/-- `#{S : ¬ (a, b ∈ S)} = 2^d - 2^{d-2}` for `a ≠ b`. -/
theorem card_filter_not_mem_mem {a b : Fin d} (hab : a ≠ b) :
    #(univ.filter fun S : Finset (Fin d) => ¬ (a ∈ S ∧ b ∈ S)) = 2 ^ d - 2 ^ (d - 2) := by
  have h := Finset.card_filter_add_card_filter_not (s := (univ : Finset (Finset (Fin d))))
    (fun S => a ∈ S ∧ b ∈ S)
  rw [card_filter_mem_mem hab, Finset.card_univ, Fintype.card_finset, Fintype.card_fin] at h
  omega

theorem two_le_card_of_mem {α : Type*} [DecidableEq α] {s : Finset α} {a b : α} (hab : a ≠ b)
    (ha : a ∈ s) (hb : b ∈ s) : 2 ≤ #s := by
  have hsub : ({a, b} : Finset α) ⊆ s := by
    intro x hx
    rw [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact ha
    · exact hb
  have h2 := Finset.card_le_card hsub
  rwa [Finset.card_pair hab] at h2

end FinCounts

/-! ## The edge count of `S_d` -/

section Sd

variable {d : ℕ} {a₁ a₂ b₁ b₂ : Fin d}

theorem sd_valid (ha : a₁ ≠ a₂) (hb : b₁ ≠ b₂) :
    ValidSwitch (Kdd d) (.inl a₁) (.inr b₁) (.inr b₂) (.inl a₂) where
  adj₁ := by simp
  adj₂ := by simp
  nadj₁ := by simp
  nadj₂ := by simp
  ne₁ := by simpa using ha
  ne₂ := by simpa using hb.symm

/-- `e_{S_d}(S ⊔ T) + [a₁ ∈ S ∧ b₁ ∈ T] + [a₂ ∈ S ∧ b₂ ∈ T] = |S||T| + [a₁, a₂ ∈ S] + [b₁, b₂ ∈ T]`. -/
theorem sd_edges (ha : a₁ ≠ a₂) (hb : b₁ ≠ b₂) (S T : Finset (Fin d)) :
    edgesIn (Sd d a₁ a₂ b₁ b₂) (S.disjSum T) + (if a₁ ∈ S ∧ b₁ ∈ T then 1 else 0) +
        (if a₂ ∈ S ∧ b₂ ∈ T then 1 else 0) =
      #S * #T + (if a₁ ∈ S ∧ a₂ ∈ S then 1 else 0) + (if b₁ ∈ T ∧ b₂ ∈ T then 1 else 0) := by
  have h := (sd_valid ha hb).edgesIn_eq (S.disjSum T)
  rw [P3Basic.edgesIn_Kdd] at h
  simp only [Finset.inl_mem_disjSum, Finset.inr_mem_disjSum] at h
  have e1 : (if b₂ ∈ T ∧ a₂ ∈ S then 1 else 0 : ℕ) = if a₂ ∈ S ∧ b₂ ∈ T then 1 else 0 := by
    simp only [and_comm]
  have e2 : (if b₂ ∈ T ∧ b₁ ∈ T then 1 else 0 : ℕ) = if b₁ ∈ T ∧ b₂ ∈ T then 1 else 0 := by
    simp only [and_comm]
  rw [e1, e2] at h
  exact h

/-- Linear facts about the four indicators. -/
theorem sd_facts (ha : a₁ ≠ a₂) (hb : b₁ ≠ b₂) (S T : Finset (Fin d)) :
    2 * (if a₁ ∈ S ∧ a₂ ∈ S then 1 else 0) ≤ #S ∧
    2 * (if b₁ ∈ T ∧ b₂ ∈ T then 1 else 0) ≤ #T ∧
    (if a₁ ∈ S ∧ b₁ ∈ T then 1 else 0) ≤ #S ∧ (if a₁ ∈ S ∧ b₁ ∈ T then 1 else 0) ≤ #T ∧
    (if a₂ ∈ S ∧ b₂ ∈ T then 1 else 0) ≤ #S ∧ (if a₂ ∈ S ∧ b₂ ∈ T then 1 else 0) ≤ #T ∧
    (if a₁ ∈ S ∧ b₁ ∈ T then 1 else 0) + (if a₂ ∈ S ∧ b₂ ∈ T then 1 else 0) ≤
      1 + (if a₁ ∈ S ∧ a₂ ∈ S then 1 else 0) ∧
    (if a₁ ∈ S ∧ b₁ ∈ T then 1 else 0) + (if a₂ ∈ S ∧ b₂ ∈ T then 1 else 0) ≤
      1 + (if b₁ ∈ T ∧ b₂ ∈ T then 1 else 0) ∧
    (if a₁ ∈ S ∧ a₂ ∈ S then 1 else 0) ≤ 1 ∧ (if b₁ ∈ T ∧ b₂ ∈ T then 1 else 0) ≤ 1 := by
  have pS : ∀ a ∈ S, 1 ≤ #S := fun a h => Finset.card_pos.mpr ⟨a, h⟩
  have pT : ∀ b ∈ T, 1 ≤ #T := fun b h => Finset.card_pos.mpr ⟨b, h⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ite_le_one _, ite_le_one _⟩
  · split_ifs with h
    · exact two_le_card_of_mem ha h.1 h.2
    · omega
  · split_ifs with h
    · exact two_le_card_of_mem hb h.1 h.2
    · omega
  · split_ifs with h
    · exact pS _ h.1
    · omega
  · split_ifs with h
    · exact pT _ h.2
    · omega
  · split_ifs with h
    · exact pS _ h.1
    · omega
  · split_ifs with h
    · exact pT _ h.2
    · omega
  · split_ifs <;> simp_all
  · split_ifs <;> simp_all

/-- Every set spanning at most one edge of `K_{d,d}` spans at most one edge of `S_d`. -/
theorem sd_le_one_of_kdd (ha : a₁ ≠ a₂) (hb : b₁ ≠ b₂) (S T : Finset (Fin d))
    (h : #S * #T ≤ 1) : edgesIn (Sd d a₁ a₂ b₁ b₂) (S.disjSum T) ≤ 1 := by
  have F := sd_edges ha hb S T
  obtain ⟨f1, f2, f3, f4, f5, f6, f7, f8, f9, f10⟩ := sd_facts ha hb S T
  rcases Nat.eq_zero_or_pos (#S) with hs | hs
  · rw [hs, Nat.zero_mul] at F
    omega
  rcases Nat.eq_zero_or_pos (#T) with ht | ht
  · rw [ht, Nat.mul_zero] at F
    omega
  have h1 : #S * #T = 1 := le_antisymm h (Nat.mul_pos hs ht)
  obtain ⟨hs1, ht1⟩ := mul_eq_one_cases h1
  rw [h1] at F
  omega

/-- The sets spanning at most one edge of `S_d` and at least two of `K_{d,d}`. -/
theorem sd_extra_iff (ha : a₁ ≠ a₂) (hb : b₁ ≠ b₂) (S T : Finset (Fin d)) :
    (edgesIn (Sd d a₁ a₂ b₁ b₂) (S.disjSum T) ≤ 1 ∧ ¬ #S * #T ≤ 1) ↔
      (S = {a₁} ∧ b₁ ∈ T ∧ b₂ ∉ T ∧ #T = 2) ∨ (S = {a₂} ∧ b₂ ∈ T ∧ b₁ ∉ T ∧ #T = 2) ∨
        (T = {b₁} ∧ a₁ ∈ S ∧ a₂ ∉ S ∧ #S = 2) ∨ (T = {b₂} ∧ a₂ ∈ S ∧ a₁ ∉ S ∧ #S = 2) := by
  have F := sd_edges ha hb S T
  obtain ⟨f1, f2, f3, f4, f5, f6, f7, f8, f9, f10⟩ := sd_facts ha hb S T
  constructor
  · rintro ⟨he, hst⟩
    have key : #S * #T = 2 ∧ (if a₁ ∈ S ∧ a₂ ∈ S then 1 else 0) = 0 ∧
        (if b₁ ∈ T ∧ b₂ ∈ T then 1 else 0) = 0 ∧
        ((if a₁ ∈ S ∧ b₁ ∈ T then 1 else 0) = 1 ∨ (if a₂ ∈ S ∧ b₂ ∈ T then 1 else 0) = 1) := by
      omega
    obtain ⟨hst2, hτ₁, hτ₂, hσ | hσ⟩ := key
    · obtain ⟨h1, h3⟩ := of_ite_eq_one hσ
      have h2 : a₂ ∉ S := fun h2 => not_of_ite_eq_zero hτ₁ ⟨h1, h2⟩
      have h4 : b₂ ∉ T := fun h4 => not_of_ite_eq_zero hτ₂ ⟨h3, h4⟩
      rcases mul_eq_two_cases hst2 with ⟨hs, ht⟩ | ⟨hs, ht⟩
      · exact Or.inl ⟨eq_singleton_of_card_one hs h1, h3, h4, ht⟩
      · exact Or.inr (Or.inr (Or.inl ⟨eq_singleton_of_card_one ht h3, h1, h2, hs⟩))
    · obtain ⟨h2, h4⟩ := of_ite_eq_one hσ
      have h1 : a₁ ∉ S := fun h1 => not_of_ite_eq_zero hτ₁ ⟨h1, h2⟩
      have h3 : b₁ ∉ T := fun h3 => not_of_ite_eq_zero hτ₂ ⟨h3, h4⟩
      rcases mul_eq_two_cases hst2 with ⟨hs, ht⟩ | ⟨hs, ht⟩
      · exact Or.inr (Or.inl ⟨eq_singleton_of_card_one hs h2, h4, h3, ht⟩)
      · exact Or.inr (Or.inr (Or.inr ⟨eq_singleton_of_card_one ht h4, h2, h1, hs⟩))
  · rintro (⟨rfl, h3, h4, ht⟩ | ⟨rfl, h4, h3, ht⟩ | ⟨rfl, h1, h2, hs⟩ | ⟨rfl, h2, h1, hs⟩)
    · simp only [Finset.mem_singleton, Finset.card_singleton, ht, h3, h4, ha.symm, and_true,
        and_false, ite_true, ite_false] at F ⊢
      omega
    · simp only [Finset.mem_singleton, Finset.card_singleton, ht, h3, h4, ha, and_true,
        and_false, ite_true, ite_false] at F ⊢
      omega
    · simp only [Finset.mem_singleton, Finset.card_singleton, hs, h1, h2, hb.symm, and_true,
        and_false, ite_true, ite_false] at F ⊢
      omega
    · simp only [Finset.mem_singleton, Finset.card_singleton, hs, h1, h2, hb, and_true,
        and_false, ite_true, ite_false] at F ⊢
      omega

/-- The independent sets of `S_d`. -/
theorem sd_indep_iff (ha : a₁ ≠ a₂) (hb : b₁ ≠ b₂) (S T : Finset (Fin d)) :
    edgesIn (Sd d a₁ a₂ b₁ b₂) (S.disjSum T) ≤ 0 ↔
      (T = ∅ ∧ ¬ (a₁ ∈ S ∧ a₂ ∈ S)) ∨ (S = ∅ ∧ (T ≠ ∅ ∧ ¬ (b₁ ∈ T ∧ b₂ ∈ T))) ∨
        (S = {a₁} ∧ T = {b₁}) ∨ (S = {a₂} ∧ T = {b₂}) := by
  have F := sd_edges ha hb S T
  obtain ⟨f1, f2, f3, f4, f5, f6, f7, f8, f9, f10⟩ := sd_facts ha hb S T
  constructor
  · intro he
    by_cases hT : T = ∅
    · subst hT
      simp only [Finset.notMem_empty, and_false, ite_false, Finset.card_empty, Nat.mul_zero,
        add_zero, zero_add] at F
      refine Or.inl ⟨rfl, fun h => ?_⟩
      rw [ite_eq_left h] at F
      omega
    by_cases hS : S = ∅
    · subst hS
      simp only [Finset.notMem_empty, false_and, ite_false, Finset.card_empty, Nat.zero_mul,
        add_zero, zero_add] at F
      refine Or.inr (Or.inl ⟨rfl, hT, fun h => ?_⟩)
      rw [ite_eq_left h] at F
      omega
    have hs : 1 ≤ #S := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hS)
    have ht : 1 ≤ #T := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hT)
    have hst : 1 ≤ #S * #T := Nat.mul_pos hs ht
    have key : #S * #T = 1 ∧ (if a₁ ∈ S ∧ a₂ ∈ S then 1 else 0) = 0 ∧
        (if b₁ ∈ T ∧ b₂ ∈ T then 1 else 0) = 0 ∧
        ((if a₁ ∈ S ∧ b₁ ∈ T then 1 else 0) = 1 ∨ (if a₂ ∈ S ∧ b₂ ∈ T then 1 else 0) = 1) := by
      omega
    obtain ⟨hst1, -, -, hσ | hσ⟩ := key
    · obtain ⟨h1, h3⟩ := of_ite_eq_one hσ
      obtain ⟨hs1, ht1⟩ := mul_eq_one_cases hst1
      exact Or.inr (Or.inr (Or.inl ⟨eq_singleton_of_card_one hs1 h1,
        eq_singleton_of_card_one ht1 h3⟩))
    · obtain ⟨h2, h4⟩ := of_ite_eq_one hσ
      obtain ⟨hs1, ht1⟩ := mul_eq_one_cases hst1
      exact Or.inr (Or.inr (Or.inr ⟨eq_singleton_of_card_one hs1 h2,
        eq_singleton_of_card_one ht1 h4⟩))
  · rintro (⟨rfl, h⟩ | ⟨rfl, -, h⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · rw [ite_eq_right h, Finset.card_empty, Nat.mul_zero] at F
      simp only [Finset.notMem_empty, and_false, ite_false] at F
      omega
    · rw [ite_eq_right h, Finset.card_empty, Nat.zero_mul] at F
      simp only [Finset.notMem_empty, false_and, ite_false] at F
      omega
    · simp only [Finset.mem_singleton, Finset.card_singleton, ha.symm, hb.symm, and_true,
        and_false, ite_true, ite_false] at F
      omega
    · simp only [Finset.mem_singleton, Finset.card_singleton, ha, hb, and_true,
        and_false, ite_true, ite_false] at F
      omega

end Sd

end P3B
