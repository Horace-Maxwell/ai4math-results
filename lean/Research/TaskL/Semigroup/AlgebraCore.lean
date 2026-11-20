import Research.TaskL.Semigroup.Challenge

namespace TaskL.Semigroup
open Challenge
noncomputable section

variable {Q B S : AddSubmonoid ℕ} {f x : ℕ}

def IsFrob (Q : AddSubmonoid ℕ) (f : ℕ) : Prop :=
  f ∉ Q ∧ ∀ n > f, n ∈ Q

private def withTail (B : AddSubmonoid ℕ) (f : ℕ) : AddSubmonoid ℕ where
  carrier := {n | n ∈ B ∨ f < n}
  zero_mem' := Or.inl B.zero_mem
  add_mem' := by
    rintro a b (ha | ha) (hb | hb)
    · exact Or.inl (B.add_mem ha hb)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)

private theorem numerical_of_tail (Q : AddSubmonoid ℕ) (f : ℕ) (ht : ∀ n > f, n ∈ Q) :
    Numerical Q := by
  apply (Finset.range (f+1)).finite_toSet.subset
  intro n hn
  have hn' : n ∉ Q := hn
  simp only [Finset.mem_coe, Finset.mem_range]
  exact Nat.lt_succ_of_le (le_of_not_gt (fun h => hn' (ht n h)))

private def belowGaps (Q : AddSubmonoid ℕ) (f : ℕ) : Finset ℕ := by
  classical exact (Finset.range (f+1)).filter (fun n => n ∉ Q)

private theorem maximal_irreducible (hN : Numerical Q) (hf : f ∉ Q)
    (hmax : ∀ T : AddSubmonoid ℕ, Q ≤ T → f ∉ T → T ≤ Q) : Irreducible Q := by
  refine ⟨hN, ?_⟩
  intro A B _ _ hAB
  have ha : Q ≤ A := hAB ▸ inf_le_left
  have hb : Q ≤ B := hAB ▸ inf_le_right
  by_cases h : f ∈ A
  · have h' : f ∉ B := fun hB => hf (hAB ▸ show f ∈ A ⊓ B from ⟨h,hB⟩)
    exact Or.inr (le_antisymm hb (hmax B hb h'))
  · exact Or.inl (le_antisymm ha (hmax A ha h))

theorem exists_irreducible_avoiding {B : AddSubmonoid ℕ} {f : ℕ} (hf : f ∉ B) :
    ∃ R : AddSubmonoid ℕ, B ≤ R ∧ Irreducible R ∧ f ∉ R ∧ ∀ n > f, n ∈ R := by
  classical
  let good (Q : AddSubmonoid ℕ) := B ≤ Q ∧ IsFrob Q f
  have ex : ∃ k : ℕ, ∃ Q : AddSubmonoid ℕ, good Q ∧ (belowGaps Q f).card = k := by
    refine ⟨_, withTail B f, ⟨fun _ h => Or.inl h, ?_, fun _ h => Or.inr h⟩, rfl⟩
    rintro (h | h)
    · exact hf h
    · omega
  obtain ⟨R, ⟨hBR,hfR,hR⟩, hcard⟩ := Nat.find_spec ex
  refine ⟨R, hBR, maximal_irreducible (numerical_of_tail R f hR) hfR ?_, hfR, hR⟩
  intro T hRT hfT n hn
  by_contra hmiss
  have hsub : belowGaps T f ⊂ belowGaps R f := by
    apply Finset.ssubset_iff_subset_ne.mpr
    constructor
    · intro z hz
      simp only [belowGaps, Finset.mem_filter] at hz ⊢
      exact ⟨hz.1, fun h => hz.2 (hRT h)⟩
    · intro heq
      have hz : n ∈ belowGaps R f := by
        have hl : n ≤ f := le_of_not_gt (fun h => hmiss (hR n h))
        simp [belowGaps, hl, hmiss]
      rw [← heq] at hz
      exact (Finset.mem_filter.mp hz).2 hn
  have hmin := Nat.find_min' ex (show ∃ Q : AddSubmonoid ℕ, good Q ∧
      (belowGaps Q f).card = (belowGaps T f).card from
      ⟨T, ⟨le_trans hBR hRT, hfT, fun z hz => hRT (hR z hz)⟩, rfl⟩)
  have hlt := Finset.card_lt_card hsub
  omega

private theorem irreducible_maximal (hQ : Irreducible Q) (hF : IsFrob Q f)
    (T : AddSubmonoid ℕ) (hQT : Q ≤ T) (hfT : f ∉ T) : T ≤ Q := by
  have hfpos : 0 < f := Nat.pos_of_ne_zero (fun h => hF.1 (h ▸ Q.zero_mem))
  let U := withTail Q (f-1)
  have hfU : f ∈ U := Or.inr (by omega)
  have he : Q = U ⊓ T := by
    ext n
    constructor
    · intro hn
      exact ⟨Or.inl hn, hQT hn⟩
    · rintro ⟨hn, ht⟩
      rcases (show n ∈ Q ∨ f-1 < n from hn) with h | h
      · exact h
      · have hne : n ≠ f := fun e => hfT (e ▸ ht)
        exact hF.2 n (by omega)
  have hNU := numerical_of_tail U f (fun n h => Or.inr (by omega))
  have hNT := numerical_of_tail T f (fun n h => hQT (hF.2 n h))
  rcases hQ.2 U T hNU hNT he with e | e
  · exact False.elim (hF.1 (e ▸ hfU))
  · exact le_of_eq e.symm

private def withGenerator (Q : AddSubmonoid ℕ) (y : ℕ) : AddSubmonoid ℕ where
  carrier := {n | ∃ q ∈ Q, ∃ k : ℕ, n = q + k*y}
  zero_mem' := ⟨0, Q.zero_mem, 0, by simp⟩
  add_mem' := by
    rintro a b ⟨q,hq,k,rfl⟩ ⟨r,hr,t,rfl⟩
    exact ⟨q+r,Q.add_mem hq hr,k+t,by ring⟩

theorem complement_low (hQ : Irreducible Q) (hF : IsFrob Q f) (hx : 2*x < f) :
    f-x ∈ Q ↔ x ∉ Q := by
  constructor
  · intro hy hxQ
    have e : x+(f-x)=f := by omega
    exact hF.1 (e ▸ Q.add_mem hxQ hy)
  · intro hxQ
    let y := f-x
    let T := withGenerator Q y
    have hQT : Q ≤ T := fun n hn => ⟨n, hn, 0, by simp⟩
    have hyT : y ∈ T := ⟨0, Q.zero_mem, 1, by simp⟩
    apply irreducible_maximal hQ hF T hQT _ hyT
    rintro ⟨q,hq,k,he⟩
    rcases k with _ | k
    · simp only [Nat.zero_mul, Nat.add_zero] at he
      exact hF.1 (he ▸ hq)
    · rcases k with _ | k
      · simp only [Nat.zero_add, Nat.one_mul] at he
        exact hxQ ((show x=q by dsimp [y] at he; omega) ▸ hq)
      · have hle : 2*y ≤ (k+1+1)*y := Nat.mul_le_mul_right y (by omega)
        dsimp [y] at hle he
        omega

theorem irreducible_of_complement (hF : IsFrob Q f)
    (hc : ∀ n : ℕ, 2*n < f → (f-n ∈ Q ↔ n ∉ Q)) : Irreducible Q := by
  apply maximal_irreducible (numerical_of_tail Q f hF.2) hF.1
  intro T hQT hfT n hn
  by_contra hnQ
  have hle : n ≤ f := le_of_not_gt (fun h => hnQ (hF.2 n h))
  rcases lt_trichotomy (2*n) f with h | h | h
  · have ht := T.add_mem hn (hQT ((hc n h).2 hnQ))
    exact hfT ((show f=n+(f-n) by omega) ▸ ht)
  · exact hfT ((show f=n+n by omega) ▸ T.add_mem hn hn)
  · have hl : 2*(f-n) < f := by omega
    have hm : f-n ∈ Q := by
      by_contra hnm
      have ht := (hc (f-n) hl).2 hnm
      rw [show f-(f-n)=n by omega] at ht
      exact hnQ ht
    exact hfT ((show f=n+(f-n) by omega) ▸ T.add_mem hn (hQT hm))

end
end TaskL.Semigroup
