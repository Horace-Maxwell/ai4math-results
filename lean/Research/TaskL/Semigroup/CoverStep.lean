import Research.TaskL.Semigroup.Foundations

namespace TaskL.Semigroup
open Challenge
noncomputable section
open Classical

variable {S Q P R : AddSubmonoid ℕ} {D E : Finset (AddSubmonoid ℕ)} {u v : ℕ}

theorem private_gap (hS : Numerical S) (hd : Decomposition S D) (hQ : Q ∈ D) :
    ∃ g, Special S g ∧ g ∉ Q ∧ ∀ A ∈ D, A ≠ Q → g ∈ A := by
  have h := (decomp_iff hS).mp hd
  have hn := h.2.2 _ (Finset.erase_ssubset hQ)
  unfold Cover at hn
  push Not at hn
  obtain ⟨g,hg,ha⟩ := hn
  obtain ⟨A,hA,hgA⟩ := h.2.1 g hg
  have he : A = Q := by
    by_contra hh
    exact hgA (ha A (Finset.mem_erase.mpr ⟨hh,hA⟩))
  exact ⟨g,hg,he ▸ hgA,fun B hb hne => ha B (Finset.mem_erase.mpr ⟨hne,hb⟩)⟩

def score (D : Finset (AddSubmonoid ℕ)) : ℕ := ∑ A ∈ D, 3 ^ gapWeight A

theorem score_mono (h : E ⊆ D) : score E ≤ score D := by
  exact Finset.sum_le_sum_of_subset_of_nonneg h (by intros; positivity)

theorem score_insert (P : AddSubmonoid ℕ) (D : Finset (AddSubmonoid ℕ)) :
    score (insert P D) ≤ 3^gapWeight P + score D := by
  by_cases hp : P ∈ D
  · rw [Finset.insert_eq_of_mem hp]; exact Nat.le_add_left _ _
  · simp [score,Finset.sum_insert hp]

theorem score_erase (hQ : Q ∈ D) : score (D.erase Q) + 3^gapWeight Q = score D :=
  Finset.sum_erase_add _ (fun A => 3^gapWeight A) hQ

private theorem small_pair {a b n : ℕ} (ha : a<n) (hb : b<n) : 3^a+3^b < 3^n := by
  cases n with
  | zero => omega
  | succ n =>
    have h1 := Nat.pow_le_pow_right (by decide : 0<3) (show a≤n by omega)
    have h2 := Nat.pow_le_pow_right (by decide : 0<3) (show b≤n by omega)
    have h3 : 0<3^n := by positivity
    rw [pow_succ]
    omega

/-- All omitted old components other than Q must have the same formerly private gap u. -/
theorem card_lower (hS : Numerical S) (hd : Decomposition S D) (hQ : Q∈D)
    (hc : Cover S E)
    (types : ∀ A∈E, A∈D.erase Q ∨ A=P ∨ Q≤A)
    (swap : ∀ n, n∈P ↔ n=v ∨ n∈Q ∧ n≠u) : D.card ≤ E.card+1 := by
  let T := D.erase Q
  have lost (A : AddSubmonoid ℕ) (hA : A ∈ T \ E) :
      u∉A ∧ ∀ B∈D, B≠A → u∈B := by
    obtain ⟨ha,haE⟩ := Finset.mem_sdiff.mp hA
    obtain ⟨hne,haD⟩ := Finset.mem_erase.mp ha
    obtain ⟨g,hg,hgA,unique⟩ := private_gap hS hd haD
    have hgQ := unique Q hQ hne.symm
    obtain ⟨Z,hZ,hgZ⟩ := hc g hg
    have hgu : g=u := by
      rcases types Z hZ with h | h | h
      · have hZA : Z ≠ A := fun e => haE (e ▸ hZ)
        exact (hgZ (unique Z (Finset.mem_erase.mp h).2 hZA)).elim
      · subst Z
        by_contra hu
        exact hgZ ((swap g).2 (.inr ⟨hgQ,hu⟩))
      · exact (hgZ (h hgQ)).elim
    subst g
    exact ⟨hgA,unique⟩
  have lone : (T \ E).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro a ha b hb
    by_contra hne
    exact (lost b hb).1 ((lost a ha).2 b (Finset.mem_erase.mp (Finset.mem_sdiff.mp hb).1).2 (Ne.symm hne))
  obtain ⟨g,hg,_,unique⟩ := private_gap hS hd hQ
  obtain ⟨Z,hZ,hgZ⟩ := hc g hg
  have hZT : Z ∉ T := fun e => hgZ (unique Z (Finset.mem_erase.mp e).2 (Finset.mem_erase.mp e).1)
  have hex : 0 < (E \ T).card := Finset.card_pos.mpr ⟨Z,Finset.mem_sdiff.mpr ⟨hZ,hZT⟩⟩
  have hi₁ : (T ∩ E).card ≤ T.card := Finset.card_le_card Finset.inter_subset_left
  have hi₂ : (T ∩ E).card ≤ E.card := Finset.card_le_card Finset.inter_subset_right
  rw [Finset.card_sdiff, Finset.inter_comm E T] at lone
  rw [Finset.card_sdiff] at hex
  have ht : T.card+1=D.card := Finset.card_erase_add_one hQ
  omega

/-- Move through a possibly redundant pool, then extract an irredundant subcover. -/
theorem rebalance (hS : Numerical S) (hd : Decomposition S D) (hQ : Q∈D)
    (hp : Irreducible P ∧ S≤P) (hw : gapWeight P<gapWeight Q)
    (swap : ∀ n, n∈P ↔ n=v ∨ n∈Q ∧ n≠u)
    (repair : ∃ R : AddSubmonoid ℕ, Irreducible R ∧ Q≤R ∧ v∉R ∧ gapWeight R<gapWeight Q) :
    ∃ E, Decomposition S E ∧ score E < score D ∧ D.card ≤ E.card+1 ∧ E.card ≤ D.card+1 := by
  let T := D.erase Q
  let N := insert P T
  have old := (decomp_iff hS).mp hd
  have hel : Eligible S N := by
    intro A hA
    rcases Finset.mem_insert.mp hA with rfl | ht
    · exact hp
    · exact old.1 _ (Finset.mem_erase.mp ht).2
  have one (g : ℕ) (hg : Special S g) (hne : g≠v) : ∃ A∈N, g∉A := by
    obtain ⟨A,hA,hm⟩ := old.2.1 g hg
    by_cases he : A=Q
    · subst A
      exact ⟨P,Finset.mem_insert_self _ _,fun h => ((swap g).mp h).elim hne (fun z => hm z.1)⟩
    · exact ⟨A,Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨he,hA⟩),hm⟩
  have nt : score N ≤ 3^gapWeight P + score T := score_insert P T
  have dt : score T+3^gapWeight Q=score D := score_erase hQ
  have ct : T.card+1=D.card := Finset.card_erase_add_one hQ
  have cn : N.card ≤ T.card+1 := Finset.card_insert_le _ _
  by_cases hc : Cover S N
  · obtain ⟨E,he,hdE⟩ := exists_minimal_subcover hS hel hc
    have bounded := score_mono he
    have lt := Nat.pow_lt_pow_right (by decide : 1<3) hw
    have lower := card_lower hS hd hQ ((decomp_iff hS).mp hdE).2.1 (P:=P) (fun A hA => by
      rcases Finset.mem_insert.mp (he hA) with h | h
      · exact .inr (.inl h)
      · exact .inl h) swap
    have cc := Finset.card_le_card he
    exact ⟨E,hdE,by omega,lower,by omega⟩
  · obtain ⟨R,hR,hQR,hv,hwR⟩ := repair
    let J := insert R N
    have hcJ : Cover S J := by
      intro g hg
      by_cases e : g=v
      · exact ⟨R,Finset.mem_insert_self _ _,e ▸ hv⟩
      · obtain ⟨A,hA,hm⟩ := one g hg e
        exact ⟨A,Finset.mem_insert_of_mem hA,hm⟩
    have elJ : Eligible S J := by
      intro A hA
      rcases Finset.mem_insert.mp hA with h | h
      · exact h ▸ ⟨hR,(old.1 Q hQ).2.trans hQR⟩
      · exact hel _ h
    obtain ⟨E,he,hdE⟩ := exists_minimal_subcover hS elJ hcJ
    have lower := card_lower hS hd hQ ((decomp_iff hS).mp hdE).2.1 (P:=P) (fun A hA => by
      rcases Finset.mem_insert.mp (he hA) with h | h
      · exact .inr (.inr (h ▸ hQR))
      · rcases Finset.mem_insert.mp h with z | z
        · exact .inr (.inl z)
        · exact .inl z) swap
    have bounded := score_mono he
    have js : score J ≤ 3^gapWeight R+score N := score_insert R N
    have lt := small_pair hw hwR
    have cj : J.card ≤ N.card+1 := Finset.card_insert_le _ _
    have cc := Finset.card_le_card he
    exact ⟨E,hdE,by omega,lower,by omega⟩

end
end TaskL.Semigroup
