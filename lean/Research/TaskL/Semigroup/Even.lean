import Research.TaskL.Semigroup.Foundations
import Research.TaskL.Semigroup.AlgebraCore

namespace TaskL.Semigroup
open Challenge

variable {S : AddSubmonoid ℕ} {k m g f : ℕ}

private theorem multiple_mem (hs : m ∈ S) (hd : m ∣ g) : g ∈ S := by
  obtain ⟨t, rfl⟩ := hd
  simpa [nsmul_eq_mul, mul_comm] using S.nsmul_mem hs t

private theorem special_unique_residue (hm : m ∈ S) (hg : Special S g) (hf : Special S f)
    (hc : g % m = f % m) : g = f := by
  have aux : ∀ {a b : ℕ}, Special S a → Special S b → a % m = b % m → ¬ a < b := by
    intro a b ha hb he hlt
    have hd := (Nat.modEq_iff_dvd' hlt.le).mp he
    have hmem := ha.2.2 _ (multiple_mem hm hd) (by omega)
    exact hb.1 ((by omega : a + (b - a) = b) ▸ hmem)
  exact le_antisymm (le_of_not_gt (aux hf hg hc.symm)) (le_of_not_gt (aux hg hf hc))

/-- When twice a difference is in the semigroup, adjoining it has at most two cosets. -/
private def twoCosets (S : AddSubmonoid ℕ) (d : ℕ) (hd : d+d ∈ S) : AddSubmonoid ℕ where
  carrier := {x | x ∈ S ∨ ∃ a ∈ S, x = a+d}
  zero_mem' := Or.inl S.zero_mem
  add_mem' := by
    rintro x y (hx | ⟨a, ha, rfl⟩) (hy | ⟨b, hb, rfl⟩)
    · exact Or.inl (S.add_mem hx hy)
    · exact Or.inr ⟨_, S.add_mem hx hb, by omega⟩
    · exact Or.inr ⟨_, S.add_mem ha hy, by omega⟩
    · exact Or.inl ((show a+b+(d+d) = (a+d)+(b+d) by omega) ▸ S.add_mem (S.add_mem ha hb) hd)

private theorem pair_avoid_le (hg : g ∉ S) (hf : f ∉ S) (hgf : g ≤ f)
    (hd : (f-g)+(f-g) ∈ S) :
    ∃ Q : AddSubmonoid ℕ, S ≤ Q ∧ Irreducible Q ∧ g ∉ Q ∧ f ∉ Q := by
  let B := twoCosets S (f-g) hd
  have hfB : f ∉ B := by
    rintro (h | ⟨a, ha, e⟩)
    · exact hf h
    · exact hg ((show a=g by omega) ▸ ha)
  obtain ⟨Q, hBQ, ir, hmiss, _⟩ := exists_irreducible_avoiding hfB
  have hdB : f-g ∈ B := Or.inr ⟨0, S.zero_mem, by omega⟩
  refine ⟨Q, fun _ h ↦ hBQ (Or.inl h), ir, ?_, hmiss⟩
  intro h
  exact hmiss ((by omega : g+(f-g)=f) ▸ Q.add_mem h (hBQ hdB))

private theorem pair_avoid (hm : 2*k ∈ S) (hg : Special S g) (hf : Special S f)
    (hc : g % k = f % k) :
    ∃ Q : AddSubmonoid ℕ, S ≤ Q ∧ Irreducible Q ∧ g ∉ Q ∧ f ∉ Q := by
  have aux : ∀ {a b : ℕ}, a ≤ b → a % k = b % k → (b-a)+(b-a) ∈ S := by
    intro a b hab he
    obtain ⟨t, ht⟩ := (Nat.modEq_iff_dvd' hab).mp he
    apply multiple_mem hm
    exact ⟨t, by rw [ht]; ring⟩
  rcases le_total g f with h | h
  · exact pair_avoid_le hg.1 hf.1 h (aux h hc)
  · obtain ⟨Q, hSQ, hir, h1, h2⟩ := pair_avoid_le hf.1 hg.1 h (aux h hc.symm)
    exact ⟨Q, hSQ, hir, h2, h1⟩

private theorem top_irreducible : Irreducible (⊤ : AddSubmonoid ℕ) := by
  refine ⟨?_, fun A B _ _ he ↦ Or.inl (le_antisymm (he ▸ inf_le_left) le_top)⟩
  change ((↑(⊤ : AddSubmonoid ℕ) : Set ℕ)ᶜ).Finite
  simp

private theorem class_avoider (hm : 2*k ∈ S) (i : ℕ) :
    ∃ Q : AddSubmonoid ℕ, S ≤ Q ∧ Irreducible Q ∧
      ∀ g, Special S g → (g % (2*k) = i ∨ g % (2*k) = i+k) → g ∉ Q := by
  classical
  by_cases h₁ : ∃ a, Special S a ∧ a % (2*k) = i
  · obtain ⟨a, ha, hia⟩ := h₁
    by_cases h₂ : ∃ b, Special S b ∧ b % (2*k) = i+k
    · obtain ⟨b, hb, hib⟩ := h₂
      have hc : a % k = b % k := by
        have div : k ∣ 2*k := dvd_mul_left k 2
        rw [← Nat.mod_mod_of_dvd a div, ← Nat.mod_mod_of_dvd b div, hia, hib]
        simp
      obtain ⟨Q, hSQ, hir, hA, hB⟩ := pair_avoid hm ha hb hc
      refine ⟨Q, hSQ, hir, ?_⟩
      rintro g hg (hi | hi)
      · exact (special_unique_residue hm hg ha (hi.trans hia.symm)).symm ▸ hA
      · exact (special_unique_residue hm hg hb (hi.trans hib.symm)).symm ▸ hB
    · obtain ⟨Q, hSQ, hir, hA, _⟩ := exists_irreducible_avoiding ha.1
      refine ⟨Q, hSQ, hir, ?_⟩
      rintro g hg (hi | hi)
      · exact (special_unique_residue hm hg ha (hi.trans hia.symm)).symm ▸ hA
      · exact (h₂ ⟨g,hg,hi⟩).elim
  · by_cases h₂ : ∃ b, Special S b ∧ b % (2*k) = i+k
    · obtain ⟨b,hb,hib⟩ := h₂
      obtain ⟨Q, hSQ, hir, hB, _⟩ := exists_irreducible_avoiding hb.1
      refine ⟨Q, hSQ, hir, ?_⟩
      rintro g hg (hi | hi)
      · exact (h₁ ⟨g,hg,hi⟩).elim
      · exact (special_unique_residue hm hg hb (hi.trans hib.symm)).symm ▸ hB
    · refine ⟨⊤, le_top, top_irreducible, ?_⟩
      rintro g hg (hi | hi)
      · exact (h₁ ⟨g,hg,hi⟩).elim
      · exact (h₂ ⟨g,hg,hi⟩).elim

theorem short_even_decomposition (hS : Numerical S) (hm : HasMultiplicity S (2*k)) :
    ∃ n ≤ k, HasLength S n := by
  classical
  choose Q hSQ hir hav using class_avoider hm.2.1
  let D := (Finset.range k).image Q
  have el : Eligible S D := by
    intro T hT
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hT
    exact ⟨hir i, hSQ i⟩
  have cov : Cover S D := by
    intro g hg
    let r := g % (2*k)
    have hr : r < 2*k := Nat.mod_lt _ hm.1
    by_cases hi : r < k
    · exact ⟨Q r, Finset.mem_image.mpr ⟨r, Finset.mem_range.mpr hi, rfl⟩, hav r g hg (Or.inl rfl)⟩
    · exact ⟨Q (r-k), Finset.mem_image.mpr ⟨r-k, Finset.mem_range.mpr (by omega), rfl⟩,
             hav (r-k) g hg (Or.inr (show r = r-k+k by omega))⟩
  obtain ⟨E, he, hd⟩ := exists_minimal_subcover hS el cov
  have hcard : D.card ≤ k := (Finset.card_image_le).trans_eq (Finset.card_range k)
  exact ⟨E.card, (Finset.card_le_card he).trans hcard, E, hd, rfl⟩

theorem even_of_interval (hi : LengthsInterval) : EvenMultiplicityDescent := by
  intro S hS k j hm hj _ hlen
  obtain ⟨n, hn, hshort⟩ := short_even_decomposition hS hm
  exact hi S hS n j (j-1) hshort hlen (by omega) (by omega)

theorem lengthsExist : LengthsExist := by
  classical
  intro S hS
  let G := specials S
  have pick : ∀ g : {x // x ∈ G}, ∃ Q : AddSubmonoid ℕ,
      S ≤ Q ∧ Irreducible Q ∧ (g : ℕ) ∉ Q := by
    intro g
    have hs := (mem_specials hS).1 g.property
    obtain ⟨Q,hle,hir,hg,_⟩ := exists_irreducible_avoiding hs.1
    exact ⟨Q, hle, hir, hg⟩
  choose Q hSQ hir hav using pick
  let D := G.attach.image Q
  have el : Eligible S D := by
    intro T hT
    obtain ⟨g, _, rfl⟩ := Finset.mem_image.mp hT
    exact ⟨hir g,hSQ g⟩
  have hc : Cover S D := by
    intro g hs
    let t : {x // x ∈ G} := ⟨g, (mem_specials hS).2 hs⟩
    exact ⟨Q t, Finset.mem_image.mpr ⟨t, Finset.mem_attach _ _, rfl⟩, hav t⟩
  obtain ⟨E, _, hd⟩ := exists_minimal_subcover hS el hc
  exact ⟨E.card, E, hd, rfl⟩

end TaskL.Semigroup
