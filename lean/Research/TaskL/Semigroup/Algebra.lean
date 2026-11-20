import Research.TaskL.Semigroup.AlgebraSwap
import Research.TaskL.Semigroup.FBase

namespace TaskL.Semigroup
open Challenge
noncomputable section

variable {S Q : AddSubmonoid ℕ} {v g : ℕ}

def Standard (S Q : AddSubmonoid ℕ) : Prop :=
  ∀ n : ℕ, 2*n < frob Q → n ∈ Q → n ∈ S

theorem isFrob_frob (hQ : Numerical Q) (hproper : Q ≠ ⊤) : IsFrob Q (frob Q) :=
  ⟨frob_notMem hQ hproper, fun _ h => mem_of_frob_lt hQ h⟩

private theorem frob_eq_of_isFrob (hQ : Numerical Q) {f : ℕ} (hF : IsFrob Q f) :
    frob Q = f := by
  have hproper : Q ≠ ⊤ := fun h => hF.1 (h ▸ show f ∈ (⊤ : AddSubmonoid ℕ) from trivial)
  apply le_antisymm _ (le_frob hQ hF.1)
  exact le_of_not_gt (fun h => frob_notMem hQ hproper (hF.2 _ h))

private theorem gapWeight_swap {R : AddSubmonoid ℕ} {u v : ℕ}
    (hQ : Numerical Q) (hR : Numerical R) (huv : u<v) (hu : u∈Q) (hv : v∉Q)
    (hm : ∀ n : ℕ, n∈R ↔ n=v ∨ n∈Q ∧ n≠u) : gapWeight R < gapWeight Q := by
  classical
  have hvG := (mem_gaps hQ).2 hv
  have huG : u ∉ gaps Q := fun h => (mem_gaps hQ).1 h hu
  have he : gaps R = insert u ((gaps Q).erase v) := by
    ext n
    simp only [mem_gaps hR, Finset.mem_insert, Finset.mem_erase, mem_gaps hQ, hm]
    by_cases hnu : n=u
    · subst n
      simp [huv.ne]
    · simp [hnu,not_or]
  have huG' : u ∉ (gaps Q).erase v := fun h => huG (Finset.mem_of_mem_erase h)
  have hs := Finset.sum_erase_add (gaps Q) (fun n => n+1) hvG
  unfold gapWeight
  rw [he,Finset.sum_insert huG']
  omega

theorem exchange_of_nonstandard (hQ : Irreducible Q) (hSQ : S≤Q) (hproper : Q≠⊤)
    (hn : ¬ Standard S Q) :
    ∃ u v : ℕ, ∃ Q' : AddSubmonoid ℕ, u<v ∧ v∉Q ∧ v<frob Q ∧
      Irreducible Q' ∧ S≤Q' ∧ gapWeight Q'<gapWeight Q ∧
      ∀ n : ℕ, n∈Q' ↔ n=v ∨ n∈Q ∧ n≠u := by
  classical
  have hF := isFrob_frob hQ.1 hproper
  have ex : ∃ n : ℕ, 2*n<frob Q ∧ n∈Q ∧ n∉S := by
    by_contra! h
    exact hn (fun n hl hm => h n hl hm)
  let u := Nat.find ex
  obtain ⟨hlo, huQ, huS⟩ := (Nat.find_spec ex : 2*u<frob Q ∧ u∈Q ∧ u∉S)
  change u ∉ S at huS
  have hup : 0<u := Nat.pos_of_ne_zero (fun he => huS (he ▸ S.zero_mem))
  have hmin (a : ℕ) (ha : a<u) (hm : a∈Q) : a∈S := by
    by_contra hs
    have hh := Nat.find_min' ex (show 2*a<frob Q ∧ a∈Q ∧ a∉S from ⟨by omega,hm,hs⟩)
    exact (not_le_of_gt ha) hh
  have hatom (a : ℕ) (ha : a∈Q) (b : ℕ) (hb : b∈Q) (eq : a+b=u) : a=0 ∨ b=0 := by
    by_contra! h
    exact huS (eq ▸ S.add_mem (hmin a (by omega) ha) (hmin b (by omega) hb))
  obtain ⟨R,hR,hSR,_,hm⟩ := swap_at_low_atom hQ hF hSQ hup hlo huS hatom
  have hv : frob Q-u ∉ Q := fun hh => (complement_low hQ hF hlo).1 hh huQ
  exact ⟨u,frob Q-u,R,by omega,hv,by omega,hR,hSR,
    gapWeight_swap hQ.1 hR.1 (by omega) huQ hv hm, hm⟩

theorem repair_component (hQ : Irreducible Q) (hv : v∉Q) (hlt : v<frob Q) :
    ∃ R : AddSubmonoid ℕ, Irreducible R ∧ Q≤R ∧ v∉R ∧ frob R=v ∧
      gapWeight R<gapWeight Q := by
  classical
  obtain ⟨R,hQR,hR,hvR,ht⟩ := exists_irreducible_avoiding hv
  have hproper : Q ≠ ⊤ := fun h => hv (h ▸ show v ∈ (⊤ : AddSubmonoid ℕ) from trivial)
  have hf := (mem_gaps hQ.1).2 (frob_notMem hQ.1 hproper)
  have hfR : frob Q ∉ gaps R := fun hg => (mem_gaps hR.1).1 hg (ht _ hlt)
  refine ⟨R,hR,hQR,hvR,frob_eq_of_isFrob hR.1 ⟨hvR,ht⟩,?_⟩
  have hs : gaps R ⊆ (gaps Q).erase (frob Q) := by
    intro n hn
    apply Finset.mem_erase.mpr
    exact ⟨fun he => hfR (he ▸ hn),
      (mem_gaps hQ.1).2 (fun h => (mem_gaps hR.1).1 hn (hQR h))⟩
  have hsum := Finset.sum_le_sum_of_subset_of_nonneg (f := fun n : ℕ => n+1) hs
      (fun _ _ _ => Nat.zero_le _)
  have hbig := Finset.sum_erase_add (gaps Q) (fun n => n+1) hf
  unfold gapWeight
  omega

theorem standard_edge (hQ : Irreducible Q) (hSQ : S≤Q) (hproper : Q≠⊤)
    (hs : Standard S Q) (hg : Special S g) : g∉Q ↔ 2*g<frob Q ∨ g=frob Q := by
  have hF := isFrob_frob hQ.1 hproper
  constructor
  · intro hgQ
    have hle := le_frob hQ.1 hgQ
    by_contra! h
    have hmid : 2*g ≠ frob Q := fun he => hF.1
      ((show frob Q=g+g by omega) ▸ hSQ hg.2.1)
    have hl : 2*(frob Q-g)<frob Q := by omega
    have htQ : frob Q-g ∈ Q := by
      by_contra hmiss
      have hm := (complement_low hQ hF hl).2 hmiss
      rw [show frob Q-(frob Q-g)=g by omega] at hm
      exact hgQ hm
    have hcontr := hg.2.2 (frob Q-g) (hs _ hl htQ) (by omega)
    rw [show g+(frob Q-g)=frob Q by omega] at hcontr
    exact hF.1 (hSQ hcontr)
  · rintro (hl | rfl)
    · exact fun h => hg.1 (hs g hl h)
    · exact hF.1

end
end TaskL.Semigroup
