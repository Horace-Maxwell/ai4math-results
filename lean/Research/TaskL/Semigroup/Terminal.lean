import Research.TaskL.Semigroup.Algebra
import Research.TaskL.Semigroup.Foundations

namespace TaskL.Semigroup
open Challenge
noncomputable section
open Classical

variable {S Q : AddSubmonoid ℕ} {D : Finset (AddSubmonoid ℕ)}

private theorem private_special (hS : Numerical S) (hd : Decomposition S D)
    (hQ : Q ∈ D) : ∃ g, Special S g ∧ g ∉ Q ∧
      ∀ R ∈ D, g ∉ R → R = Q := by
  obtain ⟨_,hc,hm⟩ := (decomp_iff hS).mp hd
  have hn := hm (D.erase Q) (Finset.erase_ssubset hQ)
  unfold Cover at hn
  push Not at hn
  obtain ⟨g,hg,hAll⟩ := hn
  have uniq (R : AddSubmonoid ℕ) (hR : R ∈ D) (hr : g ∉ R) : R = Q := by
    by_contra h
    exact hr (hAll R (Finset.mem_erase.mpr ⟨h,hR⟩))
  obtain ⟨R,hR,hgR⟩ := hc _ hg
  exact ⟨g,hg,uniq R hR hgR ▸ hgR,uniq⟩

private theorem max_gap_special (hS : Numerical S) (hnot : S ≠ ⊤) : Special S (frob S) := by
  have hn := frob_notMem hS hnot
  have hp : 0 < frob S := Nat.pos_of_ne_zero fun h => hn (h ▸ S.zero_mem)
  exact ⟨hn, mem_of_frob_lt hS (by omega), fun _ _ ht => mem_of_frob_lt hS (by omega)⟩

theorem terminal_card (hS : Numerical S) (hd : Decomposition S D)
    (edge : ∀ Q ∈ D, ∀ g, Special S g → (g ∉ Q ↔ 2*g < frob Q ∨ g = frob Q)) :
    D.card = ((specials S).filter (fun g => frob S < 2*g)).card := by
  obtain ⟨hel,hcov,-⟩ := (decomp_iff hS).mp hd
  have fbound (Q : AddSubmonoid ℕ) (hQ : Q ∈ D) : frob Q ≤ frob S := by
    apply Finset.sup_le
    intro g hg
    obtain ⟨hir,hsub⟩ := hel Q hQ
    exact le_frob hS (fun h => (mem_gaps hir.1).mp hg (hsub h))
  have hinj : Set.InjOn frob D := by
    intro Q hQ R hR he
    obtain ⟨g,hg,hgQ,hu⟩ := private_special hS hd hQ
    have e := (edge Q hQ g hg).mp hgQ
    rw [he] at e
    exact (hu R hR ((edge R hR g hg).mpr e)).symm
  have image_eq : D.image frob = (specials S).filter (fun g => frob S < 2*g) := by
    ext g
    constructor
    · intro h
      obtain ⟨Q,hQ,rfl⟩ := Finset.mem_image.mp h
      obtain ⟨z,hz,hzQ,hu⟩ := private_special hS hd hQ
      have hSprop : S ≠ ⊤ := fun h => hz.1 (h ▸ AddSubmonoid.mem_top _)
      have hF := max_gap_special hS hSprop
      have hp : 0 < frob S := Nat.pos_of_ne_zero fun h => hF.1 (h ▸ S.zero_mem)
      have hne : 2*z ≠ frob S := by
        intro he
        exact hF.1 (he ▸ show 2*z ∈ S by simpa [two_mul] using hz.2.1)
      by_cases hlow : 2*z < frob S
      · obtain ⟨R,hR,hmiss⟩ := hcov _ hF
        have hf : frob R = frob S := le_antisymm (fbound R hR) (le_frob (hel R hR).1.1 hmiss)
        have he := hu R hR ((edge R hR z hz).mpr (Or.inl (hf ▸ hlow)))
        rw [← he, hf]
        exact Finset.mem_filter.mpr ⟨(mem_specials hS).mpr hF, by omega⟩
      · have he := (edge Q hQ z hz).mp hzQ
        have hmax := fbound Q hQ
        have eqn : z = frob Q := by omega
        rw [← eqn]
        exact Finset.mem_filter.mpr ⟨(mem_specials hS).mpr hz, by omega⟩
    · intro h
      obtain ⟨hgs, hhi⟩ := Finset.mem_filter.mp h
      have hg := (mem_specials hS).mp hgs
      obtain ⟨Q,hQ,hmiss⟩ := hcov _ hg
      have edge_g := (edge Q hQ g hg).mp hmiss
      have bound := fbound Q hQ
      exact Finset.mem_image.mpr ⟨Q,hQ,by omega⟩
  exact (Finset.card_image_of_injOn hinj).symm.trans (congrArg Finset.card image_eq)

theorem standard_card (hS : Numerical S) (hd : Decomposition S D)
    (hstd : ∀ Q ∈ D, Standard S Q) :
    D.card = ((specials S).filter (fun g => frob S < 2*g)).card := by
  apply terminal_card hS hd
  intro Q hQ g hg
  have hel := (decomp_iff hS).mp hd |>.1 Q hQ
  obtain ⟨n,_,hmiss,-⟩ := private_special hS hd hQ
  have hp : Q ≠ ⊤ := fun h => hmiss (h ▸ AddSubmonoid.mem_top _)
  exact standard_edge hel.1 hel.2 hp (hstd Q hQ) hg

end
end TaskL.Semigroup
