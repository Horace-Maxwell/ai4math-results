import Research.AxialMSZ.Proof.ExSBase
set_option autoImplicit false
namespace CodexAxial.SimpleExample
open AxialMSZ.Challenge

theorem a_vec : a = ![1,0,0,0] := by
  funext k
  fin_cases k <;> simp [a,e]

theorem b_vec : b = ![0,1,0,0] := by
  funext k
  fin_cases k <;> simp [b,e]

theorem c_vec : c = ![0,0,0,1] := by
  funext k
  fin_cases k <;> simp [c,e]

theorem x_mul (u : A) : ExS.μ x u =
    ![u 0/4-u 1/4-u 3/2, -u 0/4+u 1/4-u 3/2,
      u 0/4+u 1/4+u 2+u 3/2, -u 3/4] := by
  funext k
  rw [mul_apply]
  fin_cases k <;> simp [Fin.sum_univ_four,ExS.T,x,e] <;> ring

def phi (u : A) : ℚ := u 3-u 2/2

theorem projector (u : A) :
    (2 : ℚ) • ExS.μ c (ExS.μ c u) - ExS.μ c u = phi u • c := by
  simp only [c_mul]
  funext k
  fin_cases k <;> simp [phi,c,e] <;> ring

theorem phi_detects_nonzero (u : A) (hu : u ≠ 0) :
    phi u ≠ 0 ∨ phi (ExS.μ a u) ≠ 0 ∨ phi (ExS.μ b u) ≠ 0 ∨ phi (ExS.μ x u) ≠ 0 := by
  by_contra hn
  push Not at hn
  rcases hn with ⟨h0,h1,h2,h3⟩
  simp [phi,a_mul,b_mul,x_mul] at h0 h1 h2 h3
  apply hu
  funext k
  fin_cases k <;> simp <;> linarith

theorem c_mem_of_phi {I : Submodule ℚ A} (hI : IsIdeal ExS.μ I) {u : A}
    (hu : u ∈ I) (hp : phi u ≠ 0) : c ∈ I := by
  have hc := (hI c u hu).1
  have hcc := (hI c (ExS.μ c u) hc).1
  have hm : phi u • c ∈ I := by
    rw [← projector]
    exact I.sub_mem (I.smul_mem 2 hcc) hc
  have hi := I.smul_mem (phi u)⁻¹ hm
  simpa [smul_smul,inv_mul_cancel₀ hp] using hi

theorem ideal_top_of_c {I : Submodule ℚ A} (hI : IsIdeal ExS.μ I) (hc : c ∈ I) : I = ⊤ := by
  have hxc := (hI x c hc).1
  have haxc := (hI a (ExS.μ x c) hxc).1
  have hbxc := (hI b (ExS.μ x c) hxc).1
  have ha : a ∈ I := by
    have he : a = (1/2 : ℚ) • c + (2 : ℚ) • ExS.μ x c - (4 : ℚ) • ExS.μ a (ExS.μ x c) := by
      rw [a_mul,x_mul]
      funext k
      fin_cases k <;> norm_num [a_vec,c_vec,Matrix.vecHead,Matrix.vecTail]
    rw [he]
    exact I.sub_mem (I.add_mem (I.smul_mem _ hc) (I.smul_mem _ hxc)) (I.smul_mem _ haxc)
  have hb : b ∈ I := by
    have he : b = (1/2 : ℚ) • c + (2 : ℚ) • ExS.μ x c - (4 : ℚ) • ExS.μ b (ExS.μ x c) := by
      rw [b_mul,x_mul]
      funext k
      fin_cases k <;> norm_num [b_vec,c_vec,Matrix.vecHead,Matrix.vecTail]
    rw [he]
    exact I.sub_mem (I.add_mem (I.smul_mem _ hc) (I.smul_mem _ hxc)) (I.smul_mem _ hbxc)
  have hx : x ∈ I := by
    rw [x_from_ab]
    exact I.sub_mem (I.add_mem ha hb) (I.smul_mem _ (hI a b hb).1)
  rw [eq_top_iff]
  intro u _
  rw [coordinates u]
  exact I.add_mem (I.add_mem (I.add_mem (I.smul_mem _ ha) (I.smul_mem _ hb))
    (I.smul_mem _ hx)) (I.smul_mem _ hc)

theorem simple : IsSimpleAlg ExS.μ := by
  refine ⟨?_, ?_⟩
  · refine ⟨c,c,?_⟩
    intro h
    have hz := congrFun h 3
    rw [c_mul] at hz
    norm_num [c,e] at hz
  · intro I hI
    by_cases hc : c ∈ I
    · exact Or.inr (ideal_top_of_c hI hc)
    · left
      rw [Submodule.eq_bot_iff]
      intro u hu
      by_contra hne
      rcases phi_detects_nonzero u hne with h0 | h1 | h2 | h3
      · exact hc (c_mem_of_phi hI hu h0)
      · exact hc (c_mem_of_phi hI (hI a u hu).1 h1)
      · exact hc (c_mem_of_phi hI (hI b u hu).1 h2)
      · exact hc (c_mem_of_phi hI (hI x u hu).1 h3)

#print axioms simple
end CodexAxial.SimpleExample
