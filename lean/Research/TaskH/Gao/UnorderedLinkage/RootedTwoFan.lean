import Research.TaskH.Gao.UnorderedLinkage.RerouteFork

/-! Complete elementary ordinary two-connectivity to actual rooted two-fan transport.
No Menger, block, subdivision, common-cycle, desired fan or linkage premise. -/
set_option autoImplicit false
universe u
namespace TaskH.Gao.UnorderedLinkage
open SimpleGraph
variable {V : Type u}

/-- The minimum actual trunk must have its branch at the original root. -/
theorem ordinary_two_connected_rooted_fan [Fintype V] (G : SimpleGraph V)
    (hG : _root_.TaskH.Fan.TwoConnected G) (x : V) (S : Set V)
    (hxS : x ∉ S) (hS : ∃ a ∈ S, ∃ b ∈ S, a ≠ b) :
    ∃ a ∈ S, ∃ b ∈ S, a ≠ b ∧
      ∃ (P : G.Walk x a) (Q : G.Walk x b), P.IsPath ∧ Q.IsPath ∧
        MeetsOnly P Q x ∧ HitsOnly P S a ∧ HitsOnly Q S b := by
  classical
  let F : ℕ → Prop := fun n => ∃ (c a b : V) (T : G.Walk x c)
    (P : G.Walk c a) (Q : G.Walk c b), IsFork S T P Q ∧ T.length = n
  obtain ⟨c₀, a₀, b₀, T₀, P₀, Q₀, hf₀⟩ :=
    ordinary_two_connected_fork_exists G hG x S hxS hS
  have hex : ∃ n, F n := ⟨T₀.length, c₀, a₀, b₀, T₀, P₀, Q₀, hf₀, rfl⟩
  obtain ⟨c, a, b, T, P, Q, hf, hlen⟩ := Nat.find_spec hex
  by_cases hcx : c = x
  · subst c
    rcases hf with ⟨ha, hb, hab, _, hP, hQ, _, hPS, hQS, _, _, hPQ⟩
    exact ⟨a, ha, b, hb, hab, P, Q, hP, hQ, hPQ, hPS, hQS⟩
  · obtain ⟨d, a', b', L, A, B, hnew, hshort⟩ :=
      ordinary_fork_strict_reduction G hG S T P Q hf hcx
    have hbetter : F L.length := ⟨d, a', b', L, A, B, hnew, rfl⟩
    have hmin := Nat.find_min' hex hbetter
    omega

/-- Full-support exact intersections and positive arms, from the ORIGINAL ordinary graph. -/
theorem ordinary_two_connected_rooted_fan_exact [Fintype V] (G : SimpleGraph V)
    (hG : _root_.TaskH.Fan.TwoConnected G) (x : V) (S : Set V)
    (hxS : x ∉ S) (hS : ∃ a ∈ S, ∃ b ∈ S, a ≠ b) :
    ∃ a ∈ S, ∃ b ∈ S, a ≠ b ∧
      ∃ (P : G.Walk x a) (Q : G.Walk x b), P.IsPath ∧ Q.IsPath ∧
        0 < P.length ∧ 0 < Q.length ∧
        (∀ z : V, z ∈ P.support ∧ z ∈ Q.support ↔ z = x) ∧
        (∀ z : V, z ∈ P.support ∧ z ∈ S ↔ z = a) ∧
        (∀ z : V, z ∈ Q.support ∧ z ∈ S ↔ z = b) := by
  obtain ⟨a, ha, b, hb, hab, P, Q, hP, hQ, hPQ, hPS, hQS⟩ :=
    ordinary_two_connected_rooted_fan G hG x S hxS hS
  have hxa : x ≠ a := by
    intro he
    apply hxS
    simpa only [he] using ha
  have hxb : x ≠ b := by
    intro he
    apply hxS
    simpa only [he] using hb
  have hp0 : 0 < P.length := by
    by_contra h
    have he : P.length = 0 := by omega
    exact hxa (Walk.eq_of_length_eq_zero he)
  have hq0 : 0 < Q.length := by
    by_contra h
    have he : Q.length = 0 := by omega
    exact hxb (Walk.eq_of_length_eq_zero he)
  refine ⟨a, ha, b, hb, hab, P, Q, hP, hQ, hp0, hq0, ?_, ?_, ?_⟩
  · intro z
    constructor
    · exact fun h => hPQ z h.1 h.2
    · rintro rfl
      exact ⟨P.start_mem_support, Q.start_mem_support⟩
  · intro z
    constructor
    · exact fun h => hPS z h.1 h.2
    · rintro rfl
      exact ⟨P.end_mem_support, ha⟩
  · intro z
    constructor
    · exact fun h => hQS z h.1 h.2
    · rintro rfl
      exact ⟨Q.end_mem_support, hb⟩
end TaskH.Gao.UnorderedLinkage
#print axioms TaskH.Gao.UnorderedLinkage.ordinary_two_connected_rooted_fan
#print axioms TaskH.Gao.UnorderedLinkage.ordinary_two_connected_rooted_fan_exact
