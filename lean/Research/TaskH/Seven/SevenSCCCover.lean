import Research.TaskH.Seven.SevenSCCRelation

/-! Pure finite support union bounds. A joined ordering is an internal
finite-family interface; graph construction of that ordering is separate. -/

set_option autoImplicit false

universe u

namespace TaskH.Seven

open scoped Classical

variable {V : Type u} [DecidableEq V]

def sevenSupportUnion : List (Finset V) → Finset V
  | [] => ∅
  | S :: L => S ∪ sevenSupportUnion L

def SevenJoinedFamily : List (Finset V) → Prop
  | [] => True
  | S :: L => S.card ≤ 7 ∧ SevenJoinedFamily L ∧
      (L = [] ∨ (S ∩ sevenSupportUnion L).Nonempty)

theorem card_union_le_add_six (A B : Finset V) (hB : B.card ≤ 7)
    (hjoin : (A ∩ B).Nonempty) : (A ∪ B).card ≤ A.card + 6 := by
  have hpos : 0 < (A ∩ B).card := Finset.card_pos.mpr hjoin
  have hsum := Finset.card_union_add_card_inter A B
  omega

theorem sevenSupportUnion_card_le (L : List (Finset V)) (hL : SevenJoinedFamily L) :
    (sevenSupportUnion L).card ≤ 6 * L.length + 1 := by
  revert hL
  induction L with
  | nil => intro _; simp [sevenSupportUnion]
  | cons S L ih =>
    intro hL
    rcases hL with ⟨hS, htail, hjoin⟩
    rcases hjoin with rfl | hjoin
    · simpa [sevenSupportUnion] using hS
    · have htailbound := ih htail
      have hu := card_union_le_add_six (sevenSupportUnion L) S hS
        (by simpa only [Finset.inter_comm] using hjoin)
      have hu' : (sevenSupportUnion (S :: L)).card ≤
          (sevenSupportUnion L).card + 6 := by
        simpa only [sevenSupportUnion, Finset.union_comm] using hu
      simp only [List.length_cons]
      omega

def SupportIntersection {I : Type*} (F : Finset I) (S : I → Finset V) (a b : I) : Prop :=
  a ∈ F ∧ b ∈ F ∧ (S a ∩ S b).Nonempty

theorem reflTransGen_step_out {I : Type*} (A : Finset I) (R : I → I → Prop)
    {a b : I} (h : Relation.ReflTransGen R a b) :
    a ∈ A → b ∉ A → ∃ u ∈ A, ∃ v ∉ A, R u v := by
  induction h with
  | refl =>
    intro ha hn
    exact (hn ha).elim
  | @tail b d _ hbd ih =>
    intro ha hd
    by_cases hb : b ∈ A
    · exact ⟨b, hb, d, hd, hbd⟩
    · exact ih ha hb

/-- A connected finite family of seven-point supports has union size
at most6 times the number of members plus1. The maximal joined subfamily
argument constructs the needed growth; it assumes no supplied ordering. -/
theorem finiteFamily_union_card_le {I : Type*} (F : Finset I) (S : I → Finset V)
    (hne : F.Nonempty) (hsize : ∀ i ∈ F, (S i).card ≤ 7)
    (hconnected : ∀ a ∈ F, ∀ b ∈ F,
      Relation.ReflTransGen (SupportIntersection F S) a b) :
    (F.biUnion S).card ≤ 6 * F.card + 1 := by
  classical
  let candidates : Finset (Finset I) := F.powerset.filter (fun A =>
    A.Nonempty ∧ (A.biUnion S).card ≤ 6 * A.card + 1)
  obtain ⟨r, hr⟩ := hne
  have hbase : ({r} : Finset I) ∈ candidates := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_powerset.mpr ?_, Finset.singleton_nonempty r, ?_⟩
    · exact Finset.singleton_subset_iff.mpr hr
    · simpa using hsize r hr
  obtain ⟨A, hA, hmax⟩ := Finset.exists_max_image candidates Finset.card ⟨{r}, hbase⟩
  have hAsub : A ⊆ F := Finset.mem_powerset.mp (Finset.mem_filter.mp hA).1
  have hAne : A.Nonempty := (Finset.mem_filter.mp hA).2.1
  have hAbound : (A.biUnion S).card ≤ 6 * A.card + 1 :=
    (Finset.mem_filter.mp hA).2.2
  have hAF : A = F := by
    by_contra hneAF
    have hnot : ¬ ∀ d, d ∈ F → d ∈ A := by
      intro h
      exact hneAF (Finset.Subset.antisymm hAsub (fun d hd => h d hd))
    push Not at hnot
    obtain ⟨d, hdF, hdA⟩ := hnot
    obtain ⟨b, hbA⟩ := hAne
    obtain ⟨u, huA, v, hvA, huv⟩ := reflTransGen_step_out A (SupportIntersection F S)
      (hconnected b (hAsub hbA) d hdF) hbA hdA
    have hvF : v ∈ F := huv.2.1
    obtain ⟨z, hz⟩ := huv.2.2
    have hzparts := Finset.mem_inter.mp hz
    have hjoin : (A.biUnion S ∩ S v).Nonempty := by
      refine ⟨z, Finset.mem_inter.mpr ⟨?_, hzparts.2⟩⟩
      exact Finset.mem_biUnion.mpr ⟨u, huA, hzparts.1⟩
    have hnewbound : ((insert v A).biUnion S).card ≤ 6 * (insert v A).card + 1 := by
      have hu := card_union_le_add_six (A.biUnion S) (S v) (hsize v hvF) hjoin
      rw [Finset.biUnion_insert]
      have hu' : (S v ∪ A.biUnion S).card ≤ (A.biUnion S).card + 6 := by
        simpa only [Finset.union_comm] using hu
      rw [Finset.card_insert_of_notMem hvA]
      omega
    have hnew : insert v A ∈ candidates := by
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_powerset.mpr ?_, Finset.insert_nonempty v A, hnewbound⟩
      exact Finset.insert_subset_iff.mpr ⟨hvF, hAsub⟩
    have hle := hmax (insert v A) hnew
    rw [Finset.card_insert_of_notMem hvA] at hle
    omega
  simpa only [hAF] using hAbound

/-- Once the actual finite component/circle partition is proved, this
last natural-number sum closes order45 without further rigidity cases. -/
theorem order45_of_finite_component_budgets {I : Type*} (Q : Finset I)
    (N T : I → ℕ) (n : ℕ)
    (hpartition : (∑ i ∈ Q, N i) = n)
    (hcover : ∀ i ∈ Q, N i ≤ 6 * T i + 1)
    (hmin : ∀ i ∈ Q, 2 ≤ T i)
    (htotal : (∑ i ∈ Q, T i) ≤ 7) : n ≤ 45 := by
  have htwo : 2 * Q.card ≤ ∑ i ∈ Q, T i := by
    calc
      2 * Q.card = ∑ _i ∈ Q, 2 := by simp [Nat.mul_comm]
      _ ≤ _ := Finset.sum_le_sum hmin
  have hnum : Q.card ≤ 3 := by omega
  have hsum : (∑ i ∈ Q, N i) ≤ ∑ i ∈ Q, (6 * T i + 1) :=
    Finset.sum_le_sum hcover
  have hrhs : (∑ i ∈ Q, (6 * T i + 1)) =
      6 * (∑ i ∈ Q, T i) + Q.card := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    simp
  rw [hpartition, hrhs] at hsum
  omega

end TaskH.Seven

#print axioms TaskH.Seven.sevenSupportUnion
#print axioms TaskH.Seven.SevenJoinedFamily
#print axioms TaskH.Seven.card_union_le_add_six
#print axioms TaskH.Seven.sevenSupportUnion_card_le
#print axioms TaskH.Seven.SupportIntersection
#print axioms TaskH.Seven.reflTransGen_step_out
#print axioms TaskH.Seven.finiteFamily_union_card_le
#print axioms TaskH.Seven.order45_of_finite_component_budgets
