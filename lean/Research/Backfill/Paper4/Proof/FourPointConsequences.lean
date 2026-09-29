import Research.Backfill.Paper4.Proof.Foundation

/-! Complete frozen Proposition3 for arbitrary a,b,c.
The arithmetic contradiction uses the already accepted integer Lemma2.
Acceptance evidence for this new module is recorded separately. -/
set_option autoImplicit false

namespace CodexPaper4
open BackfillPaper4

namespace FourPointConsequences

lemma fp_nat_to_int {A B C : ℕ} (h : Challenge.FP A B C) :
    Challenge.FPZ (A : ℤ) (B : ℤ) (C : ℤ) := by
  unfold Challenge.FP at h
  unfold Challenge.FPZ
  rcases h with ⟨hab,hc⟩ | ⟨hac,hb⟩ | ⟨hbc,ha⟩
  · exact Or.inl ⟨by exact_mod_cast hab, by exact_mod_cast hc⟩
  · exact Or.inr (Or.inl ⟨by exact_mod_cast hac, by exact_mod_cast hb⟩)
  · exact Or.inr (Or.inr ⟨by exact_mod_cast hbc, by exact_mod_cast ha⟩)

end FourPointConsequences

/-- The full comparison inequality does not assume a triametral triple. -/
theorem check_Proposition3 : Challenge.Proposition3 := by
  intro V _ G _hconn hfp x y hxy a b c hab hac hbc
  have hxy' : G.dist x y = G.diam := hxy
  by_contra hn
  have hmax :
      max (max (Challenge.triDist G a x y) (Challenge.triDist G b x y))
        (Challenge.triDist G c x y) < Challenge.triDist G a b c :=
    lt_of_not_ge hn
  obtain ⟨habmax,hc⟩ := max_lt_iff.mp hmax
  obtain ⟨ha,hb⟩ := max_lt_iff.mp habmax
  simp only [Challenge.triDist, G.dist_comm (u := a) (v := x),
    G.dist_comm (u := a) (v := y), hxy'] at ha
  simp only [Challenge.triDist, G.dist_comm (u := b) (v := x),
    G.dist_comm (u := b) (v := y), hxy'] at hb
  simp only [Challenge.triDist, G.dist_comm (u := c) (v := x),
    G.dist_comm (u := c) (v := y), hxy'] at hc
  have f1 := FourPointConsequences.fp_nat_to_int (hfp x y a b)
  have f2 := FourPointConsequences.fp_nat_to_int (hfp x y a c)
  have f3 := FourPointConsequences.fp_nat_to_int (hfp x y b c)
  simp only [Nat.cast_add, hxy'] at f1 f2 f3
  have habZ : (G.dist a b : ℤ) ≤ (G.diam : ℤ)-1 := by omega
  have hacZ : (G.dist a c : ℤ) ≤ (G.diam : ℤ)-1 := by omega
  have hbcZ : (G.dist b c : ℤ) ≤ (G.diam : ℤ)-1 := by omega
  have haZ : (G.diam : ℤ)+(G.dist x a : ℤ)+(G.dist y a : ℤ) ≤
      (G.dist a b : ℤ)+(G.dist a c : ℤ)+(G.dist b c : ℤ)-1 := by omega
  have hbZ : (G.diam : ℤ)+(G.dist x b : ℤ)+(G.dist y b : ℤ) ≤
      (G.dist a b : ℤ)+(G.dist a c : ℤ)+(G.dist b c : ℤ)-1 := by omega
  have hcZ : (G.diam : ℤ)+(G.dist x c : ℤ)+(G.dist y c : ℤ) ≤
      (G.dist a b : ℤ)+(G.dist a c : ℤ)+(G.dist b c : ℤ)-1 := by omega
  exact check_Lemma2 (G.diam : ℤ) (G.dist a b : ℤ) (G.dist a c : ℤ) (G.dist b c : ℤ)
    (G.dist x a : ℤ) (G.dist x b : ℤ) (G.dist x c : ℤ)
    (G.dist y a : ℤ) (G.dist y b : ℤ) (G.dist y c : ℤ)
    habZ hacZ hbcZ f1 f2 f3 haZ hbZ hcZ

#print axioms check_Proposition3
end CodexPaper4
