import Mathlib

/-! Scalar endgames of the actual C16 attachment count in BP45.
These lemmas contain no graph theorem and do not assume their numerical
premises for an original graph. The real attachment partition, disjoint high
neighborhoods, and four forced low or zero attachment vertices still have to
supply all these premises in the graph transport. -/

set_option autoImplicit false

namespace TaskH.Seven.BP

theorem quad_side_at_least_fourteen (a b e h3 h4 n0 n1 : ℕ)
    (hn : a + b ≤ 29) (he : 29 ≤ e)
    (hidentity : e + n1 + 2 * n0 = 2 * a + h3 + 2 * h4)
    (hdisjoint : 4 * h3 + 3 * h4 ≤ b) (hzero : 4 ≤ n0) : 14 ≤ a := by
  omega

theorem quad_side_fourteen_extreme (a b e h3 h4 n0 n1 : ℕ)
    (ha : a = 14) (hn : a + b ≤ 29) (he : 29 ≤ e)
    (hidentity : e + n1 + 2 * n0 = 2 * a + h3 + 2 * h4)
    (hdisjoint : 4 * h3 + 3 * h4 ≤ b) (hzero : 4 ≤ n0) :
    b = 15 ∧ h3 = 0 ∧ h4 = 5 ∧ n0 = 4 ∧ n1 ≤ 1 := by
  have hh4 : 5 ≤ h4 := by omega
  omega

theorem small_noquad_side_impossible (a b e h t : ℕ)
    (hn : a + b ≤ 29) (hb : b ≤ 14) (he : 29 ≤ e)
    (hidentity : e + t = 2 * b + h)
    (hdisjoint : 4 * h ≤ a) (hlow : 0 < h → 4 ≤ t) : False := by
  have hh : 0 < h := by omega
  have ht := hlow hh
  omega

theorem two_noquad_sides_impossible (a b ea eb ha hb ta tb : ℕ)
    (hn : a + b ≤ 29) (hea : 29 ≤ ea) (heb : 29 ≤ eb)
    (hida : ea + ta = 2 * a + ha) (hidb : eb + tb = 2 * b + hb)
    (hda : 4 * ha ≤ b) (hdb : 4 * hb ≤ a)
    (hla : 0 < ha → 4 ≤ ta) (hlb : 0 < hb → 4 ≤ tb) : False := by
  by_cases hapos : 0 < ha
  · by_cases hbpos : 0 < hb
    · have hta := hla hapos
      have htb := hlb hbpos
      omega
    · have hbzero : hb = 0 := by omega
      have hs : a ≤ 14 := by omega
      exact small_noquad_side_impossible b a ea ha ta (by omega) hs hea hida hda hla
  · have hazero : ha = 0 := by omega
    have hs : b ≤ 14 := by omega
    exact small_noquad_side_impossible a b eb hb tb hn hs heb hidb hdb hlb

theorem noquad_opposite_to_large_side_impossible (a b eb h t : ℕ)
    (hn : a + b ≤ 29) (ha : 15 ≤ a) (heb : 29 ≤ eb)
    (hid : eb + t = 2 * b + h) (hd : 4 * h ≤ a)
    (hlow : 0 < h → 4 ≤ t) : False := by
  have hs : b ≤ 14 := by omega
  exact small_noquad_side_impossible a b eb h t hn hs heb hid hd hlow

end TaskH.Seven.BP

#print axioms TaskH.Seven.BP.quad_side_at_least_fourteen
#print axioms TaskH.Seven.BP.quad_side_fourteen_extreme
#print axioms TaskH.Seven.BP.small_noquad_side_impossible
#print axioms TaskH.Seven.BP.two_noquad_sides_impossible
#print axioms TaskH.Seven.BP.noquad_opposite_to_large_side_impossible
