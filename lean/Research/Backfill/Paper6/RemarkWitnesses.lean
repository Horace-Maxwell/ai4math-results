import Research.Backfill.Paper6.S0WitnessBasic

/-! Eighteen genuine witnesses for the frozen sparse-weight remark.
The masks and their order are copied from sparse_table_s7.txt.
Weight 362 is deliberately absent: its known six-term row does not meet this contract.
Source candidate only; Root must compile and audit this module. -/

set_option autoImplicit false
set_option maxRecDepth 4096

namespace Paper6RemarkWitnesses

open BackfillPaper6.V3
open Paper6S0Witnesses

/-- The certificate retains the actual five-term bound. -/
def RowData5 (t : ℕ × List ℕ) : Prop :=
  (∀ s ∈ t.2, s < 16384) ∧
  (∀ s ∈ t.2, RM714.degNat s ≤ 7) ∧
  t.2.length ≤ 5 ∧ charCount t.2 0 = 16384 - 2 * (t.1 : ℤ)

instance rowData5Decidable (t : ℕ × List ℕ) : Decidable (RowData5 t) :=
  inferInstanceAs (Decidable
    ((∀ s ∈ t.2, s < 16384) ∧ (∀ s ∈ t.2, RM714.degNat s ≤ 7) ∧
      t.2.length ≤ 5 ∧ charCount t.2 0 = 16384 - 2 * (t.1 : ℤ)))

/-- The witness is exactly the polynomial encoded by the list, with an independent
support bound of five. No stronger bound is extracted from the eight-term S0 theorem. -/
theorem row_sound5 (t : ℕ × List ℕ) (h : RowData5 t) : t.1 ∈ weightsLe5 := by
  refine ⟨polyOf (t.2.map RM714.maskSet), ?_, ?_, ?_⟩
  · exact (Paper6ThmA.polyOf_support_card_le _).trans
      (by simpa only [List.length_map] using h.2.2.1)
  · apply Paper6ThmA.polyOf_degree_le
    intro S hS
    obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hS
    rw [RM714.card_maskSet]
    exact h.2.1 s hs
  · have heq := charCount_zero t.2
    have hcert := h.2.2.2
    have hw : (hammingNorm (evalFun (polyOf (t.2.map RM714.maskSet))) : ℤ) =
        (t.1 : ℤ) := by linarith
    exact_mod_cast hw

def row_254 : ℕ × List ℕ := (254, [127, 16256])

set_option maxHeartbeats 200000 in
theorem row_254_valid : RowData5 row_254 := by
  decide +kernel

theorem weight_254 : 254 ∈ weightsLe5 :=
  row_sound5 row_254 row_254_valid

def row_314 : ℕ × List ℕ := (314, [127, 16256, 4730])

set_option maxHeartbeats 200000 in
theorem row_314_valid : RowData5 row_314 := by
  decide +kernel

theorem weight_314 : 314 ∈ weightsLe5 :=
  row_sound5 row_314 row_314_valid

def row_318 : ℕ × List ℕ := (318, [127, 16256, 251, 13702])

set_option maxHeartbeats 200000 in
theorem row_318_valid : RowData5 row_318 := by
  decide +kernel

theorem weight_318 : 318 ∈ weightsLe5 :=
  row_sound5 row_318 row_318_valid

def row_338 : ℕ × List ℕ := (338, [127, 16256, 9767])

set_option maxHeartbeats 200000 in
theorem row_338_valid : RowData5 row_338 := by
  decide +kernel

theorem weight_338 : 338 ∈ weightsLe5 :=
  row_sound5 row_338 row_338_valid

def row_342 : ℕ × List ℕ := (342, [127, 16256, 11141, 15776])

set_option maxHeartbeats 200000 in
theorem row_342_valid : RowData5 row_342 := by
  decide +kernel

theorem weight_342 : 342 ∈ weightsLe5 :=
  row_sound5 row_342 row_342_valid

def row_346 : ℕ × List ℕ := (346, [127, 16256, 1906, 9586, 15748])

set_option maxHeartbeats 200000 in
theorem row_346_valid : RowData5 row_346 := by
  decide +kernel

theorem weight_346 : 346 ∈ weightsLe5 :=
  row_sound5 row_346 row_346_valid

def row_350 : ℕ × List ℕ := (350, [127, 16256, 11789, 1143])

set_option maxHeartbeats 200000 in
theorem row_350_valid : RowData5 row_350 := by
  decide +kernel

theorem weight_350 : 350 ∈ weightsLe5 :=
  row_sound5 row_350 row_350_valid

def row_354 : ℕ × List ℕ := (354, [127, 16256, 6757, 1143, 6764])

set_option maxHeartbeats 200000 in
theorem row_354_valid : RowData5 row_354 := by
  decide +kernel

theorem weight_354 : 354 ∈ weightsLe5 :=
  row_sound5 row_354 row_354_valid

def row_358 : ℕ × List ℕ := (358, [127, 16256, 9578, 9326, 4221])

set_option maxHeartbeats 200000 in
theorem row_358_valid : RowData5 row_358 := by
  decide +kernel

theorem weight_358 : 358 ∈ weightsLe5 :=
  row_sound5 row_358 row_358_valid

def row_366 : ℕ × List ℕ := (366, [127, 16256, 8072, 11787])

set_option maxHeartbeats 200000 in
theorem row_366_valid : RowData5 row_366 := by
  decide +kernel

theorem weight_366 : 366 ∈ weightsLe5 :=
  row_sound5 row_366 row_366_valid

def row_370 : ℕ × List ℕ := (370, [127, 16256, 5214, 9310, 11720])

set_option maxHeartbeats 200000 in
theorem row_370_valid : RowData5 row_370 := by
  decide +kernel

theorem weight_370 : 370 ∈ weightsLe5 :=
  row_sound5 row_370 row_370_valid

def row_374 : ℕ × List ℕ := (374, [127, 16256, 11172, 2291])

set_option maxHeartbeats 200000 in
theorem row_374_valid : RowData5 row_374 := by
  decide +kernel

theorem weight_374 : 374 ∈ weightsLe5 :=
  row_sound5 row_374 row_374_valid

def row_378 : ℕ × List ℕ := (378, [127, 16256, 11936])

set_option maxHeartbeats 200000 in
theorem row_378_valid : RowData5 row_378 := by
  decide +kernel

theorem weight_378 : 378 ∈ weightsLe5 :=
  row_sound5 row_378 row_378_valid

def row_382 : ℕ × List ℕ := (382, [127, 16256, 13985, 13960])

set_option maxHeartbeats 200000 in
theorem row_382_valid : RowData5 row_382 := by
  decide +kernel

theorem weight_382 : 382 ∈ weightsLe5 :=
  row_sound5 row_382 row_382_valid

def row_386 : ℕ × List ℕ := (386, [127, 16256, 15560, 6052])

set_option maxHeartbeats 200000 in
theorem row_386_valid : RowData5 row_386 := by
  decide +kernel

theorem weight_386 : 386 ∈ weightsLe5 :=
  row_sound5 row_386 row_386_valid

def row_390 : ℕ × List ℕ := (390, [127, 16256, 6938, 12379])

set_option maxHeartbeats 200000 in
theorem row_390_valid : RowData5 row_390 := by
  decide +kernel

theorem weight_390 : 390 ∈ weightsLe5 :=
  row_sound5 row_390 row_390_valid

def row_394 : ℕ × List ℕ := (394, [127, 16256, 4311, 11287, 14359])

set_option maxHeartbeats 200000 in
theorem row_394_valid : RowData5 row_394 := by
  decide +kernel

theorem weight_394 : 394 ∈ weightsLe5 :=
  row_sound5 row_394 row_394_valid

def row_398 : ℕ × List ℕ := (398, [127, 16256, 9395, 11145])

set_option maxHeartbeats 200000 in
theorem row_398_valid : RowData5 row_398 := by
  decide +kernel

theorem weight_398 : 398 ∈ weightsLe5 :=
  row_sound5 row_398 row_398_valid

/-- The full right-hand side, except the one explicitly unfilled value 362. -/
theorem historical_positive (w : ℕ)
    (hw : w = 254 ∨ w = 314 ∨ w = 318 ∨ (w % 4 = 2 ∧ 338 ≤ w ∧ w ≤ 398))
    (hne : w ≠ 362) : w ∈ weightsLe5 := by
  have hcases : w = 254 ∨ w = 314 ∨ w = 318 ∨ w = 338 ∨ w = 342 ∨ w = 346 ∨ w = 350 ∨ w = 354 ∨ w = 358 ∨ w = 366 ∨ w = 370 ∨ w = 374 ∨ w = 378 ∨ w = 382 ∨ w = 386 ∨ w = 390 ∨ w = 394 ∨ w = 398 := by
    omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact weight_254
  · exact weight_314
  · exact weight_318
  · exact weight_338
  · exact weight_342
  · exact weight_346
  · exact weight_350
  · exact weight_354
  · exact weight_358
  · exact weight_366
  · exact weight_370
  · exact weight_374
  · exact weight_378
  · exact weight_382
  · exact weight_386
  · exact weight_390
  · exact weight_394
  · exact weight_398

/-- This is a proved partial inclusion, not the frozen set equality. -/
theorem historical_subset :
    {w : ℕ | (w = 254 ∨ w = 314 ∨ w = 318 ∨
        (w % 4 = 2 ∧ 338 ≤ w ∧ w ≤ 398)) ∧ w ≠ 362} ⊆
      {w | w ∈ weightsLe5 ∧ w % 4 = 2 ∧ 250 ≤ w ∧ w ≤ 400} := by
  intro w hw
  change (w = 254 ∨ w = 314 ∨ w = 318 ∨
    (w % 4 = 2 ∧ 338 ≤ w ∧ w ≤ 398)) ∧ w ≠ 362 at hw
  obtain ⟨hspec, hne⟩ := hw
  refine ⟨historical_positive w hspec hne, ?_, ?_, ?_⟩ <;> omega

end Paper6RemarkWitnesses

#print axioms Paper6RemarkWitnesses.RowData5
#print axioms Paper6RemarkWitnesses.rowData5Decidable
#print axioms Paper6RemarkWitnesses.row_sound5
#print axioms Paper6RemarkWitnesses.row_254
#print axioms Paper6RemarkWitnesses.row_254_valid
#print axioms Paper6RemarkWitnesses.weight_254
#print axioms Paper6RemarkWitnesses.row_314
#print axioms Paper6RemarkWitnesses.row_314_valid
#print axioms Paper6RemarkWitnesses.weight_314
#print axioms Paper6RemarkWitnesses.row_318
#print axioms Paper6RemarkWitnesses.row_318_valid
#print axioms Paper6RemarkWitnesses.weight_318
#print axioms Paper6RemarkWitnesses.row_338
#print axioms Paper6RemarkWitnesses.row_338_valid
#print axioms Paper6RemarkWitnesses.weight_338
#print axioms Paper6RemarkWitnesses.row_342
#print axioms Paper6RemarkWitnesses.row_342_valid
#print axioms Paper6RemarkWitnesses.weight_342
#print axioms Paper6RemarkWitnesses.row_346
#print axioms Paper6RemarkWitnesses.row_346_valid
#print axioms Paper6RemarkWitnesses.weight_346
#print axioms Paper6RemarkWitnesses.row_350
#print axioms Paper6RemarkWitnesses.row_350_valid
#print axioms Paper6RemarkWitnesses.weight_350
#print axioms Paper6RemarkWitnesses.row_354
#print axioms Paper6RemarkWitnesses.row_354_valid
#print axioms Paper6RemarkWitnesses.weight_354
#print axioms Paper6RemarkWitnesses.row_358
#print axioms Paper6RemarkWitnesses.row_358_valid
#print axioms Paper6RemarkWitnesses.weight_358
#print axioms Paper6RemarkWitnesses.row_366
#print axioms Paper6RemarkWitnesses.row_366_valid
#print axioms Paper6RemarkWitnesses.weight_366
#print axioms Paper6RemarkWitnesses.row_370
#print axioms Paper6RemarkWitnesses.row_370_valid
#print axioms Paper6RemarkWitnesses.weight_370
#print axioms Paper6RemarkWitnesses.row_374
#print axioms Paper6RemarkWitnesses.row_374_valid
#print axioms Paper6RemarkWitnesses.weight_374
#print axioms Paper6RemarkWitnesses.row_378
#print axioms Paper6RemarkWitnesses.row_378_valid
#print axioms Paper6RemarkWitnesses.weight_378
#print axioms Paper6RemarkWitnesses.row_382
#print axioms Paper6RemarkWitnesses.row_382_valid
#print axioms Paper6RemarkWitnesses.weight_382
#print axioms Paper6RemarkWitnesses.row_386
#print axioms Paper6RemarkWitnesses.row_386_valid
#print axioms Paper6RemarkWitnesses.weight_386
#print axioms Paper6RemarkWitnesses.row_390
#print axioms Paper6RemarkWitnesses.row_390_valid
#print axioms Paper6RemarkWitnesses.weight_390
#print axioms Paper6RemarkWitnesses.row_394
#print axioms Paper6RemarkWitnesses.row_394_valid
#print axioms Paper6RemarkWitnesses.weight_394
#print axioms Paper6RemarkWitnesses.row_398
#print axioms Paper6RemarkWitnesses.row_398_valid
#print axioms Paper6RemarkWitnesses.weight_398
#print axioms Paper6RemarkWitnesses.historical_positive
#print axioms Paper6RemarkWitnesses.historical_subset
