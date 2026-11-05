import Research.Backfill.Paper7.C61ThreeUnitWitness

/-! NEW SOURCE ONLY. Definitional rewrites for fixed six-cycle indices. -/
set_option autoImplicit false
namespace Paper7C61FourIndex

@[simp]
theorem add_one_zero : (0 : Fin 6) + 1 = 1 := rfl
#print axioms Paper7C61FourIndex.add_one_zero
@[simp]
theorem add_one_one : (1 : Fin 6) + 1 = 2 := rfl
#print axioms Paper7C61FourIndex.add_one_one
@[simp]
theorem add_one_two : (2 : Fin 6) + 1 = 3 := rfl
#print axioms Paper7C61FourIndex.add_one_two
@[simp]
theorem add_one_three : (3 : Fin 6) + 1 = 4 := rfl
#print axioms Paper7C61FourIndex.add_one_three
@[simp]
theorem add_one_four : (4 : Fin 6) + 1 = 5 := rfl
#print axioms Paper7C61FourIndex.add_one_four
@[simp]
theorem add_one_five : (5 : Fin 6) + 1 = 0 := rfl
#print axioms Paper7C61FourIndex.add_one_five
@[simp]
theorem add_five_zero : (0 : Fin 6) + 5 = 5 := rfl
#print axioms Paper7C61FourIndex.add_five_zero
@[simp]
theorem add_five_one : (1 : Fin 6) + 5 = 0 := rfl
#print axioms Paper7C61FourIndex.add_five_one
@[simp]
theorem add_five_two : (2 : Fin 6) + 5 = 1 := rfl
#print axioms Paper7C61FourIndex.add_five_two
@[simp]
theorem add_five_three : (3 : Fin 6) + 5 = 2 := rfl
#print axioms Paper7C61FourIndex.add_five_three
@[simp]
theorem add_five_four : (4 : Fin 6) + 5 = 3 := rfl
#print axioms Paper7C61FourIndex.add_five_four
@[simp]
theorem add_five_five : (5 : Fin 6) + 5 = 4 := rfl
#print axioms Paper7C61FourIndex.add_five_five

end Paper7C61FourIndex
