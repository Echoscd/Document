import Mathlib
import Mathlib.Tactic
import Mathlib.Algebra.Group.MinimalAxioms
--2203B
def unit_subgroup {G : Type*} [CommGroup G] : Set G := { s | s ^ 2 = 1 }

example {G : Type*} [CommGroup G] : Subgroup G where
  --Define the multiple of the subgroup and verify that the result is in the subgroup
  carrier := unit_subgroup
  mul_mem' := by
    intro a b ha hb
    --Verify the result is in unit subgroup by calculate $(a * b) \^ 2$.
    have : (a * b) * (a * b) = 1  := by
      calc
        --Since $G$ is commutative, we can change the order of product
        _ = (a * a) * (b * b) := by exact mul_mul_mul_comm a b a b
        _ = 1 * 1 := by
          --Using the condition and the definition of the unit subgroup
          unfold unit_subgroup at ha hb
          dsimp at ha hb
          rw [← pow_two,← pow_two]
          rw [ha, hb]
        _ = _ := by exact LeftCancelMonoid.one_mul 1
    unfold unit_subgroup
    dsimp
    rw [ pow_two]
    apply this
  -- Verify that 1 is in the subgroup
  one_mem' := by
    unfold unit_subgroup
    dsimp
    exact one_pow 2
  -- Verify the inverse is in the subgroup
  inv_mem' := by
    unfold unit_subgroup
    dsimp
    intro h h1
    calc
      _ = h⁻¹ * h⁻¹ := by rw[pow_two]
      _ = (h * h)⁻¹ := by group
      _ = (h ^ 2)⁻¹ := by rw[←pow_two]
      _ = 1⁻¹ := by rw [h1]
      _ = _ := by group

--1409B
example {G : Type*} [Group G] (a b : G) : orderOf a = orderOf (b * a * b⁻¹) := by
  refine orderOf_eq_orderOf_iff.mpr ?_
  sorry
