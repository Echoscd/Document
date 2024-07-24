import Mathlib
variable {G : Type} [Group G]

#check Subgroup.center
#check QuotientGroup.mk'
example {G : Type*} [Group G] (h : IsCyclic (G ⧸ (Subgroup.center G))) : CommGroup G := by
  refine CommGroup.mk ?mul_comm
  intro a b
  rcases h with ⟨⟨h0⟩ ,h1⟩
  let a' := QuotientGroup.mk' (Subgroup.center G) a
  rcases (h1 a') with ⟨n,hn⟩
  dsimp at hn
  let h0g := Quotient.out' h0
  have a_pow : (h0g^n)⁻¹ * a ∈ (Subgroup.center G) := by
    apply QuotientGroup.eq'.mp
    change _ = a'
    rw [← hn]

open Equiv.Perm
theorem bezout_theorem (a b : ℕ) (h: (a ≠ 0) ∨ (b ≠ 0)) : ∃ x y : ℤ, a * x + b * y = gcd a b := by
  let d := gcd a b
  have d_non_zero : gcd a b ≠ 0 := by
    intro h1
    have a_eq_0: a = 0 := by
      exact eq_zero_of_gcd_eq_zero_left
    have b0: b = 0 := by
      exact eq_zero_of_gcd_eq_zero_right
