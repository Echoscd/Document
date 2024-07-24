import Mathlib
import Mathlib.Tactic
import Mathlib.Algebra.Group.MinimalAxioms
--1101B
def Func (S : Type*) := S → ℝ

instance (S : Type*) : Add (Func S) where
  add := by
    intro f g x
    exact f x + g x

instance (S : Type*) : Neg (Func S) where
  neg := by
    intro f x
    apply - f x

instance (S : Type*) : Zero (Func S) where
  zero := by
    intro x
    apply 0

noncomputable instance (S : Type*) : AddGroup (Func S) := by
  apply AddGroup.ofLeftAxioms
  · intro f g h
    funext x
    sorry
  · sorry
  · sorry
@[ext]
structure two_div_sum where
  x : ℤ
  y : ℤ
  h : 2 ∣ x + y

instance : Add two_div_sum where
  add := by
    intro h1 h2
    -- exact ⟨h1.x + h2.x, h1.y + h2.y, (by
    --   rw [← add_assoc, add_assoc h1.x, add_comm h2.x, ← add_assoc, add_assoc]
    --   sorry
    -- )⟩

    exact ⟨h1.x + h2.x, h1.y + h2.y, (by
      -- have := (Int.dvd_add_right h1.h).mpr h2.h
      convert (Int.dvd_add_right h1.h).mpr h2.h using 1
      ring
    )⟩

    -- --calculate the summation of the result
    -- have h5: 2 ∣ (h1.x + h1.y) + (h2.x + h2.y) := by
    --   let h3 := h1.h
    --   let h4 := h2.h
    --   exact (Int.dvd_add_right h3).mpr h4

    -- -- prove that the result is even
    -- have h6: 2 ∣  (h1.x + h2.x) + (h1.y + h2.y) := by

    --   --Using Interchangeability of the summation
    --   have h7 : (h1.x + h2.x) + (h1.y + h2.y)=(h1.x + h1.y) + (h2.x + h2.y) := by ring
    --   rw [h7]
    --   exact h5

    -- exact ⟨h1.x + h2.x, h1.y + h2.y, h6⟩


instance : Neg two_div_sum where
  neg := by
    intro h1
    --prove that $the negative is -(h1.x + h2.x)$ is even
    exact ⟨-h1.x, -h1.y, (by
      convert  Int.dvd_neg.mpr h1.h using 1
      ring
    )⟩


instance : Zero two_div_sum where
  --prove that (0,0) is the zero of the group
  zero := ⟨ 0, 0, (by
    exact Int.dvd_of_emod_eq_zero rfl
  )⟩

instance : AddGroup two_div_sum := by
  apply AddGroup.ofLeftAxioms
  --prove the vector $a,b,c$ satisfies $a + b + c = a + (b + c)$.
  · intro a b c
    ext
    · calc
        _= a.x + b.x + c.x := by rfl
        _= a.x + (b.x + c.x) := by rw[add_assoc]
        _=_ := by rfl
    · calc
        _= a.y + b.y + c.y := by rfl
        _= a.y + (b.y + c.y) := by rw[add_assoc]
        _=_ := by rfl
   --prove the vector $a$ satisfies $0 + a = a $.
  · intro a
    ext
    · calc
        _= 0 + a.x := by rfl
        _= a.x := by rw[zero_add]
        _=_ := by rfl
    · calc
        _= 0 + a.y := by rfl
        _= a.y := by rw[zero_add]
        _=_ := by rfl
  --prove the vector $a$ satisfies $-a + a = 0 $.
  · intro a
    ext
    · calc
        _ = -a.x + a.x := by rfl
        _ = 0 := by group
        _ = _ := by rfl
    · calc
        _ = -a.y + a.y := by rfl
        _ = 0 := by group
        _ = _ := by rfl
--1211B
example {G : Type*} [Group G] (h: ∀ (x : G), x * x = 1) : CommGroup G := by
  apply CommGroup.mk
  have h1: ∀ (x : G), x = x⁻¹ := by
    intro x
    calc
    _ = x * x * x⁻¹ := by group
    _ = 1 * x⁻¹ := by rw[h]
    _ = _ := by group
  intro a b
  calc
    _ = a⁻¹ * b⁻¹ := by
      rw[h1 a⁻¹ , h1 b⁻¹]
      group
    _ = (b * a)⁻¹ := by group
    _ = b * a := by rw[← h1 (b*a)]

--1214B
example {G : Type*} [Group G] {a b : G} : (a * b = 1)  ↔ (b * a = 1) := by
  constructor
  · intro h1
    have h0: b = a⁻¹ := by
      calc
        _ = a⁻¹ * (a * b) := by group
        _ = a⁻¹ * 1 := by rw[h1]
        _ = _ := by group
    calc
      _ = a⁻¹ * a := by rw[h0]
      _ = _ := by group
  · intro h2
    have h0: a = b⁻¹ := by
      calc
        _ = b⁻¹ * (b * a) := by group
        _ = b⁻¹ * 1 := by rw[h2]
        _ = _ := by group
    calc
      _ = b⁻¹ * b := by rw[h0]
      _ = _ := by group


example {G : Type*} [hG : Monoid G] (h: ∀ (g h : G), ∃! (x : G), x * g = h): Group G := {
  hG with
  inv := by sorry
  mul_left_inv := by sorry
}

example {G : Type*} [Monoid G] {g : G} (h: ∃ (li : G), li * g = 1): ∃! (ri: G), g * ri = 1 := by
  sorry

def mul_subgroup {G : Type*} [CommGroup G] (H₁ H₂ : Subgroup G) : Set G := {h| ∃ h₁ h₂ : G, h₁ ∈ H₁ ∧ h₂ ∈ H₂ ∧ h = h₁ * h₂}

example {G : Type*} [CommGroup G] (H₁ H₂ : Subgroup G) : Subgroup G where
  carrier := mul_subgroup H₁ H₂
  mul_mem' := by sorry
  one_mem' := by sorry
  inv_mem' := by sorry


example {G : Type*} [Monoid G] {g : G} (h₁: ∃ (li : G), li * g = 1) (h₂ : ∃ (ri : G), g * ri = 1) : ∃! (ri: G), g * ri = 1 := by
  rcases h₂ with ⟨r2, h2⟩
  rcases h₁ with ⟨r1, h1⟩
  use r2
  constructor
  · exact h2
  · intro x h3
    have h4 : x = r1 := by
      calc
        _ = 1 * x := by rw[one_mul]
        _ = r1 * g * x := by rw[h1]
        _ = r1 * (g * x) := by rw[mul_assoc]
        _ = r1 * 1 := by rw[h3]
        _ = _ := by rw[mul_one]
    have h5 : r2 = r1 := by
      calc
        _ = 1 * r2 := by rw[one_mul]
        _ = r1 * g * r2 := by rw[h1]
        _ = r1 * (g * r2) := by rw[mul_assoc]
        _ = r1 * 1 := by rw[h2]
        _ = _ := by rw[mul_one]
    rw[h4,h5]






def centre_carrier {G : Type*} [Group G] : Set G := { g | ∀ h : G, g * h = h * g }

def centre {G : Type*} [Group G]: Subgroup G where
  carrier := centre_carrier
  mul_mem' := by
    intro a b ha hb g
    -- set S := { g | property g }
    -- g ∈ S <=> property g
    have h3 : g * b = b * g := by
      rw [hb g]
    rw [mul_assoc,← h3, ← mul_assoc, ha g, mul_assoc]



  one_mem' := by sorry
  inv_mem' := by sorry

example {G : Type*} [Group G] : CommGroup (centre : Subgroup G) := by sorry

example {G : Type*} [Group G] : (centre : Subgroup G).Normal := by sorry
