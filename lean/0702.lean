import MIL.common
import mathlib
example {G : Type*} [Group G] {g : G} (h : g ^ 2 = 1) : g = g⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  rw[←pow_two]
  apply h


example {G : Type*} [Group G] (a b : G) (h : a * b = b * a⁻¹) : b * a = a⁻¹ * b := by
  rw[inv_mul_eq_of_eq_mul]
  rw[← mul_assoc, h, mul_assoc]
  rw[ mul_left_inv]
  rw[mul_one]

example {G : Type*} [Group G] {g : G} (h : g ^ 2 = g) : g = 1 := by
calc
  _ = g * g * g⁻¹ := by rw [mul_assoc, mul_right_inv, mul_one]
  _ = g ^ 2 * g⁻¹ := by rw [pow_two]
  _ = g * g⁻¹ := by rw [h]
  _ = _ := by rw[mul_right_inv]

example {G : Type*} [Group G] (a b a₁ a₂ : G) : (b * a * b⁻¹)⁻¹ = b * a⁻¹ * b⁻¹ ∧ (b * a₁ * b⁻¹) * (b * a₂ * b⁻¹) = b * a₁ * a₂ * b⁻¹ := by
  constructor
  · rw [conj_inv]
  · group

example {G : Type*} [Group G] (a b c : G) : ∃! x : G, a * x * b = c := by
  use (a⁻¹ * c * b⁻¹)
  constructor
  · group
  · intro h1 h2
    rw [← h2]
    group

example {G : Type*} [Group G] {x y : G} (h : (x * y) * (x * y) = (x * x) * (y * y)): x * y = y * x := by
  have lemma1 : x * y * x = x * x * y := by
    calc
    _ = (x * y) * (x * y) * y⁻¹ := by group
    _ = (x * x) * (y * y) * y⁻¹ := by rw [h]
    _ = _ := by group
  calc
    _ = x⁻¹ * (x * x * y) := by group
    _ = x⁻¹ * (x * y * x) := by rw[lemma1]
    _ = y * x := by group

example {G : Type*}[Group G]{a :G}: (a⁻¹)⁻¹=a:=by
  apply inv_inv


example {G : Type*} [Group G]: ∀ (g : G), ∃! (y : G), g * y = 1 := by
  intro g
  use g⁻¹
  constructor
  · apply mul_inv_self
  · intro h1 h2
    calc
      _ = g⁻¹ * (g * h1) := by group
      _ = g⁻¹ * 1 := by rw[h2]
      _ = _ := by group

example {G : Type*} [Group G]: ∃! (le : G), ∃! (re : G), ∀ (g : G), le * g = g ∧ g * re = g := by
  use 1
  constructor
  · use 1
    constructor
    · intro x
      constructor
      · apply one_mul
      · apply mul_one
    intro y h1
    -- h1 y <=> 1 * y = y ∧ y * y = y
    let h2 := (h1 y).2
    calc
      _ = y * y * y⁻¹ := by group
      _ = y * y⁻¹ := by rw [h2]
      _ = _ := by group
  · intro h1 h2
    rcases h2 with ⟨h3, h4, h5⟩
    let h6 := (h4 h1).1
    calc
      _ = h1 * h1 * h1⁻¹ := by group
      _ = h1 * h1⁻¹ := by rw[h6]
      _ = _ := by group










example {G : Type*} [Group G] {a b c : G} (h : a * b * c = 1) : b * c * a = 1 ∧ c * a * b = 1 := by
  constructor
  calc
    _ = b * c * (a * b * c) * (b * c)⁻¹ := by group
    _ = b * c * 1 * (b * c)⁻¹ := by rw[h]
    _ = _ := by  group
  calc
    _ = c * (a * b * c) * c⁻¹ := by group
    _ = c * 1 * c⁻¹ := by rw[h]
    _ = _ := by group

example {G : Type*}[Group G]{a b : G}:(a * b)⁻¹= b⁻¹ * a⁻¹ := by
apply mul_inv_rev

example {G : Type*} [Group G] (a b : G) : ((a * b)⁻¹ = a⁻¹ * b⁻¹ ↔ a * b = b * a) ∧ (a * b = b * a ↔ a * b * a⁻¹ * b⁻¹ = 1) := by
  constructor
  · constructor
    · intro h
      have h0 : a * b * (a⁻¹ * b⁻¹) * b * a = a * b := by group
      rw [← h0,←h]
      group
    · intro h
      rw [h]
      group
  · constructor
    · intro h
      rw [h]
      group
    · intro h
      calc
      _ = (a* b * a⁻¹ * b⁻¹) * b * a := by group
      _ = 1 * b * a := by rw[h]
      _ = _ := by group
