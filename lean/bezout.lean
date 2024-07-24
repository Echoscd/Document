import mathlib
#check Nat.gcd_zero_right
theorem bezout_theorem_of_one (n: ℕ ) : ∀ a b : ℕ , a + b = n  → gcd a b = 1 →  ∃ x y : ℤ , a * x + b * y = 1 := by
  induction' n using Nat.strong_induction_on with n hn
  intro a b habn coprime
  by_cases hab : a > b
  · by_cases zerob : b = 0
    · have : a ≠ 0 := by exact Nat.not_eq_zero_of_lt hab
      have : a = 1 := by
        rw[← Nat.gcd_zero_right a]
        rw[← zerob]
        exact coprime
      use 1,0
      rw[this, zerob]
      norm_num
    · have a_le : a - b < a := by
        have : b > 0 := by exact Nat.zero_lt_of_ne_zero zerob
        omega
      have a_eq : (a - b) + b = a:= by
        apply Nat.sub_add_cancel
        exact Nat.le_of_succ_le hab
      have a_le_n : a < n := by
        omega
      have b_leq_a : b ≤ a := by
        exact Nat.le_of_succ_le hab
      have hgcd : gcd (a - b) b = 1 := by
        calc
          _ = gcd a b := by
            apply Nat.gcd_sub_self_left b_leq_a
          _ = _ := by exact coprime
      rcases hn a a_le_n (a - b) b a_eq hgcd with ⟨x0 ,⟨ y0, hy⟩⟩
      use x0, y0-x0
      calc
        _ = ((a : ℤ) - (b : ℤ)) * x0 + (b : ℤ) * y0 := by ring
        _ = (((a - b) : ℕ)  : ℤ) * x0 + (b : ℤ) * y0 := by
          congr 2
          rw [Int.ofNat_sub b_leq_a]
        _ = _ := by rw[hy]
  sorry

theorem bezout_theorem (a b : ℕ) (h: (a ≠ 0) ∨ (b ≠ 0)) : ∃ x y : ℤ, a * x + b * y = gcd a b := by
  let d := gcd a b
  have d_non_zero : gcd a b ≠ 0 := by
    intro h1
    have ab_eq_zero:(a = 0) ∧ (b = 0) := by
       exact Nat.gcd_eq_zero_iff.mp h1
    have : ¬ ((a = 0) ∧ (b = 0)) := by
      exact (Decidable.not_and_iff_or_not (a = 0) (b = 0)).mpr h
    exact this ab_eq_zero
  let a' := a / d
  have a_mul : d * a' = a := by
    refine Nat.mul_div_cancel' ?H
    exact gcd_dvd_left a b
  let b' := b / d
  have b_mul : d * b' = b := by
    apply Nat.mul_div_cancel'
    exact gcd_dvd_right a b
  have dtimes : d * (gcd a' b')  = d := by
    calc
      _ = gcd (d * a') (d * b') := by
        rw[gcd_mul_left d a' b']
        dsimp
        norm_num
      _ = gcd a b := by rw[a_mul, b_mul]
      _ = d := by simp
  have coprime : gcd a' b' = 1 := by
    exact (Nat.mul_eq_left d_non_zero).mp dtimes
  rcases bezout_theorem_of_one (a' + b') a' b' (by norm_num) coprime with ⟨x0, ⟨y0,hxy⟩⟩
  use x0, y0
  have d_eq_ab :d = gcd a b := by simp
  nth_rw 1 [← a_mul, ← b_mul, ← d_eq_ab]
  calc
    _ = d * (a' * x0 + b' * y0) := by
      sorry
    _ = d * 1 := by rw[hxy]
    _ = _  := by norm_num
