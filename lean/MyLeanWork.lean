import Mathlib

-- S01 Suppose that $G$ is a group and $a, b \in G$ satisfy $a * b=b * a^{-1}$. Prove that $b * a=a^{-1} * b$.
example {G : Type*} [Group G] (a b : G) (h : a * b = b * a⁻¹) : b * a = a⁻¹ * b := by
  rw[inv_mul_eq_of_eq_mul]
  rw[← mul_assoc, h, mul_assoc]
  rw[ mul_left_inv]
  rw[mul_one]

--S02 Suppose that $G$ is a group, $g \in G$, and suppose that $g^{2}=e$. Prove that $g=g^{-1}$.
example {G : Type*} [Group G] {g : G} (h : g ^ 2 = 1) : g = g⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  rw[←pow_two]
  apply h

--S03 Suppose that $G$ is a group, $g \in G$, and suppose that $g^{2}=g$. Prove that $g$ is the identity.
example {G : Type*} [Group G] {g : G} (h : g ^ 2 = g) : g = 1 := 
calc
  _ = g * g * g⁻¹ := by rw [mul_assoc, mul_right_inv, mul_one]
  _ = g ^ 2 * g⁻¹ := by rw [pow_two]
  _ = g * g⁻¹ := by rw [h]
  _ = _ := by rw[mul_right_inv]

--S04 Suppose that $G$ is a group and $a, b,a_1,a_2 \in G$. Prove that $(bab^{-1})^{-1}=ba^{-1}b^{-1}$ and $(ba_1b^{-1})(ba_2b^{-1})=ba_1a_2b^{-1}$.
example {G : Type*} [Group G] (a b a₁ a₂ : G) : (b * a * b⁻¹)⁻¹ = b * a⁻¹ * b⁻¹ ∧ (b * a₁ * b⁻¹) * (b * a₂ * b⁻¹) = b * a₁ * a₂ * b⁻¹ := by
  constructor
  · rw [conj_inv]
  · group

--S05 Suppose that $G$ is a group and $a, b, c\in G$. Prove that $a * x * b=c$ has a unique solution.
example {G : Type*} [Group G] (a b c : G) : ∃! x : G, a * x * b = c := by
  use (a⁻¹ * c * b⁻¹)
  constructor
  · group
  · intro h1 h2 
    rw [← h2]
    group

--S06 Given an nature number $n$ which is not less than 2, prove either it is a prime or it can be divided by a prime nature number.
-- Definition of theorem two_le stating that for any natural number m, if m is not 0 and not 1, then 2 ≤ m.
theorem two_le {m : ℕ} (h0 : m ≠ 0) (h1 : m ≠ 1) : 2 ≤ m :=
  by
    -- Induction on m
    induction' m with m ih
    -- Case: m = 0, contradiction with h0 (m ≠ 0)
    · exact False.elim (h0 rfl)  
    · cases' m with e
      -- Case: m = 1, contradiction with h1 (m ≠ 1)
      · exact False.elim (h1 rfl)  
      -- Case: m = e + 2, where e is a natural number
      · exact Nat.le_add_left 2 e  


-- Example demonstrating that if 2 ≤ n, then there exists a prime number p
-- such that p divides n.
example {n : Nat} (h : 2 ≤ n) : ∃ p : Nat, p.Prime ∧ p ∣ n :=
  by
    -- Induction on n using strong induction
    induction' n using Nat.strong_induction_on with n hn
    -- Case distinction on whether n is prime or not
    by_cases np : n.Prime
    -- Case: n is prime, use n itself as the prime number p
    · use n  
    · rw[Nat.prime_def_lt] at np
      push_neg at np
      rcases np h with ⟨m, ⟨mltn, ⟨mdvdn, mnel⟩⟩⟩
      -- Showing m ≠ 0 to use the fact that n is not prime
      have : m ≠ 0 := by
        intro mz
        rw[mz, zero_dvd_iff] at mdvdn
        linarith
      -- Applying the theorem two_le to establish 2 ≤ m
      have mge2 : 2 ≤ m := two_le this mnel
      -- Applying the induction hypothesis to find a prime p that divides m
      rcases hn m mltn mge2 with ⟨p, ⟨pprime, pdivm⟩⟩
      -- Using p as the prime number that divides n
      use p
      constructor
      · exact pprime
      · exact Nat.dvd_trans pdivm mdvdn

--S08 H is a normal group of G iff for all h ∈ H, g ∈ G, we have g⁻¹ * h * g ∈ H. Because G is commutative, g * n * g⁻¹ = g * g⁻¹ * n = n ∈ H .
example {G : Type*} [CommGroup G] (H: Subgroup G) : H.Normal := by 
  --  H is a normal group of G iff for all h ∈ H, g ∈ G, we have g⁻¹ * h * g ∈ H.
  refine { conj_mem := ?conj_mem }
  intro n hn g
  --Because G is commutative, g * n * g⁻¹ = g * g⁻¹ * n = n ∈ H .
  have : g * n * g⁻¹ = n := by
    calc
      _ = n * g * g⁻¹ := by rw[mul_comm g n]
      _ = n := by group
  rw[this]
  exact hn

--S09 Let $R$ be a ring in which $x^{3}=x$ for every $x \in R$. Prove that $R$ is commutative.
example {R: Type*} [Ring R] (a b : R) (hR: ∀ x : R, x ^ 3 = x) : a * b = b * a := by
  -- First we prove (1) $\mathrm{ab}=0 \Rightarrow \mathrm{ba}=0$ via $\mathrm{ba}=(\mathrm{ba})^3=\mathrm{bababa} =0$
  have zero_comm : ∀ a b : R, a * b = 0 → b * a = 0 := by
    intro a b hab
    calc
      _ = (b * a) ^ 3 := by rw[ hR (b * a)]
      _ = (b * a) * (b * a) * (b * a) := by exact pow_three' (b * a)
      _ = b * (a * b) * (a * b) * a := by group
      _ = b * 0 * 0 * a := by rw[hab]
      _ = _ := by simp only [mul_zero, zero_mul]
  --(2) $\mathrm{c}^2=\mathrm{c} \Rightarrow \mathrm{c}$ is central [which means that $\mathrm{xc}=\mathrm{cx}$ for all x .
  have nil_central : ∀ c x: R, c * c = c → x * c = c * x := by
    intro c x hc
     --$c(x-c x)=0 \Rightarrow(x-c x) c=0$ by (1), so $\mathrm{xc}=\mathrm{cxc}$
    have lhs: x * c = c * x * c := by
      have : (x - c * x) * c = 0 := by
        apply zero_comm 
        calc
          _ = c * x - c * c * x := by 
            rw[mul_sub_left_distrib, mul_assoc]
          _ = c * x - c * x := by rw[hc]
          _ = _ := by exact sub_eq_zero_of_eq rfl
      apply eq_of_sub_eq_zero
      rw[← this]
      exact Eq.symm (sub_mul x (c * x) c)
    --$(x-x c) c=0 \Rightarrow c(x-x c)=0$ by $(1)$, so $\mathrm{cx}=\operatorname{cxc}$
    have rhs: c * x = c * x * c := by
      have : c * (x - x * c) = 0 := by
        apply zero_comm
        calc
          _ = x * c - x * (c * c) := by rw[mul_sub_right_distrib, mul_assoc]
          _ = x * c - x * c := by rw[hc]
          _ = 0 := by exact sub_eq_zero_of_eq rfl
      apply eq_of_sub_eq_zero
      rw[← this]
      calc
        _ = c * x - c * (x * c) := by rw[mul_assoc]
        _ = _ := by exact Eq.symm (mul_sub_left_distrib c x (x * c))
    rw[lhs]
    nth_rw 2 [rhs]
  --(3) $\mathrm{x}^2$ central via $\mathrm{c}=\mathrm{x}^2$ in (2)
  have sqr_central : ∀ x b : R, b * (x * x) = (x * x) * b := by
    intro x b
    apply nil_central
    rw[← mul_assoc]
    congr 1
    rw[← pow_three']
    exact hR x
  --(4) $\mathrm{c}^2=2 \mathrm{c} \Rightarrow \mathrm{c}$ central. Proof: $\mathrm{c}=\mathrm{c}^3=2 \mathrm{c}^2$ central by (3)
  have two_central : ∀ c x :R , c * c = 2 * c → x * c = c * x := by
    intro c x hc
    calc
      _ = (x * (c * c * c)) := by 
        nth_rw 1 [← hR c, pow_three,mul_assoc]
      _ = x * (2 * c * c) := by rw[hc]
      _ = x * 2 * c * c := by group
      _ = 2 * x * c * c := by 
        congr 2
        rw[two_mul,mul_two]
      _ = 2 * (x * (c * c)) := by group
      _ = 2 * (c * c * x) := by rw[sqr_central c x]
      _ = (2 * c) * c * x := by group
      _ = c * c * c * x := by rw[hc]
      _ = _ := by rw[← pow_three', hR c]
  --(5) $\mathrm{x}+\mathrm{x}^2$ central via $\mathrm{c}=\mathrm{x}+\mathrm{x}^2$ in (4)
  have plus_central : ∀ c x : R, c * (x * x + x) = (x * x + x) * c := by
    intro c x 
    apply two_central
    calc
      _ = x * x * x * x + x * x * x + x * x * x + x * x := by
        simp only [add_mul]
        rw[mul_add]
        rw[mul_add]
        rw[← add_assoc]
        congr 1
        congr 1
        congr 1
        exact IsJordan.lmul_lmul_comm_rmul x x
        exact sqr_central x x
      _ = _ := by 
        rw[←pow_three', hR x]
        rw[two_mul]
        abel
  --(6) $\mathrm{x}=\left(\mathrm{x}+\mathrm{x}^2\right)-\mathrm{x}^2$ central via (3),(5) by centrals closed under subtraction. QED
  calc
    _ = ( a * a + a - a * a) * b := by 
      congr 1
      abel
    _ = (a * a + a) * b - a * a * b := by exact sub_mul (a * a + a) (a * a) b
    _ = b * (a * a + a) - b * (a * a) := by 
      rw[plus_central b a, sqr_central a b]
    _ = b * (a * a + a - a * a) := by exact Eq.symm (mul_sub_left_distrib b (a * a + a) (a * a))
    _ = _ := by 
      congr 1
      abel

--S10 We know that $\log : \mathbb{R}^{+} \rightarrow \mathbb{R}$ is a group homomorphism; see Example 22.4. Find a subgroup $G$ of $\mathbb{R}^{+}$, so that the restricted logarithm function maps $G$ onto the subgroup $\mathbb{Z}$ of $\mathbb{R}$. What about a subgroup of $\mathbb{R}^{+}$that maps onto the subgroup $\mathbb{Q}$ of $\mathbb{R}$ ?
-- First, we define the multiplicative group of the ℝ+.
def Reals_pos : Set ℝ := {x : ℝ |  0 < x}
noncomputable instance : Group Reals_pos where
  -- The group multiple is exactly the multiple of real number.
  mul := by
    intro x y
    use x.1 * y.1
    exact Real.mul_pos x.2 y.2
  mul_assoc := by
    intro a b c
    apply Subtype.val_inj.1
    show a.1 * b.1 * c.1 = a.1 * (b.1 * c.1)
    rw [mul_assoc]
  one := by
    use 1
    exact Real.zero_lt_one 
  one_mul := by
    intro a
    apply Subtype.val_inj.1
    show 1 * a.1 = a.1 
    exact one_mul (a : ℝ)
  mul_one := by
    intro a
    apply Subtype.val_inj.1
    show a.1 * 1 = a.1
    exact mul_one (a : ℝ)
  inv := by
    intro a
    use 1 / a.1
    unfold Reals_pos
    dsimp
    apply one_div_pos.2 
    exact a.2
  mul_left_inv := by
    intro a
    apply Subtype.val_inj.1
    
    have :(1 /(a.1)) * a.1 = 1:= by 
      apply one_div_mul_cancel
      apply @ne_of_gt ℝ _ a.1 0 a.2
    exact this

-- Then we define the homomorphism from ℝ+ to ℝ by log. 
noncomputable def loghom : Reals_pos →* Multiplicative ℝ where
  toFun := by
    intro x
    apply Real.log x.1
  map_one' := by
    apply Real.log_one
  map_mul' := by
    simp
    intro a apos b bpos
    apply Real.log_mul
    · simp
      apply ne_of_gt (α :=ℝ) apos
    · apply ne_of_gt (α :=ℝ) bpos
-- Define expZ := {exp x | x ∈ ℤ} as a subgroup of positive real number.
noncomputable def expZ : Subgroup Reals_pos where
  carrier := {Real.exp x | x : ℤ}
  mul_mem' := by
    intro a b ⟨ea, hea⟩ ⟨eb, heb⟩ 
    use ea + eb
    have :(a * b).1 = a.1 * b.1 := by rfl
    rw[this, ←hea, ←heb]
    rw[← Real.exp_add]
    congr
    exact Int.cast_add ea eb
  one_mem' := by
    simp
  inv_mem' := by
    simp
    intro a apos x hexp
    use (-x)
    simp
    rw[Real.exp_neg]
    rw[hexp]
    conv_rhs => dsimp [·⁻¹]
    field_simp
-- Define expQ := {exp x | x ∈ ℚ} as a subgroup of positive real number.
noncomputable def expQ : Subgroup Reals_pos where
  carrier := {Real.exp x | x : ℚ}
  mul_mem' := by
    intro a b ⟨ea, hea⟩ ⟨eb, heb⟩ 
    use ea + eb
    have :(a * b).1 = a.1 * b.1 := by rfl
    rw[this, ←hea, ←heb]
    rw[← Real.exp_add]
    congr
    exact Rat.cast_add ea eb
  one_mem' := by
    simp
  inv_mem' := by
    simp
    intro a apos x hexp
    use (-x)
    simp
    rw[Real.exp_neg]
    rw[hexp]
    conv_rhs => dsimp [·⁻¹]
    field_simp
-- We prove that the loghom maps the subgroup expZ to ℤ.
example : loghom '' expZ = {x : ℝ | ∃ z : ℤ, (z : ℝ) = x} := by
  ext x
  constructor
  · intro h
    dsimp
    rcases h with ⟨h1,⟨⟨z0,hz⟩,h3⟩⟩
    use z0
    rw[← h3]
    show (z0: ℝ) = Real.log h1
    rw[← hz]
    exact Eq.symm (Real.log_exp ↑z0)
  · intro ⟨z, hz⟩ 
    simp
    rw[← hz]
    use Real.exp z
    have h : Real.exp (z : ℝ) ∈ Reals_pos := by
      unfold Reals_pos
      dsimp
      exact Real.exp_pos (z : ℝ)
    use h
    constructor
    · use z
    · apply Real.log_exp

-- Finally we prove that the loghom maps the subgroup expQ to ℚ.
example : loghom '' expQ = {x : ℝ | ∃ z : ℚ, (z : ℝ) = x} := by
  ext x
  constructor
  · intro h
    dsimp
    rcases h with ⟨h1,⟨⟨z0,hz⟩,h3⟩⟩
    use z0
    rw[← h3]
    show (z0: ℝ) = Real.log h1
    rw[← hz]
    exact Eq.symm (Real.log_exp ↑z0)
  · intro ⟨z, hz⟩ 
    simp
    rw[← hz]
    use Real.exp z
    have h : Real.exp (z : ℝ) ∈ Reals_pos := by
      unfold Reals_pos
      dsimp
      exact Real.exp_pos (z : ℝ)
    use h
    constructor
    · use z
    · apply Real.log_exp

-- S11 Let $1\rightarrow H\overset{i}{\rightarrow} G\overset{p}{\rightarrow}P\rightarrow1$ be a sequence of homomorphism of groups where $1$ stands for the trivial group. Assume that $H,G$ and $P$ are all finite groups and the sequence is exact at $H,G$ and $P$. Prove that $|G|=|H||P|$.
open Set
open Polynomial List Nat Sylow Fintype Setoid Classical
open Subgroup MonoidHom

#synth Group Unit

example {H G P: Type*} [Fintype G][Fintype H][Fintype P][Group G] [Group H] [Group P](to_H : Unit →* H) (i : H →* G) (p : G →* P)  (to_T : P →* Unit) (exact_H : i.ker = to_H.range) (exact_G : p.ker = i.range) (exact_P: to_T.ker = p.range): card G = card H * card P:= by
  -- First we prove that p is surjective, using the fact that the sequence is exact at P.
  have surjp : Function.Surjective p:= by
    refine range_top_iff_surjective.mp ?_
    rw[← exact_P]
    refine (eq_top_iff' to_T.ker).mpr ?_
    intro x
    refine (mem_ker to_T).mpr ?_
    apply Unit.ext
  -- Then we prove that i is injective, using the fact that the sequence is exact at H.
  have inji : Function.Injective i:= by
    refine (ker_eq_bot_iff i).mp ?_
    rw [exact_H]
    exact eq_bot_of_card_eq to_H.range rfl
  -- Since i is injective, the range of i is exactly H.
  have h1 : card H = card (i.range):= by
    exact Eq.symm (card_range_of_injective inji)
  rw [h1]
  -- Using the first fundamental homomorphism theorem at G and the homomorphism p. 
  have card_ker_range : card (G ⧸ p.ker) = card P := by
    apply Fintype.card_congr
    exact (QuotientGroup.quotientKerEquivOfSurjective p surjp).toEquiv
  -- Using the Lagrange's theorem at G.
  have : card (G ⧸ p.ker) * card (p.ker) = card G := by
    exact Eq.symm (card_eq_card_quotient_mul_card_subgroup p.ker)
  rw[← this, card_ker_range]
  simp_rw[exact_G]
  rw[mul_comm]

--S12 Consider subgroups $G_{1}, G_{2}$ of a group $G$. If $G$ is abelian, why is $G_{1} G_{2}$ a subgroup?
--Define the product of two subgroup as G := { s | ∃ h : H, ∃ k : K, s = h * k } 
def HK {G : Type*} [Group G] (H K: Subgroup G) : Set G := { s | ∃ h : H, ∃ k : K, s = h * k }

def product_comm {G : Type*} [CommGroup G] (H K: Subgroup G) : Subgroup G where
  carrier := HK H K
  --Show that the product of any two elements are still in the group.
  mul_mem' := by
    intro a b ha hb
    -- Take two elements as xa*ya and xb*yb, then xa*ya*xb*yb = (xa*xb)*(ya*yb) is still in HK.
    rcases ha with ⟨xa,ya,hxya⟩
    rcases hb with ⟨xb,yb,hxyb⟩ 
    rw[hxya, hxyb]
    use xa*xb, ya*yb
    dsimp
    group
    rw[mul_assoc (xa: G), mul_comm (ya : G),← mul_assoc]
  -- Also 1 = 1 * 1 is in the subgroup.
  one_mem' := by
    dsimp
    use 1,1 
    dsimp
    group
  -- The inverse of a member (a * b) ⁻¹ = a⁻¹ * b⁻¹ is is still in the subgroup HK.
  inv_mem' := by
    intro x hx
    dsimp
    dsimp at hx
    rcases hx with ⟨a,b,hab⟩ 
    use a⁻¹, b⁻¹ 
    rw[hab]
    dsimp
    exact mul_inv (a : G) (b : G)

-- S13 Verify that $\mathscr{F}(\mathbb{R})$ satisfies all the axioms for being a commutative ring with unity. Indicate the zero and unity, and describe the negative of any $f$.

-- Describe the divisors of zero in $\mathscr{F}(\mathbb{R})$.
-- Describe the invertible elements in $\mathscr{F}(\mathbb{R})$.
--Here we define the ring structure on ℝ → ℝ.
noncomputable instance : Ring (ℝ → ℝ) where
  add := by
    intro a b
    exact a + b
  add_assoc := by
    intro a b c
    group
  zero := by
    intro x
    exact 0
  zero_add := by
    intro a
    group
  add_zero := by
    intro a 
    group
  nsmul := by
    intro n a x
    exact n * (a x)
  nsmul_zero := by
    intro x
    simp
    rfl 
  nsmul_succ := by
    intro x y
    ext a
    dsimp
    push_cast
    rw[add_mul]
    refine add_left_cancel_iff.mpr ?h.a
    group
  add_comm := by
    intro x y 
    group
  mul := by
    intro x y z
    exact x z * y z
  left_distrib := by
    intro a b c
    ring
  right_distrib := by
    intro a b c 
    ring
  zero_mul := by
    intro a
    group
  mul_zero := by
    intro a
    group
  mul_assoc := by
    intro a b c
    ring
  one := by
    intro a
    exact 1
  one_mul := by
    intro a
    group
  mul_one := by
    intro a
    group
  natCast := by
    intro n a
    exact (n : ℝ)
  natCast_zero := by
    ext x
    dsimp
    group
  natCast_succ := by
    intro n
    ext x
    dsimp
    push_cast
    rfl
  npow := by
    intro n x
    intro a
    exact (x a) ^ n
  npow_zero := by
    intro f
    ext x
    rfl
  npow_succ := by
    intro n f
    ext x
    dsimp
    exact rfl
  neg := by
    intro x a
    exact -x a
  sub := by
    intro f g x
    exact f x - g x
  sub_eq_add_neg := by
    intro a b
    ext x
    show  a x - b x = a x + (-b) x
    rfl
  zsmul := by
    intro z f x
    exact z * f x 
  zsmul_zero' := by
    intro f
    ext x
    push_cast
    simp
  zsmul_succ' := by
    intro n f 
    ext x
    dsimp
    push_cast
    rw[add_mul]
    rw[one_mul]
  zsmul_neg' := by
    intro n f
    ext x
    dsimp
    simp
    rw[← neg_add, add_comm] 
    symm
    apply neg_mul_eq_neg_mul ((n : ℝ) + 1) (f x)
  add_left_neg := by
    intro a
    ring
  intCast := by
    intro z x
    exact (z : ℝ)
  intCast_ofNat := by
    intro n
    simp
  intCast_negSucc := by
    intro n
    simp
-- The zero divisor of this ring is the functions which map some x to zero.
def Zero_divisor := {f : ℝ → ℝ| ∃  g : ℝ → ℝ, g ≠ 0 ∧  f * g = 0}
example : f ∈ Zero_divisor ↔ ∃  x : ℝ,  f x = 0 := by
  constructor
  -- If f is a zero divisor, then ∃ g ≠ 0 such that f * g =0 .
  · intro ⟨g, hg⟩  
  -- Since g is not a zero map, there exists x0 such that g(x0) ≠ 0.
    have gneq : ∃ x : ℝ, g x ≠  0 := by
      by_contra h
      push_neg at h
      have : g = 0 := by
         ext x
         exact h x
      exact hg.1 this 
    rcases gneq with ⟨x0, gx0⟩ 
    use x0
  -- Also we know that f(x0) * g(x0) = 0, so f(x0) = 0.
    have :f x0 * g x0 = 0 := by
      show (f * g) x0 = 0
      rw[hg.right]
      rfl
    exact eq_zero_of_ne_zero_of_mul_right_eq_zero gx0 this
  --On the other hand, if f(x0)=0,
  · intro h 
    rcases h with ⟨x0, hx⟩ 
  --We can construct g such that g(x0) = 1 and g(x) = 0 for all x ≠ x0.
    let g : ℝ → ℝ := by
      intro x
      by_cases (x = x0)
      exact 1
      exact 0
    use g
    constructor
    --This g is obviously nonzero,
    · have : ∃ x : ℝ , g x ≠ 0 := by
        use x0
        have:  g x0 = 1 := by 
          exact (Ne.dite_eq_left_iff fun h a => h rfl).mpr rfl
        rw[this]
        exact Ne.symm (zero_ne_one' ℝ)
      exact Function.support_nonempty_iff.mp this
      -- and f x * g x = 0 for all x ∈ ℝ.
    · ext x
      show f x * g x = 0
      by_cases h: x = x0 
      · rw[h]
        rw[hx]
        group
      · suffices: g x = 0
        · rw[this]
          group
        · exact (Ne.dite_eq_right_iff fun h_1 a => h h_1).mpr h
      
-- Then we prove that the invertible elements are those f without zero point.
def Invert := {f :ℝ → ℝ | ∃ g : ℝ → ℝ, f * g = 1}  
example : f ∈ Invert ↔ ∀ x : ℝ, f x ≠ 0 := by
  constructor
  --First if f is invertible, and for all x, f(x) * g(x) = 1, so f(x) ≠ 0.
  · intro ⟨g,hg⟩  x
    intro hf
    have mul_zero: f x * g x = 1 := by
      show (f * g) x = 1
      rw[hg]
      rfl
    have mul_one: f x * g x = 0 := by
      rw[hf]
      group
    have : ¬ f x * g x = 0 := by
      exact ne_zero_of_eq_one mul_zero
    exact this mul_one
  --On the other hand, if f doesn't have zero point, then g(x) = f(x)⁻¹ is well defined, so f * g = 1.
  · intro hf
    use (fun x ↦ (f x)⁻¹ )
    ext x
    simp
    exact CommGroupWithZero.mul_inv_cancel (f x) (hf x)

-- S14 A subgroup $N$ of a group $G$ with index $2$ must be a normal subgroup of $G$.

-- Applying a theorem from group theory: index_eq_two_iff
example {G : Type*} [Group G] (N: Subgroup G) (h₁: N.index = 2) : N.Normal := by
  apply Subgroup.index_eq_two_iff.mp at h₁
  rcases h₁ with ⟨a, ha⟩
  refine { conj_mem := ?intro.conj_mem }
  intro n hn g
  let h3 := ha g
  rcases h3 with ⟨h4,h5⟩  | ⟨h4,h5⟩
  · have h7 : a ∉ N := by
      intro h1
      have : g ∈ N := by exact (Subgroup.mul_mem_cancel_right N h1).mp h4
      exact h5 this
    have a_inv: a⁻¹ ∉ N := by
      intro h1
      have : a ∈ N := by exact (Subgroup.inv_mem_iff N).mp h1
      exact h7 this
    have h6 : a⁻¹ * n ∉ N := by
      have : n⁻¹ ∈ N := by exact (Subgroup.inv_mem_iff N).mpr hn
      intro h1
      have : a⁻¹ ∈ N := by exact (Subgroup.mul_mem_cancel_right N hn).mp h1
      exact a_inv this
    have h8 : g * n ∉ N := by
      have a_inv_g : (g * a)⁻¹ ∈ N := by exact (Subgroup.inv_mem_iff N).mpr h4
      intro h1
      have hh : (g * a)⁻¹ * (g * n) ∈ N := by
        exact (Subgroup.mul_mem_cancel_right N h1).mpr a_inv_g
      have : a⁻¹ * n = (g * a)⁻¹ * (g * n) := by group
      have : a⁻¹ * n ∈ N := by
        rw[this]
        exact hh
      exact h6 this
    have h9 : (g * n * g⁻¹) * (g * a) ∈ N := by
      have hn1: g * n * a ∈ N := by
        rcases ha (g * n) with ⟨h41,h51⟩ |⟨h41, h51⟩
        · exact h41
        · exact False.elim (h8 h41)
      have : (g * n * g⁻¹) * (g * a) = g * n * a := by group
      rw [this]
      exact hn1
    exact (Subgroup.mul_mem_cancel_right N h4).mp h9
  · have h6: g * n ∈ N := by exact (Subgroup.mul_mem_cancel_right N hn).mpr h4
    have h7 : g⁻¹ ∈ N := by exact (Subgroup.inv_mem_iff N).mpr h4
    exact (Subgroup.mul_mem_cancel_right N h7).mpr h6

  --S15 Bezout theorem Use induction to show that for natural numbers $a,b\in\mathbb N=\mathbb Z_{\ge0}$ where $(a,b)\ne (0,0)$, there exists integer $x,y\in\mathbb Z$ such that $\operatorname{GCD}(a,b)=ax+by$. Here $\operatorname{GCD}$ should be defined as the largest positive integer which is the divisor of both $a$ and $b$.

  -- Firstly, we prove a lemma, stating that if gcd(a,b)=1, then their exists x and y in ℤ such that a * x + b * y = 1.

lemma bezout_theorem_of_one (n: ℕ ) : ∀ a b : ℕ , a + b = n  → gcd a b = 1 →  ∃ x y : ℤ , a * x + b * y = 1 := by
  --We prove by the induction of n = a + b.
  induction' n using Nat.strong_induction_on with n hn
  intro a b habn coprime
  --First Suppose that a > b.
  by_cases hab : a > b
  -- If b = 0, then a = 1, because gcd(a,0)=a. and we can apply 1 * 1 + 0 * 0 = 1.
  · by_cases zerob : b = 0
    · have : a ≠ 0 := by exact Nat.not_eq_zero_of_lt hab
      have : a = 1 := by
        rw[← Nat.gcd_zero_right a]
        rw[← zerob]
        exact coprime
      use 1,0
      rw[this, zerob]
      norm_num
    -- If b ≠  0, then a - b < a,
    · have a_le : a - b < a := by
        have : b > 0 := by exact Nat.zero_lt_of_ne_zero zerob
        omega
    -- and a can divided by a = (a - b) + b,
      have a_eq : (a - b) + b = a:= by
        apply Nat.sub_add_cancel
        exact Nat.le_of_succ_le hab
      have a_le_n : a < n := by
        omega
      have b_leq_a : b ≤ a := by
        exact Nat.le_of_succ_le hab
      -- and gcd(a,b) = gcd(a-b,b),
      have hgcd : gcd (a - b) b = 1 := by
        calc
          _ = gcd a b := by
            apply Nat.gcd_sub_self_left b_leq_a
          _ = _ := by exact coprime
      --so by the inductional assumption, their exists x0 and y0 such that (a - b) * x0 + b * y0 = 1. 
      rcases hn a a_le_n (a - b) b a_eq hgcd with ⟨x0 ,⟨ y0, hy⟩⟩
      --Then we can let x = x0 and y = y0 - x0.
      use x0, y0-x0
      calc
        _ = ((a : ℤ) - (b : ℤ)) * x0 + (b : ℤ) * y0 := by ring
        _ = ((a - b) : ℕ) * x0 + (b : ℤ) * y0 := by
          congr 2
          rw [Int.ofNat_sub b_leq_a]
        _ = _ := by rw[hy]
  · by_cases eq : a = b
    -- If a = b, then 1 = gcd(a,b) = gcd(a,a) = a, so we can apply x = 1 and y = 0.
    · have : a = 1 := by
        rw[← Nat.gcd_self a]
        calc
          _ = gcd a b := by 
            rw[eq]
            rfl
          _ = _ := by exact coprime
      use 1,0
      rw[← eq, this]
      simp
   -- Consider the case when a < b.
    · have a_leq_b : a ≤ b := by
        exact Nat.le_of_not_lt hab
      have hab : a < b := by
        exact Nat.lt_of_le_of_ne a_leq_b eq
      --If a = 0, then b = 1, because gcd(b,0)=b. and we can apply 0 * 1 + 1 * 1 = 1.
      by_cases zeroa : a = 0
      · have : b ≠ 0 := by exact Nat.not_eq_zero_of_lt hab
        have : b = 1 := by
          rw[← Nat.gcd_zero_left b]
          rw[← zeroa]
          exact coprime
        use 0,1
        rw[this, zeroa]
        norm_num
      -- If a ≠  0, then b - a < b,
      · have a_le : b - a < b := by
          have : b > 0 := by exact Nat.zero_lt_of_lt hab
          omega
        have b_eq : (b - a) + a = b:= by
          apply Nat.sub_add_cancel
          exact Nat.le_of_succ_le hab
        have b_le_n : b < n := by
          omega
      -- and gcd(b-a, b) = gcd(a,b),
        have hgcd : gcd (b - a) a = 1 := by
          calc
            _ = gcd b a := by
              apply Nat.gcd_sub_self_left a_leq_b
            _ = gcd a b := by exact gcd_comm b a
            _ = _ := by exact coprime
      --  so by the inductional assumption, their exists x0 and y0 such that (b - a) * x0 + a * y0 = 1. 
        rcases hn b b_le_n (b - a) a b_eq hgcd with ⟨x0 ,⟨ y0, hy⟩⟩
        --Then we can let x = y0 - x0 and y = x0.
        use y0-x0, x0
        calc
          _ = ((b : ℤ) - (a : ℤ)) * x0 + (a : ℤ) * y0 := by ring
          _ = ((b - a) : ℕ) * x0 + (a : ℤ) * y0 := by
            congr 2
            rw [Int.ofNat_sub a_leq_b]
          _ = _ := by rw[hy] 
-- Back to the origional problem.
theorem bezout_theorem (a b : ℕ) (h: (a ≠ 0) ∨ (b ≠ 0)) : ∃ x y : ℤ, a * x + b * y = gcd a b := by
  --First let d = gcd(a,b). Let  a = a' * d and b = b' * d.
  let d := gcd a b
  have d_non_zero : gcd a b ≠ 0 := by
    intro h1
    have ab_eq_zero:(a = 0) ∧ (b = 0) := by
       exact Nat.gcd_eq_zero_iff.mp h1
    have : ¬ ((a = 0) ∧ (b = 0)) := by
      exact (Decidable.not_and_iff_or_not (a = 0) (b = 0)).mpr h
    exact this ab_eq_zero
  --Then divide both side of  a * x + b * y = gcd(a,b) by d, so we can deduce that a' * x + b' * y = 1.
  let a' := a / d
  have a_mul : d * a' = a := by
    refine Nat.mul_div_cancel' ?H
    exact gcd_dvd_left a b
  let b' := b / d
  have b_mul : d * b' = b := by
    apply Nat.mul_div_cancel'
    exact gcd_dvd_right a b
  -- By lemma, it suffice to show that gcd(a',b')=1 by calculation. We first show that d * gcd(a',b') = d, and d ≠ 0.
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
  --Then we apply the lemma.
  rcases bezout_theorem_of_one (a' + b') a' b' (by norm_num) coprime with ⟨x0, ⟨y0,hxy⟩⟩
  use x0, y0
  have d_eq_ab :d = gcd a b := by simp
  nth_rw 1 [← a_mul, ← b_mul, ← d_eq_ab]
  calc
    _ = d * (a' * x0 + b' * y0) := by
      push_cast
      ring
    _ = d * 1 := by rw[hxy]
    _ = _  := by norm_num

--S16 Prove that the sum of odd numbers from 1 to 2n+1 is n^2.
open BigOperators Finset Classical

def p : ℕ → Prop := fun n ↦ Odd n

theorem rfl_p : p n ↔ Odd n := by rfl
-- Theorem to prove: For any natural number n, the sum of all odd numbers i in the range [0, 2*n) equals n*n. We use induction.
example (n : ℕ) : ∑ i ∈ range (2 * n) with p i, i = n * n := by
  induction' n  with n nh
  -- n = 0 is trivial.
  · simp
  -- If n > 0, we split the sum $\sum_{i=1}^{2(n+1)} Odd i$ into  $\sum_{i=1}^{2n} Odd i + (2n+1)$.
  · have : filter (fun i => p i) (range (2 * (n + 1))) = cons (2 * n + 1) (filter (fun i => p i) (range (2 * n))) (by
    simp
    ) := by
      simp
      ext a
      simp
      -- To show this, we must prove that if a < 2 * (n + 1) and a is odd, then  a = 2 * n + 1 or a < 2 * n and a is odd.
      rw [rfl_p]
      constructor
      · rintro ⟨h1, h2⟩
        by_cases h: a = 2 * n + 1
        · exact Or.intro_left (a < 2 * n ∧ Odd a) h
        · refine Or.inr ?_
          constructor
          · unfold Odd at h2
            omega
          · exact h2
      · intro h3
        constructor
        · rcases h3 with h | h
          rw [h]
          linarith
          rcases h with ⟨h5, _⟩
          apply lt_trans h5
          linarith
        · rcases h3 with h | h
          · unfold Odd
            use n
          · rcases h with ⟨_ , h6⟩
            exact h6
    rw [this]
    simp
    -- Then, using inductive hypothesis, we only need to show that 2 * n + 1 + n * n = (n + 1) * (n + 1).
    rw [nh]
    -- This is trivial!
    ring

-- S17 Let $G$ and $H$ be groups. Prove that if $G \times H$ is a cyclic group, then $G$ and $H$ are both cyclic.
-- Let $G$ and $H$ be groups. Prove that if $G \times H$ is a cyclic group, then $G$ and $H$ are both cyclic.
example {G H : Type*} [Group G] [Group H] (h : IsCyclic (G × H) ) : (IsCyclic G) ∧ (IsCyclic H) := by 
  constructor
    --Prove that G is cyclic. We want to find a generator.
  · refine { exists_generator := ?left.exists_generator } 
    rcases h with ⟨x, hx⟩
    -- Take the generator of the group G × H as x = (xG, xH), then xG is the generator of G and xH is the generator of H.
    let ⟨xG, xH⟩ := x
    use xG
    intro x
    rcases hx ⟨x,1⟩  with  ⟨x1,hx1⟩
    dsimp at hx1 
    use x1
    dsimp
    apply Prod.eq_iff_fst_eq_snd_eq.mp at hx1
    dsimp at hx1
    exact hx1.1

  · refine { exists_generator := ?right.exists_generator } 
    rcases h with ⟨x, hx⟩
    let ⟨xG, xH⟩ := x
    use xH
    intro x
    rcases hx ⟨1,x⟩  with  ⟨x1,hx1⟩
    dsimp at hx1 
    use x1
    dsimp
    apply Prod.eq_iff_fst_eq_snd_eq.mp at hx1
    dsimp at hx1
    exact hx1.2

--S18 Let $G$ be a group and suppose $a \in G$ generates a cyclic subgroup of order 2 and is the unique such element. Show that $a x=x a$ for all $x \in G$. [Hint: Consider $\left(x a x^{-1}\right)^{2}$.]
example {G : Type*} [Group G] {a : G} (h₁: orderOf a = 2) (h₂: ∃! (x : G), orderOf x = 2) : ∀ x : G, a * x = x * a := by 
  intro x
  -- Given that Ord(a) = 2, the square of a is 1
  have : a ^ 2 = 1 := by
    refine orderOf_dvd_iff_pow_eq_one.mp ?_
    rw[h₁]
  -- Consider (x * a * x⁻¹) ,its square is 1.
  have : (x * a * x⁻¹) ^ 2 = 1 :=
    calc
      _ = x * a * x⁻¹ * (x * a *x⁻¹) := by exact pow_two (x * a * x⁻¹)
      _ = x * (a * a) * x⁻¹ := by group
      _ = x * (a ^ 2) * x⁻¹ := by rw[pow_two]
      _ = x * 1 * x⁻¹ := by rw[this]
      _ = _ := by group
  
  rcases h₂ with ⟨c,_,hd⟩
  dsimp at hd
  -- To prove that Ord(x * a * x⁻¹) = 2.
  have : orderOf (x * a * x⁻¹) = 2 := by
    refine orderOf_eq_prime this ?hg1
    intro h
    -- To prove that its order is not 1, using contradiction.
    have : a = 1 := by
      calc
       _ = x⁻¹ * (x * a * x⁻¹) * x :=  by group
       _ = x⁻¹  * 1 * x := by rw[h]
       _ = _ := by group
    have : orderOf a = 1 := by
      exact orderOf_eq_one_iff.mpr this
    absurd h₁
    rw [this]
    norm_num
  -- To prove that a and x * a * x⁻¹ are both the unique element, thus they are same.
  have h5: (x * a * x⁻¹) = c := by exact hd (x * a * x⁻¹) this
  have h4: a = c := by exact hd a h₁
  symm
  -- finally calc
  calc
    _ = x * a * x⁻¹ * x := by group
    _ = c * x := by rw[h5]
    _ = a * x := by rw[h4]

--S19 Prove that if $G$ is an Abelian group, written multiplicatively, with identity element $e$, then all elements $x$ of $G$ satisfying the equation $x^{2}=e$ form a subgroup $H$ of $G$.

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

     