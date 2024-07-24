import Mathlib
--Let $a$ be elements of a group $G$. Show that $\operatorname{ord}(a)=\operatorname{ord}(a^{-1})$.
example {G : Type*} [Group G] (a : G) : orderOf a = orderOf (a⁻¹) := by
  -- If for all interger n, $a^n = 1$ if and only if $b^n = 1$, then Ord(a) = Ord(b).
  refine orderOf_eq_orderOf_iff.mpr ?_
  intro n
  constructor
  ·intro h
  -- If a ^ n = 1, then a⁻¹ ^ n = 1.
   calc
     _ = (a ^ n)⁻¹ := by exact inv_pow a n
     _ = 1⁻¹ := by rw[h]
     _ = _ := by group
  -- If a⁻¹  ^ n = 1, then a ^ n = 1.
  ·intro h
   calc
     _ = ((a⁻¹) ^ n )⁻¹ := by group
     _ = 1⁻¹ := by rw[h]
     _ = _ := by group

--2204B
--Let $G$ be a group and suppose $a \in G$ generates a cyclic subgroup of order 2 and is the unique such element. Show that $a x=x a$ for all $x \in G$. [Hint: Consider $\left(x a x^{-1}\right)^{2}$.]
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

--Let $a, b$, and $c$ be elements of a group $G$, then $\operatorname{ord}(a b c)=\operatorname{ord}(c a b)$.
-- This is exercise 1409B
theorem order_conj {G : Type*} [Group G] (a b : G) : orderOf a = orderOf ((b * a * b⁻¹)) := by
  -- If for all interger n, $a^n = 1$ if and only if $b^n = 1$, then Ord(a) = Ord(b).
  refine orderOf_eq_orderOf_iff.mpr ?_
  intro n
  constructor
  -- Show that if $a ^ n = 1$, then (b * a * b⁻¹) ^ n = 1.
  · intro h
    calc
      _ = b * (a ^ n) * b⁻¹ := by exact conj_pow
      _ = b * 1 * b⁻¹ := by rw[h]
      _ = _ := by group
  -- Show that if (b * a * b⁻¹) ^ n = 1, then $a ^ n = 1$.
  · intro h
    have : b * (a ^ n) * b⁻¹ = 1 := by
      calc
        _ = (b * a * b⁻¹) ^ n := by exact Eq.symm conj_pow
        _ = _ := by rw[h]
    calc
      _ = b⁻¹ * (b *(a ^ n) * b⁻¹) * b := by group
      _ = b⁻¹  * 1 * b := by rw[this]
      _ = _ := by group

--Corllary of the exercise 1409B: that ord(ab) = ord(ba).
theorem order_comm {G : Type*} [Group G] (a b : G) : orderOf (a*b) = orderOf (b * a) := by
  rw[order_conj (a * b) b]
  have : b * (a * b) * b⁻¹ = b * a := by group
  rw [ this ]

--Since the order is communicative, we can transform cba into abc.
example { G : Type* } [ Group G ] { a b c: G } : orderOf (
   a * b * c ) = orderOf ( c * a * b ) := by

  rw[order_comm (a * b) c]
  rw[← mul_assoc]
