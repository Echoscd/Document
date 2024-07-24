import mathlib
def conj {G : Type*} [Group G] (S: Subgroup G) (g : G) :Set G := { p | ∃ s : S, p = g * s * g⁻¹ }

def normaliser_carrier {G : Type*} [Group G] (S: Subgroup G): Set G := { g | (conj S g) = S }

def normaliser {G : Type*} [Group G] (S: Subgroup G): Subgroup G where
  carrier := normaliser_carrier S
  mul_mem' := by sorry
  one_mem' := by sorry
  inv_mem' := by sorry
def abgroup {G : Type*} [Group G] (H : Set G) (h_finite: H.Finite) (non_em: H.Nonempty) (h0: ∀ a ∈ H,∀ b ∈ H, a * b ∈ H) : Subgroup G where
  carrier := H
  mul_mem' := by
    intro a b h0a h0b
    exact h0 a h0a b h0b
  one_mem' := by
    rcases non_em with ⟨x, hx⟩
    have Ord_pos: orderOf x > 0 := by
      sorry
    have : ∀ x : H, ∀ n > 0 , (x : G) ^ n ∈ H := by
      intro x n npos
      induction' n with n hn
      · sorry
      · have : (x : G) ^ (n + 1) = (x : G) ^ n * x := by group
        rw[this]
        have n_pos : n > 0 := by apply?
          apply mul_mem' (x : G) ^ n x
  inv_mem' := sorry
def H_cap_K {G : Type*} [Group G] (H K: Subgroup G) : Set G := H.carrier ∩ K.carrier
-- To prove that if G,H are subgroups, then $G\capH$ is a subgroup.
def intersect_subgroup {G : Type*} [Group G] (H K: Subgroup G) : Subgroup G where
  carrier := H_cap_K H K
  --Firstly we prove that for any two elments $x,y \in G,H$, then $xy ∈ GH$.
  mul_mem' := by
    intro a b ha hb
    constructor
    · apply H.mul_mem'
      exact Set.mem_of_mem_inter_left ha
      exact Set.mem_of_mem_inter_left hb
    · apply K.mul_mem'
      exact Set.mem_of_mem_inter_right ha
      exact Set.mem_of_mem_inter_right hb
--Also since $1 ∈ G,H$, then 1 ∈ G ∩ H.
  one_mem' := by
    dsimp
    constructor
    apply H.one_mem'
    apply K.one_mem'
--Finally the inverse of element in G ∩ H is also in G ∩ H.
  inv_mem' := by
    intro x hx
    dsimp at hx
    rcases hx with ⟨ha,hb⟩
    dsimp
    constructor
    ·apply H.inv_mem' ha
    ·apply K.inv_mem' hb

example {G : Type*} [Group G] (H K: Subgroup G) [h₁: H.Normal] [h₂: K.Normal] : (intersect_subgroup H K).Normal := {
  --To prove that G ∩ H is normal, it suffice to show that the conjugate of an element x ∈ G ∩ H is still in G ∩ H.
  conj_mem := by
    intro x hx
    rcases hx with ⟨h1,h2⟩
    let h₁' := h₁.conj_mem
    let h₂' := h₂.conj_mem
    --Since G, H is normal, the conjugate of an element in G is still in G, and so is H.
    intro g
    constructor
    · exact h₁' x h1 g
    · exact h₂' x h2 g

}
#check Subgroup.index_eq_two_iff
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
