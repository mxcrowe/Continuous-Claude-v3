import Mathlib

/-!
# Every group of order p² is abelian

## Main Result

`isCommutative_of_card_eq_prime_sq`: A finite group of order p² (p prime) is abelian.

## Proof Strategy

For a p-group G with |G| = p²:
1. The center Z(G) is non-trivial (standard p-group result)
2. So |Z(G)| ∈ {p, p²} by Lagrange's theorem
3. If |Z(G)| = p², then G = Z(G), done
4. If |Z(G)| = p, then |G/Z(G)| = p, so G/Z(G) is cyclic
5. G/Z(G) cyclic ⟹ G abelian (standard result)
-/

open Subgroup in
/-- A group of order p² is commutative -/
theorem isCommutative_of_card_eq_prime_sq
    {G : Type*} [Group G] [Fintype G]
    {p : ℕ} [hp : Fact (Nat.Prime p)]
    (hcard : Fintype.card G = p ^ 2) :
    ∀ a b : G, a * b = b * a := by
  have hpp : Nat.Prime p := hp.out
  -- Convert to Nat.card for IsPGroup
  have hcard' : Nat.card G = p ^ 2 := by simp [Nat.card_eq_fintype_card, hcard]
  -- The key insight: G is a p-group
  have hpgroup : IsPGroup p G := IsPGroup.of_card hcard'
  -- G is nontrivial since |G| = p² ≥ 4
  haveI hnt : Nontrivial G := by
    apply Fintype.one_lt_card_iff_nontrivial.mp
    rw [hcard]
    calc 1 < p := Nat.Prime.one_lt hpp
         _ ≤ p ^ 2 := Nat.le_self_pow (by omega) p
  -- For p-groups, the center is nontrivial
  haveI hcenter : Nontrivial (center G) := IsPGroup.center_nontrivial hpgroup
  -- The center has order dividing p² (using Nat.card)
  have hdiv : Nat.card (center G) ∣ p ^ 2 := by
    rw [← hcard']
    exact Subgroup.card_subgroup_dvd_card _
  -- Center is nontrivial means order > 1
  have hgt1 : 1 < Nat.card (center G) := Finite.one_lt_card_iff_nontrivial.mpr hcenter
  -- Divisors of p² that are > 1 are p or p²
  have hdiv_cases : Nat.card (center G) = p ∨ Nat.card (center G) = p ^ 2 := by
    have h := (Nat.dvd_prime_pow hpp).mp hdiv
    obtain ⟨k, hk, hcard_center⟩ := h
    interval_cases k
    · -- k = 0: |Z(G)| = p^0 = 1, contradicts hgt1
      simp only [pow_zero] at hcard_center
      omega
    · -- k = 1: |Z(G)| = p
      left; simp only [pow_one] at hcard_center; exact hcard_center
    · -- k = 2: |Z(G)| = p²
      right; exact hcard_center
  rcases hdiv_cases with hp_case | hp2_case
  · -- Case: |Z(G)| = p, so |G/Z(G)| = p
    intro a b
    have hquot : Nat.card (G ⧸ center G) = p := by
      have heq := Subgroup.card_eq_card_quotient_mul_card_subgroup (center G)
      rw [hcard', hp_case] at heq
      have hp_pos : 0 < p := Nat.Prime.pos hpp
      have hp2 : p ^ 2 = p * p := sq p
      rw [hp2] at heq
      exact Nat.eq_of_mul_eq_mul_right hp_pos heq.symm
    -- A group of prime order is cyclic
    have hcyclic : IsCyclic (G ⧸ center G) := isCyclic_of_prime_card hquot
    -- G/Z(G) cyclic implies G is abelian via the quotient map
    have hker : (QuotientGroup.mk' (center G)).ker ≤ center G := by
      rw [QuotientGroup.ker_mk']
    exact commutative_of_cyclic_center_quotient (QuotientGroup.mk' (center G)) hker a b
  · -- Case: |Z(G)| = p², so Z(G) = G
    intro a b
    have hcenter_eq : center G = ⊤ := by
      apply Subgroup.eq_top_of_card_eq
      rw [hp2_case, hcard']
    -- All elements are in the center
    have ha : a ∈ center G := by rw [hcenter_eq]; trivial
    -- Use center membership to show commutativity
    exact (mem_center_iff.mp ha b).symm
