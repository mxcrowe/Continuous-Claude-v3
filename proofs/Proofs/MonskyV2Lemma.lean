/-
  Monsky's v₂ Constraint - Helper Lemmas
  ======================================

  This file develops the machinery needed to prove:
  For a complete triangle in [0,1]², v₂(twiceArea) ≤ 0.

  Key insight: The determinant formula has a unique minimum-valuation term.
-/

import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Tactic

set_option linter.style.nativeDecide false

noncomputable section

namespace MonskyV2Lemma

instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

/-!
## Part 1: Basic v₂ properties
-/

/-- v₂(a*b) = v₂(a) + v₂(b) for nonzero a, b -/
lemma v2_mul {a b : ℚ} (ha : a ≠ 0) (hb : b ≠ 0) :
    padicValRat 2 (a * b) = padicValRat 2 a + padicValRat 2 b :=
  padicValRat.mul ha hb

/-- v₂(a + b) ≥ min(v₂(a), v₂(b)) when a + b ≠ 0 -/
lemma v2_add_ge_min {a b : ℚ} (hab : a + b ≠ 0) :
    min (padicValRat 2 a) (padicValRat 2 b) ≤ padicValRat 2 (a + b) :=
  padicValRat.min_le_padicValRat_add hab

/-- When v₂(a) ≠ v₂(b), we have v₂(a + b) = min(v₂(a), v₂(b)) -/
lemma v2_add_eq_min {a b : ℚ} (hab : a + b ≠ 0) (ha : a ≠ 0) (hb : b ≠ 0)
    (hne : padicValRat 2 a ≠ padicValRat 2 b) :
    padicValRat 2 (a + b) = min (padicValRat 2 a) (padicValRat 2 b) :=
  padicValRat.add_eq_min hab ha hb hne

/-- v₂(q⁻¹) = -v₂(q) -/
lemma v2_inv (q : ℚ) : padicValRat 2 q⁻¹ = -padicValRat 2 q :=
  padicValRat.inv q

/-!
## Part 2: v₂ for powers of 2
-/

/-- v₂(2^n) = n -/
lemma v2_pow_two (n : ℕ) : padicValRat 2 (2^n : ℚ) = n := by
  have h2n : (2 : ℚ)^n = ((2^n : ℕ) : ℚ) := by norm_cast
  rw [h2n, padicValRat.of_nat]
  have : padicValNat 2 (2^n) = n * padicValNat 2 2 := padicValNat.pow n (by norm_num : (2:ℕ) ≠ 0)
  simp only [padicValNat.self (by norm_num : 1 < 2), mul_one] at this
  exact_mod_cast this

/-- v₂(1/2^n) = -n -/
lemma v2_pow_two_inv (n : ℕ) : padicValRat 2 (1 / 2^n : ℚ) = -(n : ℤ) := by
  rw [one_div, v2_inv, v2_pow_two]

/-- v₂(k/2^n) = v₂(k) - n for natural k ≠ 0 -/
lemma v2_nat_div_pow_two {k : ℕ} (hk : k ≠ 0) (n : ℕ) :
    padicValRat 2 (k / 2^n : ℚ) = padicValNat 2 k - n := by
  have hkq : (k : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hk
  have h2n : (2 : ℚ)^n ≠ 0 := pow_ne_zero n (by norm_num)
  rw [div_eq_mul_inv, padicValRat.mul hkq (inv_ne_zero h2n)]
  rw [v2_inv, v2_pow_two, padicValRat.of_nat]
  ring

/-!
## Part 3: v₂ bound for unit interval dyadic rationals
-/

/-- For k ≤ 2^n with k ≠ 0, we have v₂(k) ≤ n -/
lemma v2_nat_le_log {k : ℕ} (hk : k ≠ 0) (n : ℕ) (hle : k ≤ 2^n) :
    padicValNat 2 k ≤ n := by
  by_contra h
  push_neg at h
  -- If v₂(k) > n, then 2^(n+1) divides k
  have hv : padicValNat 2 k ≥ n + 1 := by omega
  have hdvd : 2^(n+1) ∣ k := by
    have hpow : 2^(padicValNat 2 k) ∣ k := pow_padicValNat_dvd
    exact Nat.dvd_trans (Nat.pow_dvd_pow 2 hv) hpow
  -- But 2^(n+1) > 2^n ≥ k, contradiction
  have h2pow : 2^(n+1) > k := by
    calc 2^(n+1) > 2^n := Nat.pow_lt_pow_right (by norm_num : 1 < 2) (by omega)
      _ ≥ k := hle
  have hk_ge : k ≥ 2^(n+1) := Nat.le_of_dvd (Nat.pos_of_ne_zero hk) hdvd
  omega

/-- For dyadic x = k/2^n in (0,1], v₂(x) ≤ 0 -/
theorem v2_dyadic_unit_interval {k : ℕ} {n : ℕ} (hk : k ≠ 0) (hle : k ≤ 2^n) :
    padicValRat 2 (k / 2^n : ℚ) ≤ 0 := by
  rw [v2_nat_div_pow_two hk n]
  have hv2k := v2_nat_le_log hk n hle
  omega

/-!
## Part 4: Concrete examples verifying the constraint
-/

-- Example: v₂(1/2) = -1 ≤ 0
example : padicValRat 2 (1/2 : ℚ) ≤ 0 := by native_decide

-- Example: v₂(1/4) = -2 ≤ 0
example : padicValRat 2 (1/4 : ℚ) ≤ 0 := by native_decide

-- Example: v₂(3/4) = v₂(3) - 2 = 0 - 2 = -2 ≤ 0
example : padicValRat 2 (3/4 : ℚ) ≤ 0 := by native_decide

-- Complete triangle example:
-- P0 = (1/2, 1): color 0 (v₂(1/2)=-1 < v₂(1)=0)
-- P1 = (1, 1/2): color 1 (v₂(1)=0 > v₂(1/2)=-1)
-- P2 = (1, 1): color 2 (v₂(1)=0 = v₂(1)=0)
-- twiceArea = 1/4, v₂(1/4) = -2 ≤ 0 ✓
example : padicValRat 2 (1/4 : ℚ) ≤ 0 := by native_decide

/-!
## Part 5: The determinant structure

For triangle with vertices (a,b), (c,d), (e,f):
twiceArea = a(d-f) + c(f-b) + e(b-d)
          = ad - af + cf - cb + eb - ed

For a complete triangle:
- (a,b) has color 0: v₂(a) < v₂(b)
- (c,d) has color 1: v₂(c) > v₂(d)
- (e,f) has color 2: v₂(e) = v₂(f)

Let α = v₂(a), β = v₂(b), γ = v₂(c), δ = v₂(d), ε = v₂(e) = v₂(f).
Constraints: α < β, γ > δ.

The six terms have valuations:
- v₂(ad) = α + δ
- v₂(af) = α + ε
- v₂(cf) = γ + ε
- v₂(cb) = γ + β
- v₂(eb) = ε + β
- v₂(ed) = ε + δ

MONSKY'S KEY LEMMA: For a complete triangle, α + δ is the unique minimum.

Proof sketch:
1. α + δ < γ + β: We have α < β and δ < γ, so α + δ < β + γ ✓
2. α + δ < γ + ε: Need to analyze based on ordering of δ, ε
3. α + δ < α + ε: Equivalent to δ < ε
4. α + δ < ε + β: Equivalent to α - ε < β - δ
5. α + δ < ε + δ: Equivalent to α < ε

The full proof requires careful case analysis (~100 lines) handling
all possible orderings of the five valuations α, β, γ, δ, ε,
and showing that in each case, α + δ achieves the unique minimum.

For now, we have proved the key building block: v₂(x) ≤ 0 for
dyadic rationals x in (0,1].
-/

#check v2_dyadic_unit_interval

end MonskyV2Lemma

end
