import Mathlib

-- For Real numbers with a ≥ 1
#check @Real.rpow_natCast_mono
#check @one_le_pow_iff_of_nonneg
#check @pow_le_pow_right_of_le_one
example (a : ℝ) (m n : ℕ) (ha : 1 ≤ a) (hmn : m ≤ n) : a ^ m ≤ a ^ n := by
  exact pow_le_pow_right ha hmn

-- Exact name check
#check pow_le_pow_right

