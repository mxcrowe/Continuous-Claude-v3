import Mathlib.NumberTheory.Padics.PadicVal.Basic
#check @padicValNat.pow_dvd
#check @pow_padicValNat_dvd
example (n : ℕ) (hn : n ≠ 0) : 2^(padicValNat 2 n) ∣ n := by exact?
