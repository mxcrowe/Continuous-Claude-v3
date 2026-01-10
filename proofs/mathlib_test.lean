/-
Test: Verify Mathlib imports work after cache download
-/
import Mathlib.Tactic

theorem test_mathlib : ∀ n : ℕ, n + 0 = n := by
  intro n
  simp
