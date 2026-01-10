-- Test file to verify compiler-in-the-loop hook

theorem test_add : 1 + 1 = 2 := by
  native_decide

-- Fixed based on Godel suggestion: use simp
theorem test_zero_add : ∀ n : Nat, n + 0 = n := by
  simp
