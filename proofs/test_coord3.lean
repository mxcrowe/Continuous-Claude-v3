import Mathlib

noncomputable section

-- Pigeonhole for same side
lemma pigeonhole_same_side (t₁ t₂ t₃ : ℝ) :
    (0 ≤ t₁ ∧ 0 ≤ t₂) ∨ (0 ≤ t₁ ∧ 0 ≤ t₃) ∨ (0 ≤ t₂ ∧ 0 ≤ t₃) ∨
    (t₁ ≤ 0 ∧ t₂ ≤ 0) ∨ (t₁ ≤ 0 ∧ t₃ ≤ 0) ∨ (t₂ ≤ 0 ∧ t₃ ≤ 0) := by
  by_cases h₁ : 0 ≤ t₁
  · by_cases h₂ : 0 ≤ t₂
    · exact Or.inl ⟨h₁, h₂⟩
    · by_cases h₃ : 0 ≤ t₃
      · exact Or.inr (Or.inl ⟨h₁, h₃⟩)
      · push_neg at h₂ h₃
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨le_of_lt h₂, le_of_lt h₃⟩))))
  · by_cases h₂ : 0 ≤ t₂
    · by_cases h₃ : 0 ≤ t₃
      · exact Or.inr (Or.inr (Or.inl ⟨h₂, h₃⟩))
      · push_neg at h₁ h₃
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨le_of_lt h₁, le_of_lt h₃⟩))))
    · push_neg at h₁ h₂
      exact Or.inr (Or.inr (Or.inr (Or.inl ⟨le_of_lt h₁, le_of_lt h₂⟩)))

-- Key lemma: for two values on the same side of 0, the difference is bounded
lemma same_side_dist_bound {tx tz : ℝ} (h : (0 ≤ tx ∧ 0 ≤ tz) ∨ (tx ≤ 0 ∧ tz ≤ 0)) 
    (htz : |tx| ≤ |tz|) : |tx - tz| ≤ |tz| := by
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · -- Both ≥ 0: |tx - tz| = |tz - tx| = tz - tx ≤ tz = |tz|
    have htx_eq : |tx| = tx := abs_of_nonneg h1
    have htz_eq : |tz| = tz := abs_of_nonneg h2
    rw [htx_eq, htz_eq] at htz  -- Now htz : tx ≤ tz
    have h_diff : 0 ≤ tz - tx := by linarith
    calc |tx - tz| = |-(tz - tx)| := by ring_nf
      _ = |tz - tx| := abs_neg _
      _ = tz - tx := abs_of_nonneg h_diff
      _ ≤ tz := by linarith
      _ = |tz| := htz_eq.symm
  · -- Both ≤ 0: |tx - tz| = |tz - tx| = tx - tz ≤ -tz = |tz|
    have htx_eq : |tx| = -tx := abs_of_nonpos h1
    have htz_eq : |tz| = -tz := abs_of_nonpos h2
    rw [htx_eq, htz_eq] at htz  -- Now htz : -tx ≤ -tz, i.e., tz ≤ tx
    have h_diff : tx - tz ≥ 0 := by linarith
    have h_tz_neg : -tz ≥ 0 := by linarith
    calc |tx - tz| = tx - tz := abs_of_nonneg (by linarith : 0 ≤ tx - tz)
      _ ≤ -tz := by linarith
      _ = |tz| := htz_eq.symm

#check pigeonhole_same_side
#check same_side_dist_bound

end
