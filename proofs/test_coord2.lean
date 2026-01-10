import Mathlib

open scoped EuclideanGeometry
open AffineSubspace Set Finset Classical

noncomputable section

abbrev Plane := EuclideanSpace ℝ (Fin 2)

-- Simpler: among 3 reals relative to 0, at least 2 are both ≥ 0 or both ≤ 0
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

-- Stronger: specifically when comparing |tx - tz| to |tz| (taking the farther one as z)
lemma same_side_dist_bound {tx tz : ℝ} (h : (0 ≤ tx ∧ 0 ≤ tz) ∨ (tx ≤ 0 ∧ tz ≤ 0)) 
    (htz : |tx| ≤ |tz|) : |tx - tz| ≤ |tz| := by
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · -- Both ≥ 0
    have htx : tx = |tx| := abs_of_nonneg h1
    have htz' : tz = |tz| := abs_of_nonneg h2
    rw [htx, htz'] at htz
    calc |tx - tz| = |tx - tz| := rfl
      _ = tz - tx := by rw [abs_sub_comm]; exact abs_of_nonneg (by linarith)
      _ ≤ tz := by linarith
      _ = |tz| := (abs_of_nonneg h2).symm
  · -- Both ≤ 0
    have htx : -tx = |tx| := abs_of_nonpos h1
    have htz' : -tz = |tz| := abs_of_nonpos h2
    rw [← htx, ← htz'] at htz
    have h_neg : tx - tz ≤ 0 := by linarith
    calc |tx - tz| = -(tx - tz) := abs_of_nonpos h_neg
      _ = tz - tx := by ring
      _ ≤ -tx := by linarith
      _ = |tx| := htx.symm
      _ ≤ |tz| := htz

#check pigeonhole_same_side
#check same_side_dist_bound

end
