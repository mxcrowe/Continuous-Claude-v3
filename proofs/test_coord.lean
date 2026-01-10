import Mathlib

open scoped EuclideanGeometry
open AffineSubspace Set Finset Classical

noncomputable section

abbrev Plane := EuclideanSpace ℝ (Fin 2)

-- Helper: on a line, among 3 points, at least one pair satisfies the betweenness condition relative to F
-- This is a pigeonhole argument: 3 points relative to 1 dividing point F

-- The core observation: if we parameterize L by a single real coordinate,
-- then among any 3 real numbers (the coordinates of a, b, c) relative to F's coordinate,
-- at least 2 have the same sign (or one is 0).

-- For 2 points with the same sign relative to F, one is "between" F and the other.

-- Pigeonhole principle for signs: among 3 nonzero reals, at least 2 have the same sign
-- (since there are only 2 signs: positive and negative)

-- Weak version: among any 3 reals, either one is 0 or at least 2 have the same sign
lemma pigeonhole_sign (t₁ t₂ t₃ : ℝ) :
    t₁ = 0 ∨ t₂ = 0 ∨ t₃ = 0 ∨ 
    (t₁ > 0 ∧ t₂ > 0) ∨ (t₁ > 0 ∧ t₃ > 0) ∨ (t₂ > 0 ∧ t₃ > 0) ∨
    (t₁ < 0 ∧ t₂ < 0) ∨ (t₁ < 0 ∧ t₃ < 0) ∨ (t₂ < 0 ∧ t₃ < 0) := by
  by_cases h₁ : t₁ = 0
  · left; exact h₁
  · by_cases h₂ : t₂ = 0
    · right; left; exact h₂
    · by_cases h₃ : t₃ = 0
      · right; right; left; exact h₃
      · -- All nonzero
        push_neg at h₁ h₂ h₃
        have h₁' := h₁.lt_or_lt
        have h₂' := h₂.lt_or_lt
        have h₃' := h₃.lt_or_lt
        -- t₁, t₂, t₃ are each either < 0 or > 0
        -- By pigeonhole (2 categories, 3 items), at least 2 are in the same category
        rcases h₁' with h₁n | h₁p <;> rcases h₂' with h₂n | h₂p <;> rcases h₃' with h₃n | h₃p
        all_goals (first | exact Or.inr (Or.inr (Or.inr (Or.inl ⟨h₁p, h₂p⟩)))
                        | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h₁p, h₃p⟩))))
                        | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h₂p, h₃p⟩)))))
                        | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h₁n, h₂n⟩))))))
                        | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h₁n, h₃n⟩)))))))
                        | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨h₂n, h₃n⟩))))))))

-- Simpler: among 3 reals relative to 0, at least 2 are both ≥ 0 or both ≤ 0
lemma pigeonhole_same_side (t₁ t₂ t₃ : ℝ) :
    (0 ≤ t₁ ∧ 0 ≤ t₂) ∨ (0 ≤ t₁ ∧ 0 ≤ t₃) ∨ (0 ≤ t₂ ∧ 0 ≤ t₃) ∨
    (t₁ ≤ 0 ∧ t₂ ≤ 0) ∨ (t₁ ≤ 0 ∧ t₃ ≤ 0) ∨ (t₂ ≤ 0 ∧ t₃ ≤ 0) := by
  by_cases h₁ : 0 ≤ t₁ <;> by_cases h₂ : 0 ≤ t₂ <;> by_cases h₃ : 0 ≤ t₃ <;>
    push_neg at * <;> omega

-- The key geometric lemma: for two points on the same side of F on a line,
-- the one closer to F is "between" F and the other
-- dist(x, z) ≤ dist(F, z) when x is between F and z

-- In coordinates: if 0 ≤ tx ≤ tz (or tz ≤ tx ≤ 0), then |tx - tz| ≤ |tz|
lemma same_side_dist_bound {tx tz : ℝ} (h : (0 ≤ tx ∧ 0 ≤ tz) ∨ (tx ≤ 0 ∧ tz ≤ 0)) :
    min |tx - tz| |tz - tx| ≤ max |tx| |tz| := by
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> simp [abs_of_nonneg, abs_of_nonpos, *] <;> linarith

-- Stronger: specifically when comparing |tx - tz| to |tz| (taking the farther one as z)
lemma same_side_dist_bound' {tx tz : ℝ} (h : (0 ≤ tx ∧ 0 ≤ tz) ∨ (tx ≤ 0 ∧ tz ≤ 0)) 
    (htz : |tx| ≤ |tz|) : |tx - tz| ≤ |tz| := by
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · -- Both ≥ 0
    rw [abs_of_nonneg h1, abs_of_nonneg h2] at htz
    rw [abs_of_nonneg h2]
    rw [abs_sub_comm, abs_of_nonneg (by linarith : 0 ≤ tz - tx)]
    linarith
  · -- Both ≤ 0
    rw [abs_of_nonpos h1, abs_of_nonpos h2] at htz
    rw [abs_of_nonpos h2]
    rw [abs_of_nonpos (by linarith : tx - tz ≤ 0)]
    linarith

-- Now the main lemma using coordinate-based reasoning
-- The distance on L is related to the coordinate difference by a constant (the norm of the direction vector)

#check pigeonhole_same_side
#check same_side_dist_bound'

end
