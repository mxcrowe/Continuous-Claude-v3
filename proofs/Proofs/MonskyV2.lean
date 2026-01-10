/-
  Monsky's Theorem - Proof Status
  ================================

  This file contains a partial formalization of Monsky's theorem.
  It clearly identifies what is PROVED vs what is ASSUMED.

  PROVED:
  - 2-adic coloring is well-defined
  - Unit square corners have colors 2, 0, 1, 2
  - v₂(2/n) = 1 for odd n
  - The main theorem follows from the key lemma

  ASSUMED (requires ~300 lines of additional proof):
  - Sperner property: every triangulation has a complete triangle
  - v₂ constraint: complete triangles in [0,1]² satisfy v₂(area) ≤ 0

  Reference: Monsky, P. (1970). "On Dividing a Square into Triangles".
-/

import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.Ring.Parity
import Mathlib.Data.Fin.Basic
import Mathlib.Tactic

set_option linter.style.nativeDecide false

noncomputable section

namespace MonskyV2

attribute [local instance] Classical.propDecidable

/-!
## Part 1: 2-adic Coloring (PROVED)
-/

def v₂Ext (q : ℚ) : Option ℤ :=
  if q = 0 then none else some (padicValRat 2 q)

def color (p : ℚ × ℚ) : Fin 3 :=
  match v₂Ext p.1, v₂Ext p.2 with
  | none, none => 2
  | none, some _ => 1
  | some _, none => 0
  | some vx, some vy =>
      if vx < vy then 0
      else if vx > vy then 1
      else 2

lemma color_00 : color (0, 0) = 2 := by native_decide
lemma color_10 : color (1, 0) = 0 := by native_decide
lemma color_01 : color (0, 1) = 1 := by native_decide
lemma color_11 : color (1, 1) = 2 := by native_decide

/-!
## Part 2: Triangle Structure (PROVED)
-/

structure Triangle where
  v₁ : ℚ × ℚ
  v₂ : ℚ × ℚ
  v₃ : ℚ × ℚ

def Triangle.twiceArea (t : Triangle) : ℚ :=
  t.v₁.1 * (t.v₂.2 - t.v₃.2) +
  t.v₂.1 * (t.v₃.2 - t.v₁.2) +
  t.v₃.1 * (t.v₁.2 - t.v₂.2)

def Triangle.isComplete (t : Triangle) : Prop :=
  color t.v₁ ≠ color t.v₂ ∧ color t.v₂ ≠ color t.v₃ ∧ color t.v₁ ≠ color t.v₃

/-!
## Part 3: 2-adic Valuation Lemmas (PROVED)
-/

instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

lemma padicValNat_odd {n : ℕ} (hodd : Odd n) : padicValNat 2 n = 0 := by
  apply padicValNat.eq_zero_of_not_dvd
  intro h2dvd
  have heven : Even n := even_iff_two_dvd.mpr h2dvd
  exact (Nat.not_even_iff_odd.mpr hodd) heven

lemma padicValRat_two : padicValRat 2 (2 : ℚ) = 1 := by
  rw [show (2 : ℚ) = (2 : ℕ) by norm_num, padicValRat.of_nat]
  norm_cast; exact padicValNat.self (by norm_num : 1 < 2)

lemma padicValRat_two_div_odd {n : ℕ} (hn : n ≠ 0) (hodd : Odd n) :
    padicValRat 2 (2 / n : ℚ) = 1 := by
  have hne : (n : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have h1n_ne : (1 : ℚ) / n ≠ 0 := by rw [one_div]; exact inv_ne_zero hne
  have h2n : (2 : ℚ) / n = 2 * (1 / n) := by ring
  rw [h2n, padicValRat.mul (by norm_num : (2 : ℚ) ≠ 0) h1n_ne]
  rw [one_div, padicValRat.inv (n : ℚ), padicValRat_two]
  have hv : padicValRat 2 (n : ℚ) = 0 := by
    rw [padicValRat.of_nat]; norm_cast; exact padicValNat_odd hodd
  omega

/-!
## Part 4: Triangulation Structure

The key geometric constraints are encoded as structure fields.
-/

def inUnitSquare (p : ℚ × ℚ) : Prop :=
  0 ≤ p.1 ∧ p.1 ≤ 1 ∧ 0 ≤ p.2 ∧ p.2 ≤ 1

structure Triangulation (n : ℕ) where
  triangles : Fin n → Triangle
  vertices_in_square : ∀ i, inUnitSquare (triangles i).v₁ ∧
                            inUnitSquare (triangles i).v₂ ∧
                            inUnitSquare (triangles i).v₃
  equal_areas : ∀ i, |(triangles i).twiceArea| = 2 / n
  nonzero_areas : ∀ i, (triangles i).twiceArea ≠ 0
  -- ASSUMPTION 1: Sperner property
  has_complete : ∃ i, (triangles i).isComplete

/-!
## Part 5: The Key Algebraic Constraint (ASSUMED)

This is the heart of Monsky's theorem. For a complete triangle
in [0,1]², the 2-adic valuation of the area satisfies:

  v₂(twiceArea) ≤ 0

This follows from Monsky's lemma about the determinant formula:
- For a complete triangle with colors 0, 1, 2 at vertices
- The determinant expansion has terms with different v₂ values
- The minimum v₂ term doesn't cancel (it's unique)
- This minimum is ≤ 0 for vertices in [0,1]²

The full proof requires:
1. Case analysis on which vertex has which color
2. Tracking v₂ through the determinant expansion
3. Handling boundary cases (coordinates = 0)

This is approximately 200-300 lines of detailed case analysis.
-/

axiom v2_complete_triangle_constraint {t : Triangle}
    (hcomplete : t.isComplete)
    (hin : inUnitSquare t.v₁ ∧ inUnitSquare t.v₂ ∧ inUnitSquare t.v₃)
    (hnonzero : t.twiceArea ≠ 0) :
    padicValRat 2 t.twiceArea ≤ 0

/-!
## Part 6: Main Contradiction (PROVED from axiom)
-/

theorem v2_contradiction {n : ℕ} (hn : n ≠ 0) (hodd : Odd n)
    (T : Triangulation n) : False := by
  obtain ⟨i, hcomplete⟩ := T.has_complete
  have harea := T.equal_areas i
  have hnonzero := T.nonzero_areas i
  have hin := T.vertices_in_square i
  -- v₂(2/n) = 1 for odd n
  have hv2_target : padicValRat 2 (2 / n : ℚ) = 1 := padicValRat_two_div_odd hn hodd
  -- v₂(|x|) = v₂(x) for x ≠ 0
  have hv2_abs : padicValRat 2 |(T.triangles i).twiceArea| =
                 padicValRat 2 (T.triangles i).twiceArea := by
    rcases abs_choice (T.triangles i).twiceArea with h | h
    · rw [h]
    · rw [h, padicValRat.neg]
  -- |twiceArea| = 2/n, so v₂(twiceArea) = 1
  have hv2_one : padicValRat 2 (T.triangles i).twiceArea = 1 := by
    rw [← hv2_abs, harea, hv2_target]
  -- Complete triangle has v₂(twiceArea) ≤ 0
  have hv2_le : padicValRat 2 (T.triangles i).twiceArea ≤ 0 :=
    v2_complete_triangle_constraint hcomplete hin hnonzero
  -- Contradiction: 1 ≤ 0
  omega

/-!
## Part 7: Main Theorem (PROVED from axiom)
-/

theorem monsky (n : ℕ) (hn : n ≠ 0) (T : Triangulation n) : Even n := by
  by_contra hodd_n
  have hodd : Odd n := Nat.not_even_iff_odd.mp hodd_n
  exact v2_contradiction hn hodd T

/-!
## Summary

This proof of Monsky's theorem uses ONE axiom:

  `v2_complete_triangle_constraint`:
  For a complete triangle in [0,1]² with nonzero area, v₂(area) ≤ 0.

This axiom captures the key algebraic content of Monsky's lemma.
Proving it requires detailed analysis of the determinant formula
combined with the 2-adic coloring constraints.

The `has_complete` field in Triangulation encodes the Sperner property.
A full proof would derive this from the boundary coloring (corners 2,0,1,2).

What IS proved:
✓ 2-adic coloring is well-defined
✓ Corner colors are 2, 0, 1, 2
✓ v₂(2/n) = 1 for odd n
✓ The contradiction follows from the v₂ constraint
✓ Monsky's theorem follows

What is ASSUMED:
⚠ v2_complete_triangle_constraint (requires ~200 lines)
⚠ has_complete in Triangulation (requires Sperner's lemma ~300 lines)

Total unproved content: ~500 lines of detailed case analysis
-/

#print axioms monsky

end MonskyV2

end
