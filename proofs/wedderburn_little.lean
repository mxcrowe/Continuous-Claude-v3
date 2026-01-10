/-
  Wedderburn's Little Theorem

  Statement: Every finite division ring is commutative (hence a field).

  This theorem was proven by Joseph Wedderburn in 1905. The proof in Mathlib
  uses the following key components:

  1. **Strong Induction**: Prove by strong induction on |D| that the center
     equals the whole ring.

  2. **Class Equation**: For the group of units D×, we have:
     |D×| = |Z×| + ∑_{conjugacy classes not in center} |class|

     which translates to:
     q^n - 1 = (q - 1) + ∑ |conjugacy class|

     where q = |Z| (center) and n = dim_Z(D).

  3. **Cyclotomic Polynomials**: The n-th cyclotomic polynomial Φₙ(q) divides
     q^n - 1. For each conjugacy class of size (q^n - 1)/(q^d - 1) where d | n
     and d < n, we have Φₙ(q) | (q^n - 1)/(q^d - 1).

  4. **Key Contradiction**: If n > 1, then Φₙ(q) | (q - 1) by the class equation,
     but |Φₙ(q)| > q - 1 for q > 1 and n > 1, giving a contradiction.
     Therefore n = 1, meaning D = Z (the center), so D is commutative.
-/

import Mathlib.RingTheory.LittleWedderburn

/-!
## The Theorem

Mathlib provides this as an instance: any finite division ring is automatically
promoted to a Field (which requires commutativity).
-/

-- The main theorem (Mathlib's formalization)
#check @littleWedderburn
-- littleWedderburn : ∀ (D : Type*) [inst : DivisionRing D] [inst : Finite D], Field D

/-!
## Example Usage

We can derive consequences from this theorem.
-/

-- Every finite division ring has commutative multiplication
-- The Field instance provided by littleWedderburn has the same multiplication
-- as the original DivisionRing, so we can use its mul_comm field directly
theorem finite_division_ring_comm (D : Type*) [DivisionRing D] [Finite D]
    (x y : D) : x * y = y * x :=
  (littleWedderburn D).mul_comm x y

-- A finite domain is a field (Mathlib also provides this)
#check @Finite.isDomain_to_isField
-- Finite.isDomain_to_isField : ∀ (D : Type*) [inst : Finite D] [inst : Ring D]
--                               [inst : IsDomain D], IsField D

/-!
## Proof Outline (in prose)

**Goal**: Show that for any finite division ring D, D is commutative.

**Approach**: Show the center Z(D) equals D by proving Z(D) = ⊤.

**Step 1 - Setup**:
Let Z = Z(D) be the center. Assume for contradiction that Z ≠ D.
Since Z is a subring that's a finite division ring with all proper subrings
commutative (by induction), Z is a field. Let q = |Z|.

D is a finite-dimensional Z-vector space. Let n = dim_Z(D).
Then |D| = q^n.

**Step 2 - Class Equation**:
Consider the group of units D×. Its center is Z× (units of the center).
The class equation gives:
  |D×| = |Z(D×)| + ∑_{conjugacy classes outside center} |class|

  q^n - 1 = (q - 1) + ∑ conjugacy class sizes

**Step 3 - Conjugacy Class Sizes**:
For x ∈ D× not in the center, let Z_x = centralizer of x in D.
Then Z ⊂ Z_x ⊂ D properly, and Z_x is a finite division ring containing Z.
So |Z_x| = q^d for some d | n with 1 < d < n.

The conjugacy class of x has size |D×|/|Z_x×| = (q^n - 1)/(q^d - 1).

**Step 4 - Cyclotomic Divisibility**:
The n-th cyclotomic polynomial Φₙ(X) satisfies:
  X^n - 1 = ∏_{d|n} Φ_d(X)

Key fact: For d | n with d < n, we have Φₙ(q) | (q^n - 1)/(q^d - 1).
Thus Φₙ(q) divides each conjugacy class size.

By the class equation:
  Φₙ(q) | (q^n - 1) - (sum of conjugacy class sizes)
  Φₙ(q) | (q - 1)

**Step 5 - Contradiction**:
For n > 1 and q > 1, we have |Φₙ(q)| > q - 1.
(This is the key number-theoretic lemma.)

Since |Φₙ(q)| > q - 1 but Φₙ(q) | (q - 1), we need |q - 1| ≥ |Φₙ(q)|.
Contradiction!

Therefore n = 1, meaning dim_Z(D) = 1, so D = Z = center, hence D is
commutative.

QED
-/

-- Verify the proof compiles
example (D : Type*) [DivisionRing D] [Finite D] : Field D := inferInstance
