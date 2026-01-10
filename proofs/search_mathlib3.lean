import Mathlib

-- Cyclotomic divisibility
#check @Int.cyclotomic_eval_sub_one_ne_zero
#check @Polynomial.cyclotomic_pos
#check @Polynomial.cyclotomic_coeff_zero

-- Units of division ring
#check @DivisionRing.instGroupUnits
#check Units.instGroup

-- Centralizer in units
#check @Subgroup.center_units_eq_toUnits_center

-- Division ring center
#check Subring.center
#check @Subalgebra.center

-- Finite cardinality power
#check @Fintype.card_eq_pow_finrank

-- Divisors and coprime
#check Nat.divisors
#check @Int.coprime

-- Polynomials over Z
#check @Int.cyclotomic_eq_minpoly_primitiveRoot

-- Specific cyclotomic facts
#check @Polynomial.cyclotomic_eq_prod_X_sub_primitiveRoots
#check @Polynomial.degree_cyclotomic

