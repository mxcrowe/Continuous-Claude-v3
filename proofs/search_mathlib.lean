import Mathlib

-- Search for cyclotomic polynomial primitives
#check Polynomial.cyclotomic
#check Polynomial.prod_cyclotomic_eq_X_pow_sub_one
#check Polynomial.cyclotomic_dvd_X_pow_sub_one

-- Class equation / conjugacy classes
#check MulAction.card_eq_sum_card_orbits
#check MulAction.orbit
#check MulAction.stabilizer
#check MulAction.card_orbit_mul_card_stabilizer_eq_card_group

-- Centralizers
#check Subgroup.centralizer
#check Subgroup.center

-- Division rings
#check DivisionRing
#check Subring.center
#check Subfield

-- Finite fields
#check Fintype.card
