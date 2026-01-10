import Mathlib

-- Cyclotomic evaluation
#check @Polynomial.cyclotomic.eval_one
#check @Polynomial.eval_geom_sum

-- Int divisibility  
#check Int.dvd_sub
#check Int.natAbs

-- More cyclotomic
#check @Polynomial.cyclotomic_prime
#check @Polynomial.X_pow_sub_one_dvd_iff

-- Action on conjugacy
#check ConjAct
#check MulAction.orbitEquivQuotientStabilizer
#check MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group
#check MulAction.card_fixedPoints

-- Subgroups
#check @Subgroup.card_subgroup_dvd_card
#check Subgroup.index

-- Check class equation variants
#check @Group.card_center_add_sum_card_noncenter_eq_card

-- Dimension over center
#check Module.finrank
#check FiniteDimensional

