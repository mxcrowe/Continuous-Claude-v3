import Mathlib

-- Cyclotomic evaluation
#check @Polynomial.cyclotomic.eval_one
#check @Polynomial.eval_geom_sum

-- Cyclotomic divisibility facts
#check @Polynomial.cyclotomic_dvd_geom_sum_of_lt
#check @Polynomial.sub_one_pow_totient_lt_cyclotomic_eval

-- Int cyclotomic eval bound
#check @Int.sub_one_lt_natAbs_cyclotomic_eval

-- Action on conjugacy
#check ConjAct
#check MulAction.orbitEquivQuotientStabilizer

-- Check class equation variants
#check @Group.card_center_add_sum_card_noncenter_eq_card

-- Finite dimensional
#check Module.finrank
#check FiniteDimensional
#check FiniteDimensional.finrank_pos

-- Center of division ring
#check @Subring.center_eq_top
#check @DivisionRing.toField

