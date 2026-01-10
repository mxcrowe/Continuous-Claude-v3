import Mathlib

-- Key divisibility lemma for cyclotomic
#check @Int.cyclotomic_eval_dvd_difference

-- Product formula for x^n - 1
#check @Polynomial.prod_cyclotomic_eq_X_pow_sub_one

-- Evaluation of product
#check @Polynomial.eval_prod

-- Integer arithmetic
#check @Int.natAbs_pos
#check @Int.abs_eq_natAbs
#check @Int.toNat_of_nonneg

-- Absolute value bound for cyclotomic
#check @Polynomial.sub_one_pow_totient_lt_cyclotomic_eval

-- Additional cyclotomic facts  
#check @Int.eval_int_cyclotomic_pos
#check @Int.cyclotomic_two
#check @Nat.lt_pow_sub_of_one_lt

-- Finrank and powers
#check @Module.finrank_pow_card_eq_pow
#check @card_eq_pow_finrank

-- Center as subalgebra
#check @Subalgebra.center

-- Units subgroup
#check @Subring.center
#check @Units.val

