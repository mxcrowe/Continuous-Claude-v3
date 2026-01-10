import Mathlib

-- Search for key lemmas that might exist in Mathlib about cyclotomic divisibility
-- These are the components we need to build

-- For proving Φₙ(q) | (q^n - 1)/(q^d - 1) when d | n, d < n:
-- This relates to the fact that Φₙ is a factor of X^n - 1

-- Find the key number theoretic bound
#check @Polynomial.sub_one_pow_totient_lt_cyclotomic_eval
-- This gives us: (q-1)^φ(n) < Φₙ(q) for q > 1, n ≥ 2
-- Since φ(n) ≥ 1 for n ≥ 1, we get q - 1 < Φₙ(q) when n ≥ 2

-- Check if we have the divisibility: Φₙ(q) | (q^d - 1)/(q^{d/e} - 1) for divisors
-- This comes from the factorization X^n - 1 = ∏_{d|n} Φ_d(X)

#check @Polynomial.eval_prod_cyclotomic_eq

-- We need: for d | n with d < n, Φₙ(q) | (q^n - 1)/(q^d - 1)
-- This follows from: (q^n - 1)/(q^d - 1) = ∏_{e | n, e ∤ d} Φ_e(q) for appropriate conditions

-- Division in int
#check @Int.ediv_dvd_ediv  
#check @Int.mul_div_assoc

-- For cyclotomic evaluated at integers
#check @Polynomial.cyclotomic_eval_int

