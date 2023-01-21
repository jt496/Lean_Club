import tactic
import data.nat.basic
import data.finset.basic
import algebra.big_operators
open_locale big_operators


open nat finset


/- If we want to talk about finite sums then we need to use `finsets`

If `n : ℕ` then `range n` is the finset consisting of {0,1,..,n-1}`
So in particular `range n.succ = {0,1,...,n}`
-/

/-  
Division (and subtraction) over ℕ can be painful in Lean.  
Clearing denominators can be be very helpful. -/

lemma clear_denom {n k m: ℕ} (hnz : 0 < m): m * n = k → n = k / m :=
begin
  intro h,
  rw ←h , 
  rw mul_div_right n hnz,
end


lemma sum1 (n : ℕ) :  ∑ i in range n.succ, i  = (n * (n+1))/2:=
begin
  apply clear_denom (by norm_num :0 < 2),
  induction n with n hn,
  { 
    refl,
  },
  {
   rw [sum_range_succ, mul_add, hn,succ_eq_add_one], 
   ring,   
  },
end

lemma sum2 (n : ℕ ) : ∑ i in range n.succ, i^2  = (n * (n+1)*(2*n+1))/6:=
begin
  apply clear_denom (by norm_num : 0 < 6),
   induction n with n hn,
  { 
    refl,
  },
  {
   rw [sum_range_succ, mul_add, hn,succ_eq_add_one], 
   ring,   
  },
end

lemma sum3 (n : ℕ ) : ∑ i in range n.succ, i^3  = ((n * (n+1))^2)/4:=
begin
  apply clear_denom (by norm_num : 0 < 4),
   induction n with n hn,
  { 
    refl,
  },
  {
   rw [sum_range_succ, mul_add, hn,succ_eq_add_one], 
   ring,   
  },
end


-- Unfortunately as soon as subtraction enters the picture things are more complicated
lemma sum4 (n : ℕ ) : ∑ i in range n.succ, i^4  = (n*(n + 1)*(2*n + 1)*(3*n^2 + 3*n - 1))/30:=
begin
  apply clear_denom (by norm_num : 0 < 30),
  induction n with n hn,
  { 
    refl,
  },
  {
    cases n with n hn, 
    refl,
    -- this next intermediate result will allow us to remove all subtraction
    have h3: ∀(m:ℕ),3 *m.succ - 1 = 3 * m + 2,
    { intro m, rw mul_succ, refl,},
    rw [sum_range_succ, mul_add, hn, succ_eq_add_one,succ_eq_add_one],
    -- the next line banishes all subtraction
    rw [nat.add_sub_assoc, nat.add_sub_assoc, h3,h3],
    -- no more subtraction!
    ring, -- solves the main goal 
    --leaving us to justify the two uses of nat.add_sub_assoc
    rw [mul_succ], linarith,
    rw [mul_succ], linarith,
  },
end




/- 
# Coercions and casts
Lean understands the type ℚ and allows us to coerce naturals into rationals 
Once we coerce the LHS of an equality Lean automatically coerces the RHS 
since only terms of the same type can be compared with `=` so there is no other option.

You will see `↑0`,`↑n` etc in the Infoview during the next proof.

These are the results of coercing 0 and n respectively, from ℕ to ℚ, 

Lean knows that `↑0` is just `0` in ℚ  but you need to tell it to use this fact 
with  `cast_zero` -/

lemma sum4Q (n : ℕ ) : ∑ i in range n.succ, (i^4 : ℚ)  = (n*(n + 1)*(2*n + 1)*(3*n^2 + 3*n - 1))/30:=
begin
  induction n with n hn,
  { 
    rw [range_one,sum_singleton,cast_zero,zero_mul,zero_mul,
        zero_mul,zero_div,zero_pow zero_lt_four],
  },
  {
    rw [sum_range_succ, hn ], 
    field_simp, ring,
  },
end

lemma sum6Q (n : ℕ ) : (∑ i in range n.succ, i^6 : ℚ)  = (n*(n + 1)*(2*n + 1)*(3*n^4 + 6*n^3 - 3*n + 1))/42:=
begin
  induction n with n hn,
  { 
    rw [range_one,sum_singleton,cast_zero,zero_mul,zero_mul,
        zero_mul,zero_div,zero_pow],
    norm_num,
  },
  {
    rw [sum_range_succ, hn], 
    field_simp, ring,
  },
end


