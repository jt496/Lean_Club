import tactic.core
import data.nat.basic
namespace nat
/-
In Lean the natural numbers `ℕ` are defined as follows:

inductive nat
| zero : nat
| succ (n : nat) : nat

This means that there are two ways to construct a natural number `n:ℕ`
Either `n` is `zero` or it is the successor of a previously constructed 
natural number `succ n`. -/

--#check zero
--#reduce succ 3
--#check succ (succ zero)
--#check zero.succ
end nat 


/-
Addition is defined inductively in Lean:

def add : ℕ → ℕ → ℕ
| a  zero     := a                    --  a + 0 := a
| a  (succ b) := succ (add a b)       --  a + (b + 1) := (a + b) + 1

-/

-- We will use the `dot` notation for the successor function.
/--  n + 1 = n.succ -/
lemma Succ_eq_add_one (n : ℕ) :  n.succ = n + 1  :=
begin 
  sorry,
end

/- 
We are now proving lemmas/theorems that already exist in `mathlib`.

To avoid clashes we will use the same names as `mathlib` but they will be Capitalised.

We won't use high level tactics such as `norm_num` or `linarith` but we will 
need to use earlier results as we progress (mainly with `rw` and `apply` tactics).   

For a much more complete tour of the natural numbers check out the Natural Numbers Game:

https://www.ma.imperial.ac.uk/~buzzard/xena/natural_number_game/

-/

lemma Add_zero (n : ℕ) : n + 0 = n :=
begin
  sorry,
end

/-- a + (b + 1) = (a + b) + 1 -/
lemma Add_succ (a b : ℕ) : a + b.succ = (a + b).succ:=
begin
  sorry,
end

/-
# New tactic for ℕ: induction 

If we want to prove `∀ (n:ℕ), P n` then we can use 
`induction n` which requires us to prove two things: 
`P 0` and `P n →  P n.succ`

# New tactic for structured proofs: have 

Sometimes we want to prove intermediate results within a proof.

We can do this using the `have` tactic. 

If we need to prove `h : P` (ie a proof that the proposition P is true)
then we can do this as follows:

.... middle of a proof
have h : P, 
{
  proof of P,
},
.... continue proof

We now have `h : P` in the local context.

# Variant of rw : rwa 

If we have term in the local context `h1 : P` and after `rw h2` our goal becomes `⊢ P`
then `rwa h2` will do the `rw h2, exact h1` in one step. 

(The `a` in `rwa` stands for `assumption` which is yet another tactic that will work whenever 
our goal is closed by a term in the local context.) -/

lemma Zero_add (n : ℕ) : 0 + n = n :=
begin
  induction n with n hn,
  { 
    -- prove 0 + 0 = 0
    
    sorry,
  },
  { -- ⊢ 0 + n.succ = n.succ  and we have `hn : 0 + n = n` our inductive hypothesis 
    -- a useful intermediate step is to prove `0 + n.succ = (0 + n).succ`
    have h : 0 + n.succ = (0 + n).succ,
    {
      
      sorry,
    },

    sorry,
  },
end

lemma Succ_add (a b : ℕ) : a.succ + b = (a + b).succ:=
begin
  induction b with b hb,
  { 
    sorry
  },
  {
    sorry
  },
end


/- Digression: how do we know that 0 ≠ 1? 
This is one of the axioms of the natural numbers (Peano arithmetic)
and it is built into Lean's model of ℕ.  -/

theorem Succ_ne_zero (n : ℕ) : n.succ ≠ 0 :=
begin 
  intro h, 
  --exact nat.no_confusion h, 
  contradiction,
end

-- Lean also knows that the successor function is injective (by definition)
theorem Succ.inj (n m : ℕ) : n.succ = m.succ → n = m :=
begin
  exact nat.succ.inj,
end

/- Our next result says that `+` is `associative`

In Lean `a + b + c` is defined as `(a + b) + c` so whenever you see an expression such as `a + b + c + d`
you need to remember how this is read by Lean: `((a + b) + c) + d`

We know that the brackets aren't required, but in Lean you need to prove this.
-/
--#check 1 + (2 + 4) -- brackets
--#check (1 + 2) + 4 -- no brackets

lemma Add_assoc (a b c : ℕ) : (a + b) + c = a + (b + c):=
begin
  induction c with c hc,
  {
    sorry
  },
  {
    sorry
  },
end

lemma Add_comm (m n : ℕ) : m + n = n + m :=
begin
  sorry,
end

/-
Multiplication is also defined inductively in Lean.

def mul : ℕ → ℕ → ℕ
| a 0     := 0                      --  a * 0 := 0
| a (b + 1) := (mul a b) + a        --  a * (b + 1) = (a * b) + a  -/

lemma Mul_zero (n : ℕ) : n * 0 = 0:=
begin
  sorry,
end


lemma Mul_succ (m n : ℕ) : m * n.succ = m * n + m:=
begin
  sorry,
end

lemma Succ_mul (m n : ℕ) : n.succ * m =  n * m + m:=
begin
  induction m with m hm,
  {
    sorry
  },
  {
    sorry
  },
end

lemma Zero_mul (n : ℕ) : 0 * n = 0:=
begin
  sorry,
end

lemma Mul_one (n : ℕ) : n * 1 = n:=
begin
  sorry,
end

lemma One_mul (n : ℕ) : 1 * n = n:=
begin
  sorry,
end

lemma Mul_add (a b c: ℕ) : a*(b + c) = a*b + a*c:=
begin
  induction a with a ha,
  {
    sorry
  },
  {
    sorry
  },
end
 
lemma Add_mul (a b c: ℕ) : (b + c)*a = b*a +c*a:=
begin
  sorry,
end

lemma Mul_comm (a b : ℕ) : a * b = b * a :=
begin
  sorry,
end

lemma Mul_assoc (a b c : ℕ) : a * b * c = a * (b * c):=
begin
  sorry,
end

lemma Pow_zero (n : ℕ) : n ^ 0 = 1:=
begin
  sorry,
end

lemma Pow_succ (a b : ℕ) : a^b.succ= a* a^b:=
begin
  sorry,
end

lemma Pow_one (n : ℕ) : n ^ 1 = n:=
begin 
  sorry,
end

/-
# New use of tactic : cases 

We don't need induction to prove our next result, but we do need to consider the cases of zero and 
successor separately. The `cases n` tactic does exactly this.   -/

lemma Zero_pow (n : ℕ) (h : n ≠ 0): 0 ^ n = 0:=
begin
  cases n with n hn,
  {
    sorry
  },
  {
    sorry
  },
end


lemma One_pow (n : ℕ) : 1 ^ n = 1:=
begin
  sorry,
end


lemma Pow_add (a b c: ℕ): a^(b + c)=a^b*a^c:=
begin
  induction c with c hc,
  {
    sorry
  },
  {
    sorry
  },
end

lemma Pow_mul (a b c : ℕ) : a^(b * c) = (a^b)^c :=
begin
  sorry,
end


lemma Two_eq_one_add_one : 2 = 1 + 1:=
begin
  sorry,
end

lemma Two_mul (n : ℕ) : 2*n = n + n:=
begin
  sorry,
end

lemma Three_mul (n : ℕ) : 3*n = n + n + n:=
begin
  have : 3 = 2 + 1, {
    sorry,
  },
  sorry,
end

lemma Pow_two (n : ℕ) : n^2 = n*n:=
begin
  sorry,
end

lemma Add_sq (a b : ℕ) : (a + b)^2 = a^2 + 2*a*b + b^2 :=
begin
  sorry,
end

lemma Pow_three (n : ℕ) : n^3 = n*n*n:=
begin
  have : 3 = 2 + 1, {
    sorry,
  },
  sorry,
end

lemma Add_cube (a b : ℕ) : (a + b)^3 = a^3 + 3*a^2*b + 3*a*b^2 + b^3:=
begin
  sorry, -- ring
end


