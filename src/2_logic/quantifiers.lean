import tactic
import data.nat.prime_norm_num
variables (P Q  : Prop)
variables (α β : Type)
variables (R S: ℕ → Prop)
open function nat

/-
# Quantifiers 

# Existential ∃ tactics: use / cases

If our goal is `⊢ ∃(x:A), P` (where P may depend on x) and we know that `a : A` is a term
with the required property, then we can tell Lean to `use a` and our goal will change to `⊢ P`.  
In fact if we can prove `P` using `refl` then Lean will do this automatically.

If we have `h : ∃(x:A), P` in the local context then  `cases h with x hx` 
will give us `x : A` and `hx : P` in our local context.

[Notice how similar this is to how we used `cases h with hp hq` with `h : P ∧ Q`]

# Universal ∀ tactics: intro, apply, specialize  

If we have a goal `⊢ ∀(n:ℕ), P n` then we can use `intro n` and the our goal will
change to `⊢ P n`. (For Lean a `∀` statement is basically a function.)

If we have `(h : ∀(x:A), P x)` and we want to use this hypotesis for a particular choice 
of `x` then we can use `specialize h x` or (if goal is `⊢ P x`) just `apply h`

# New tactics for numerical/arithmetic proofs: norm_num and linarith

`norm_num` can prove results involving actual numerical expressions such as `4*3^2 < 50`

`linarith` can prove results involving linear arithmetic including inequalities. 

# New tactics to help us make sense of definitions: unfold and dsimp

`unfold blah` will unfold a definition of `blah`in the goal. 
Use unfold when you're not sure what a definition means.

`dsimp` will simplify the goal using definitions. 
Use dsimp if the goal looks unreadable.  -/

-- 01
example : ∃(n:ℕ), n = 20 :=
begin
  use 20, 
end

-- 02
example : ∃(n:ℕ), 200 < n:=
begin
  use 201, 
  norm_num,  
end

-- 03 
example : ∃(P:Prop), P:=
begin
  sorry,
end

-- 04
example : ∃ (P:Prop), ¬ P → P:=
begin
  sorry,
end

-- 05 
example (h: ∃(n:ℕ), n.prime ∧ 10 < n) : ∃(k:ℕ), k.prime ∧ 7 < k :=
begin
  cases h with n hn,
  cases hn with hp hv,
  use n,
  split, {exact hp},
  linarith, -- another tactic for proving results using linear arithmetic 
end

-- 06 Hint : `even n` is defined to be `∃(r:ℕ), n = r + r`
example (n : ℕ) : even (4 * n):=
begin
  unfold  even,
  use (2*n), 
  sorry,
end

-- 07 
example (h: ∃(n:ℕ), even n ∧ even (n+1)) : ∃(k:ℕ), even (2*k + 1) :=
begin
  sorry,
end

-- 08
example : ∀ (n:ℕ), ∃ (k:ℕ), n < k:=
begin
  intro n, -- note the similarity to defining a function from ℕ
  sorry,
end

-- 09
example : ∀(n:ℕ), R n ∧ S n → ∃(k:ℕ), S k:=
begin
  sorry,
end

-- 10
example (f: ℕ → ℕ) (k : ℕ): surjective f → ∃(n:ℕ), f n = 2023^k := 
begin
  unfold surjective,
  sorry,
end

-- 11 Hint: if we have `h : ∀ (n : ℕ), f n = g n` then `rw (h n)` will replace `f n` by `g n` in the goal. 
example (f g: ℕ → ℕ) (h : ∀ n, f n = g n):  injective f → injective g:=
begin
  sorry,
end

-- 12
example (f : ℕ → ℕ) (m n : ℕ): bijective f → f m = f n → m = n:=
begin
  sorry,
end

/-
If (a b: ℕ) then `a ∣ b` means `a divides b`, ie. `∃(c:ℕ), b = a*c`
Note that this symbol is `\|` not `|` which is obviously not the same...-/

-- 13  
example (h : ∀n:ℕ, 3 ≤ n → 2 ∣ n → ¬n.prime ) :∀(k:ℕ), even k → 3 ≤ k → ¬ k.prime := 
begin
  intros k hk1 hk2, 
  apply h,
  exact hk2,
  cases hk1 with r hr,
  sorry,
end

-- We can use `⟨n,h⟩` notation for `∃ n, h`
-- 14 
example (n : ℕ)(h : n.prime) : ∃ (k : ℕ), k.prime:=
begin
  exact ⟨n,h⟩, 
end

-- 15 what if we don't have the hypothesis `n.prime`
example  : ∃ (k : ℕ), k.prime:=
begin
  use 2, 
  exact nat.prime_two, -- here we used `mathlib` 
end

-- 16 To complete the next proof we need to show 2027 is prime. Luckily `norm_num` will do it.
example  : ∃ (k : ℕ), 2026 < k ∧ k.prime:=
begin
  use 2027,
  sorry,
end

/-
# New tactic: push_neg

Given a proposition with quantifiers involving a negation  `push_neg` will push the negation inside 
the expression as far as possible 

Like `rw` we can also use it to simplify terms in the local context eg `push_neg at h`  -/

-- 17
example : ¬ ∃ (n:ℕ), ∀ (k:ℕ), k < n:=
begin
  push_neg,
  sorry,
end

-- 18 Hint: If m,n ∈ ℕ then `max m n` is their maximum, `norm_num` may be useful again here
example : ∀ (m: ℕ), ∀ (n: ℕ), ∃ (k:ℕ), m ≤ k ∧ n ≤ k:=
begin
  sorry,
end


variable (pr : α → Prop) 
/- A function from a type to Prop is usually called a `predicate` 
   For example `nat.prime: ℕ → Prop` -/

-- 19 
example : (∀ (a:α), pr a) ↔ ¬ ∃ (b:α), ¬ pr b:=
begin
  split,
  {
    sorry,
  }, 
  {
    sorry,
  }
end

/-
In the previous example we had a `split` and the two parts used almost the same 
code. One way to do such proofs is to use the `try {code}` tactic, which tries the
`code` but doesn't complain if it fails. 
-/
-- 20 
example : (∀ (a:α), pr a) ↔ ¬ ∃ b:α, ¬ pr b:=
begin
  split; -- note `;` 
  {
    intros h1,
    try {push_neg},  -- this succeeds the 1st time but silently fails the 2nd time
    try {push_neg at h1},  --this succeeds the 2nd time but silently fails the 1st time
    exact h1,
  }, 
end

-- 21 
example : ∃ (n: ℕ), n + 2 = 5 ∧ 2 * n = 6:=
begin
  sorry,
end

-- 22 beware the divides `∣` symbol is not `|` but `\|` 
example : ¬(∀ n: ℕ, n.prime ∨ (2 ∣ n)):=
begin
  sorry,
end


-- 23 Hint: even n := ∃(r:ℕ), n = r + r
example : ∀ (n m:ℕ), even n ∧ even m → even (n+m):=
begin
 sorry,
end

-- A relation r on ℕ
variables (r : ℕ → ℕ → Prop)
-- 24
example:  reflexive r → r 17 17:=
begin
  unfold reflexive,
  sorry,
end

-- 25
example : symmetric r →  r 13 2 → r 2 13:=
begin
  unfold symmetric,
  sorry,
end

-- 26
example (a b c : ℕ) : equivalence r → r a b →  r b c →  r a c:=
begin
  unfold equivalence transitive,
  sorry,
end

-- 27
example (a b c : ℕ) : equivalence r → r a b →  r b c →  r c a:=
begin
  sorry,
end

-- 28
example (h1 : symmetric r) (h2: ∃ (a b:ℕ), r a b ∧ a ≠ b) : 
(∀ {m n: ℕ}, r m n → r n m → m = n) → false :=
begin 
  sorry,
end

-- 29 Hint: dsimp may be useful here (you'll know when to use it!)
example : ∃! (n:ℕ), ∀ (k:ℕ), n ≤ k :=
begin
  sorry,
end

-- 30
example : ¬∃ (n:ℕ), ∀ (k:ℕ), k ≤ n :=
begin
  sorry,
end

/- If we want to define a function and then use it we use the `def` keyword 

 We can define the relation `parity` on the integers ℤ
 `parity a b` holds iff `a + b` is even -/
def parity : ℤ → ℤ → Prop :=
begin
  intros a b, 
  exact even (a+b),
end

-- Lets prove this is an equivalence relation
-- 31
example : equivalence parity :=
begin
  split,
  {
    sorry,
  },
  split,
  {
    sorry,
  },
  {
    sorry,
  },
end

-- The relation `r a b` iff `a = b mod m` iff `m ∣ (b-a)`
def mod (m: ℤ) : ℤ → ℤ → Prop :=
begin
  intros a b, 
  exact m ∣ (b-a),
end

-- 32
example :∀ (m:ℤ), equivalence (mod m) :=
begin
  sorry,
end

