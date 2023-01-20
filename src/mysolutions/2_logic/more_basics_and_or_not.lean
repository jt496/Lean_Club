import tactic
variables (P Q R S : Prop)

/- 
Lean has the logical connectives  `and`, `or`, `not` built-in.

Lean has special tactics to help us deal with them. 

New tactics: `cases`, `split`, `left` and `right`

# And (conjunction)

 `P and Q` is written  `P ∧ Q`. This is true iff P and Q are both true.

# cases 

 Given `h : P ∧ Q` in the local context we can use `cases h with hp hq` 
 to get the two parts so `hp : P` and `hq : Q` replace `h : P ∧ Q` -/ 

-- 01
example (h : P ∧ Q) : P:=
begin
  cases h with hp hq, 
  -- Now have 
  -- hp : P, 
  -- hq : Q
  exact hp,
end

/- If our goal is `⊢ P ∧ Q` then we can use `split` to create two new goals
one `⊢ P` and the other `⊢ Q` -/

-- 02
example (hp : P) (hq : Q) : P ∧ Q :=
begin
  split,
/-
2 goals
PQ: Prop
hp: P
hq: Q
⊢ P
PQ: Prop
hp: P
hq: Q
⊢ Q-/
  { -- Inside `{ }` we only see the 1st goal
    exact hp,
  },
  { -- Inside `{ }` we only see the 2nd goal
    exact hq,
  },
end

/- 
Dot notation: if we have `(hpq : P ∧ Q)` then `hpq.1 : P` and `hpq.2 : Q`

(This `dot` notation is very common in Lean.)

Conversely if we have `(hp : P)` and `(hq : Q)` then `⟨hp,hq⟩ : P ∧ Q` 
i.e. `⟨hp,hq⟩` is a term of type `P ∧ Q`. 

The angled brackets are typed `\<` and `\>` -/
-- 03
example (hpq : P ∧ Q) : Q ∧ P :=
begin
  cases hpq with hp hq, 
  split, 
  {
    exact hq,
  }, 
  { 
    exact hp,
  },
  -- or more simply `exact ⟨hpq.2,hpq.1⟩,`
end

-- Having introduced `→` and `∧` we get `iff` (written `↔`) for free
-- `P ↔ Q` is:  `P → Q` and `Q → P`
-- 04
example : P ∧ Q ↔ Q ∧ P := 
begin
  split,
  {
    intro hpq, cases hpq with hp hq,
    split, 
    {
      exact hq,
    },
    {
      exact hp,
    },
  },
  {
    sorry,
  }
end

-- 05 
example : P ∧ Q → Q :=
begin
  sorry,
end

-- in Lean `P ∧ Q ∧ R` means `P ∧ (Q ∧ R)` (∧ is right-associative)
-- Find a single line `exact ...` solution to the following.
-- (Hint: what are h.1 and h.2 in this example?)
-- 06
example  (h: P ∧ Q ∧ R ∧ S ) : R :=
begin
  sorry,
end

-- 07
example : P → Q → P ∧ Q :=
begin
  sorry,
end

-- 08
example : P ∧ Q → Q ∧ R → P ∧ R :=
begin
  sorry,
end

-- 09
example :  P ∧ R ∧ Q → Q ∧ P ∧ R := 
begin
  sorry,
end

/-
   # Or (disjunction)

The proposition `P or Q` is written  `P ∨ Q`. 
 
 `P ∨ Q` is true iff P is true or Q is true.

If our goal is `⊢ P ∨ Q` then we can accomplish this by either giving a term
of type `P` or a term of type `Q`. We indicate which by using `left` for `P`
and `right` for Q.
 -/

-- 10
example (hp : P) : Q ∨ P :=
begin
  right, -- Goal is now `⊢ P`
  exact hp,
end

/-
Given `(hpq : P ∨ Q)` in the local context we can use `cases hpq with hp hq` 
to split our goal into two subgoals, one in which `hp : P` and the other
in which `hq : Q`
-/
-- 11
example (hpq : P ∨ Q) : Q ∨ P :=
begin
  cases hpq with hp hq, 
  /-
2 goals
case or.inl
PQ: Prop
hp: P
⊢ Q ∨ P
case or.inr
PQ: Prop
hq: Q
⊢ Q ∨ P-/
{
  right, exact hp,
},
{
  left, exact hq,
}
end

-- 12 
example : (P ∨ Q) ∧ (P → Q) → Q :=
begin
  sorry,
end

-- 13 
example : (P ∨ Q) ∧ (P ∨ R) → P ∨ (Q ∧ R):=
begin 
  sorry,
end

-- 14 
example : (P ∨ Q) ∧ (R ∨ S) → (P ∧ R) ∨ (P ∧ S) ∨ (Q ∧ R) ∨ (Q ∧ S):=
begin
  sorry, 
end
/-
There are two special propositions : `false` and `true`

To prove `true` we use `triv`

You shouldn't be able to prove `false`.

If you have `false` in the local context then you have a `contradiction`
-/

-- 15
example : true := 
begin
  triv, 
end

-- 16
example: P → true :=
begin
  sorry
end

-- 17
example : false → P:=
begin
  intro f, 
  contradiction,
end

-- 18
example : false → true:=
begin
  sorry, 
end

-- 19 
example : true → false → true → false → true :=
begin
  sorry,
end

/- 
# Negation

If `P : Prop` then `not P` is denoted `¬ P` this is defined to be `P → false`  -/
-- 20
example : ¬ P ↔ (P → false):=
begin 
  refl,
end

-- 21
example : ¬ true → false :=
begin
  sorry,
end

-- 22
example : ¬ false → true :=
begin
  sorry,
end

-- 23
example : P → ¬¬P :=
begin
  sorry,
end

-- 24
example (hp : P) (hnp : ¬ P) : Q ∧ R → ¬ Q  :=
begin
  sorry,
end

-- Can you explain how the following proof works?
-- 25
example (hp : P) (hnp : ¬ P) : Q :=
begin
  cases (hnp hp), -- Hint: what is `(hnp hp)`?
end

