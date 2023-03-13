import tactic

/-
This file is an attempt to learn about classes by redefining
the class of groups as "mygroup" and proving a few simple results.

There is an exercise to prove that for any g ∈ G, the map x ↦ g⁻¹*x*g
is an isomorphism from G to G. 
-/

class my_group (G : Type*)
  extends has_one G, has_mul G, has_inv G :=
  (gp_assoc : ∀ {x y z:G} , (x*y)*z = x*(y*z) )
  (gp_mul_one : ∀ {x : G} , x*1=x )
  (gp_one_mul : ∀ {x : G} , 1*x=x )
  (gp_mul_inv : ∀ {x : G} , x*x⁻¹ =1 )
  (gp_inv_mul : ∀ {x : G} , x⁻¹ *x=1 )

class morphism {G G' : Type*} (f:G→ G') [my_group G] [my_group G'] :=
  (property : ∀ {x y : G}, f(x*y) = (f x) * (f y))

class isomorphism {G G' : Type*} (f : G → G') [my_group G] [my_group G']
  extends morphism f :=
  (injective : ∀ {x y : G}, f x=f y → x=y)
  (surjective : ∀ {y : G'}, ∃ x:G , f x = y)

def isomorphic (G G' : Type) [ my_group G] [my_group G'] : Prop :=
  (∃ f : G → G', nonempty( isomorphism f) )

--infix " ≅ ":55  := isomorphic

structure mysubgroup (G:Type*)[my_group G]:=
  (elts : set G)
  (one : (1:G) ∈ elts)
  (closure : ∀ {x y:G}, x∈ elts → y∈ elts → x*y ∈ elts)
  (inverse : ∀ {x: G}, x∈ elts → x⁻¹ ∈ elts)

structure normal_mysubgroup (G:Type*) [my_group G]
  extends mysubgroup G:=
  (normal : ∀ {x y:G}, x*y ∈ elts → y*x ∈ elts)

-- def quotient_group_as_type (G:Type*) [my_group G] (H:normal_mysubgroup G) : Type* :=
--   sorry


instance mysubgroup_to_sort {G:Type*} [my_group G] (H:mysubgroup G):
has_coe_to_sort (mysubgroup G) Type*:=
  {
    coe := λ H, subtype H.elts
  }

namespace my_group

open my_group

-- lemmas about elements of a my_group G:
variables {G:Type} [my_group G]
variables {G':Type} [my_group G']
variables {x y z :G}

-- restate the axioms as simplification lemmas, and in the my_group namespace
@[simp] lemma assoc : x*y*z = x*(y*z) := gp_assoc 
@[simp] lemma mul_one : x*1 = x := gp_mul_one
@[simp] lemma one_mul : 1*x = x := gp_one_mul
@[simp] lemma mul_inv : x*x⁻¹ = 1 := gp_mul_inv
@[simp] lemma inv_mul : x⁻¹*x = 1 := gp_inv_mul


lemma unique_left_id (h: x*y=y): x=1 :=
calc
  x = x*y*y⁻¹ : by rw [assoc,mul_inv,mul_one] ...
    = 1       : by rw [h, mul_inv]

lemma unique_left_inv (h: x*y=1) : x = y⁻¹ :=
calc
  x = x*y*y⁻¹ : by squeeze_simp ... -- squeeze_simp's  answer doesn't work
    = y⁻¹     : by rw [h, one_mul]

@[simp] lemma inv_id : (1:G)⁻¹ = 1 :=  eq_comm.mp (unique_left_inv one_mul)

-- Lemmas about my_group morphisms f:G → G' :
variables {f:G → G'} [morphism f]

@[simp] lemma mor_mul : f(x * y) = (f x)*(f y) := morphism.property
@[simp] lemma mor_id : f 1 = 1 := unique_left_id (calc (f 1)*(f 1) = f 1 : by rw [←mor_mul, one_mul])
@[simp] lemma mor_inv :f x⁻¹ = (f x)⁻¹ :=
begin
  apply unique_left_inv,
  simp [← mor_mul,inv_mul],
  exact mor_id,
end

def kernel (f:G → G') [morphism f] : mysubgroup G :=
{
  elts := {x:G | f x = 1},
  one := mor_id,
  closure := begin
    intros x y hx hy,
    rw [set.mem_set_of_eq] at *,
    have : f(x*y) = (f x) * (f y) := mor_mul,
    rw [this,hx,hy,one_mul],
    --rw @mor_mul _ _ _ _  x y f,
    --simp only [*, one_mul],
  end,
  inverse := begin
    intros x hx,
    simp only [set.mem_set_of_eq] at *,
    have : f(x⁻¹)= (f x)⁻¹ := mor_inv,
    simp only [*, inv_id],
  end
}

def image (f : G → G') [morphism f] : mysubgroup G' :=
{
  elts := {y : G' | ∃ x:G, f x = y},
  one := ⟨ 1, mor_id⟩,
  closure := begin
    intros x y hx hy,
    --simp at *,
    cases hx with gx hgx,
    cases hy with gy hgy,
    use gx*gy,
    have : f(gx*gy)=(f gx)*(f gy) := mor_mul, -- why is this not simp?
    simp only [*],
  end,
  inverse := begin
    intros x hx,
    cases hx with g hg,
    use g⁻¹ ,
    have : f g⁻¹ = (f g)⁻¹ := mor_inv, -- why is this not simp?
    simp *,
  end
}


instance mysubgroup_to_group (H : mysubgroup G) : my_group (H.elts) :=
{
  mul := begin
    intros x y,
    cases x with x hx,
    cases y with y hy,
    use x*y,
    exact H.closure hx hy,
  end,
  inv := begin
    intro x,
    cases x with x hx,
    use x⁻¹,
    exact H.inverse hx,
  end,
  one := ⟨ 1, H.one⟩,
  gp_assoc := begin
    intros x y z,
    cases x, cases y, cases z,
    simp,
  end,
  gp_mul_one := begin
    intro x,
    cases x,
    simp,
  end,
  gp_one_mul := begin
    intro x,
    cases x,
    simp,
  end,
  gp_mul_inv := begin
    intro x,
    cases x,
    simp,
  end,
  gp_inv_mul := begin
    intro x,
    cases x,
    simp,
  end
}


def inner_automorphism : G → G → G :=
  λ g x, g⁻¹ * x * g 

-- As an exercise, can you prove that an inner automorphism is an isomorphism?

instance iso_of_inner {G:Type} [my_group G] (g:G):
  isomorphism (inner_automorphism g) :=
{ 
  property :=
  begin
    intros x y,
    unfold inner_automorphism,
    sorry
  end,
  injective :=
  begin 
    sorry
  end,
  surjective :=
  begin 
    sorry
  end
}





end my_group




-- Now let's define a group with two elements I,X.
-- we first define the type C_2 with those two elements
inductive C_2
| I : C_2
| X : C_2


open C_2  -- this allows us to type I or X in place of C_2.I or C_2.X. 



--next define multiplication on the group
def mul : C_2 → C_2 → C_2 
| I   a := a
| a   I := a 
| _   _ := I


--we can now make this into a group by supplying proofs that the axioms are true.
--Since the group has only two elements, the proof of each axiom
--is simply to check each case.
instance group_C_2 : my_group C_2 :=
{
  one := I,
  mul := mul,
  inv := id,
  gp_assoc := λ a b c, by {cases a; cases b; cases c; refl},
  gp_mul_one := λ a, by {cases a; refl} ,
  gp_one_mul := λ a, by {cases a; refl} ,
  gp_mul_inv := λ a, by {cases a; refl} ,
  gp_inv_mul := λ a, by {cases a; refl} 
}


-- We can also make C_2 into a mathlib group.
-- These are defined in a slightly different way.
-- One can give lean a special algorithm to calculate powers of an element.
-- for example, we could define the n-th power (for n∈ ℕ ) using this function:

def npow : ℕ → C_2 → C_2 
| 0      a := I 
| (n+1)  a := mul a ( npow n a ) 



instance gpC2 : group C_2 :=
{
  mul := mul,
  mul_assoc := begin
    intros a b c,
    cases a; cases b; cases c;
    refl,
  end,
  one := I,
  one_mul := λ a, by {cases a;refl} ,
  mul_one := λ a, by {cases a;refl},
  npow := npow,
  npow_zero' := begin
    intro a,
    refl,
  end,
  npow_succ' := begin
    intros n x, refl,
  end,
  inv := id,
  --div := _,
  --div_eq_mul_inv := _,
  --zpow := _,
  --zpow_zero' := _,
  --zpow_succ' := _,
  --zpow_neg' := _,
  mul_left_inv := begin
    intro a,
    cases a;
    refl,
  end
}





instance ℤ_group : my_group ℤ := { one := 0,
  mul := λ x y, x+y,
  inv := λ x, -x,
  gp_assoc := add_assoc,
  gp_mul_one := add_zero,
  gp_one_mul := zero_add,
  gp_mul_inv := sub_self,
  gp_inv_mul := neg_add_self}