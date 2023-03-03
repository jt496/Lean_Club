import combinatorics.simple_graph.metric
import combinatorics.simple_graph.coloring
import data.nat.parity 

/-
Main theorem: `parity_adj_imp_odd_cycle`
If a connected graph G has an edge xy joining vertices that are both an even (or both odd) distance 
from a vertex z then G contains an odd cycle.

Corollary : If G is connected and does not contain an odd cycle then G is two-colourable (by parity from an arbitray vertex)



-/
namespace simple_graph
variables {V : Type*} {G : simple_graph V}
variables {x y z  u v w: V}
variable [decidable_eq V]

open list walk nat

/-- Disjoint paths can be appended to give a new path -/
lemma append_disj_paths  {p : G.walk u v} {q : G.walk v w} (hp :p.is_path) (hq: q.is_path) (hnd: p.support.disjoint q.support.tail)
: (p.append q).is_path:=
begin
  rw is_path_def, rw support_append, have :=((support_eq_cons q)),
  apply nodup_append.2 ,  refine ⟨hp.2,_,hnd⟩, 
  refine  (nodup_cons.1 _).2, exact v,exact (this ▸ hq.2),
end

/-- if z is in p then it is cons h p -/
lemma mem_cons_of_mem (h: G.adj v x) (p : G.walk x y) : z ∈ p.support → z ∈ (cons h p).support:=
begin
  intro h, rw [support_cons, mem_cons_iff], exact or.inr h,
end

/-- z ∈ (cons h p).support iff z is the newly adjoined vertex or z ∈ p.support -/
lemma mem_support_cons  (h : G.adj u x)  (p: G.walk x y): z ∈ (cons h p).support ↔   z = u ∨ z ∈ p.support:=
begin
  simp only [support_cons, mem_cons_iff],
end

/-- nil.take_until is nil -/
@[simp]
lemma take_until_nil : (nil : G.walk x x).take_until x (start_mem_support _)= nil' x:=rfl

/-- (cons h p).take_until u = nil' u if u is the new vertex-/
@[simp]
lemma take_until_cons_self   (h : G.adj u x) (p: G.walk x y) : (cons h p).take_until u (start_mem_support _) = nil' u:=
begin
  rw [take_until,dif_pos],refl,
end

/-- (cons h p).take_until z = (cons h (p.take_until z)) if z is not the new vertex the new vertex-/
@[simp]
lemma take_until_cons_ne_self (h : G.adj u x) (p: G.walk x y)  (hz : z ∈ p.support) (hz2: z ≠ u): 
(cons h p: G.walk u y).take_until z ((mem_support_cons  h p).2 (or.inr hz) ) = (cons h (p.take_until z hz)):=
begin
  rw [take_until],
  split_ifs, exfalso, exact hz2 h_1.symm,
  exact ⟨rfl,by refl⟩,
end

/-- If p is a u v walk then  p.support = p.reverse.support.tail.reverse ++ [v] -/
lemma support_eq_concat {u v : V} (p : G.walk u v) : p.support = (p.reverse.support.tail).reverse ++ [v] :=
begin
  have :=support_eq_cons p.reverse,
  rw support_reverse at *,
  apply_fun list.reverse at this,
  rw reverse_cons' at this,
  rw concat_eq_append at this,
  convert this,rw list.reverse_reverse,
end


/-- p.take_until z only contains z at the end -/
lemma take_until_rev_tail {u v z : V} (p : G.walk u v) (hz : z ∈ p.support ):  z ∉ (p.take_until z hz).reverse.support.tail:=
begin
  intro h,
  have :=support_eq_concat (p.take_until z hz) ,
  apply_fun count z at this,
  rw count_append at this,
  simp only [count_support_take_until_eq_one, support_reverse, count_eq_one_of_mem, nodup_cons, not_mem_nil, not_false_iff,
  nodup_nil, and_self, mem_singleton, self_eq_add_left, count_eq_zero, mem_reverse] at this,
  rw support_reverse at h, contradiction,
end


/-- Two walks to the same vertex z meet at `meet p q` -/
def meet : ∀ {x y z : V} (p : G.walk x z) (q: G.walk y z) , V
| x y z nil q := x
| x y z (cons r p) q  :=
    if hx : x ∈ q.support then x
    else meet p q


/-- If we add a new vertex u to p that is in q then `meet (cons h p) q = u` -/
@[simp]
lemma meet_cons_mem (p : G.walk x z) (q: G.walk y z) (h: G.adj u x) (hu :u ∈ q.support) : meet (cons h p) q = u:=
begin
  unfold meet,split_ifs,refl,
end

/-- If we add a new vertex u to p that is not in q then `meet (cons h p) q = meet p q` -/
@[simp]
lemma meet_cons_not_mem (p : G.walk x z) (q: G.walk y z) (h: G.adj u x) (hu :u ∉ q.support) : meet (cons h p) q = meet p q:=
begin
  unfold meet, split_ifs,refl,
end

/-- ite for meet (cons h p) q -/
lemma meet_cons_eq (p : G.walk x z) (q: G.walk y z) (h: G.adj u x) : meet (cons h p) q = ite (u ∈ q.support) u (meet p q):=
begin
  split_ifs, exact meet_cons_mem p q h h_1,exact meet_cons_not_mem p q h h_1,
end

/-- nil z and q meet at z -/
@[simp]
lemma meet_nil (q: G.walk y z) : meet (nil: G.walk z z) q = z:=rfl


/-- p and nil z meet at z -/
@[simp]
lemma meet_nil' (p: G.walk x z) : meet p (nil: G.walk z z) = z:=
begin
  induction p, refl, rw meet_cons_eq, split_ifs, rwa mem_support_nil_iff at h,
  exact p_ih,
end

/-- meet p q belongs to p -/
lemma meet_mem (p : G.walk x z) (q : G.walk y z) : meet p q ∈  p.support:=
begin
  induction p, unfold meet, rw support_nil, exact mem_singleton_self _,
  unfold meet,split_ifs,rw support_cons,  exact mem_cons_self _ _,
  apply mem_cons_of_mem, apply p_ih,
end

/-- meet p q belongs to q -/
lemma meet_mem' (p : G.walk x z) (q : G.walk y z) : meet p q ∈  q.support:=
begin
  induction p, unfold meet, exact end_mem_support q,
  unfold meet,
  split_ifs, exact h,
  apply p_ih,
end

/-- The shortcut from Pxz and Qyz to Wxy : follow P from x to meet p q and then from there to the start of Q in reverse. -/
def shortcut  {x y z : V} (p : G.walk x z) (q: G.walk y z) : G.walk x y
:=(p.take_until (meet p q) (meet_mem p q)).append (q.take_until (meet p q) (meet_mem' p q)).reverse

/-- edges of shortcut p q are edges of p or q -/
lemma shortcut_edges_subset  {x y z : V} (p : G.walk x z) (q: G.walk y z) {e : sym2 V}
  (he : e ∈ (shortcut p q).edges): e ∈ p.edges ∨ e ∈ q.edges:=
begin
  unfold shortcut at he, rw edges_append at he,
  cases mem_append.1 he,
  left, exact edges_take_until_subset p _ h,
  right, rw edges_reverse at h, rw mem_reverse at h,
  exact edges_take_until_subset q _ h,
end


/-- Useful for some rewriting when the name of the vertex we are walking to changes from u to v
p.take_until v is the same as p.take_until u if u = v -/
lemma take_until_eq_eq (p : G.walk x y) (hu : u ∈ p.support) (hv : u = v) :
p.take_until v (hv ▸ hu) = (p.take_until u hu).copy rfl hv :=
begin
  subst v, refl,
end


/-- If you add a vertex u ∈ q  to p then `meet (cons h p) q = u` 
so the path along this until we meet q is just the vertex u -/
lemma cons_take_meet_of_mem (p : G.walk x z) (q : G.walk y z) (hadj : G.adj u x) (hu : u ∈ q.support)
: ((cons hadj p).take_until (meet (cons hadj p ) q) (meet_mem _ q)).support = [u] :=
begin
  have h1:= meet_cons_mem p q hadj hu, 
  have h2:= take_until_cons_self hadj p,
  rw  take_until_eq_eq (cons hadj p) (meet_mem (cons hadj p) q) h1 at h2,
  apply_fun walk.support at h2,
  rwa [support_copy, support_nil] at h2,  
end

/-- If you add a vertex u ∉ q to p the (cons h p).take_until meet.. is just u :: (p.take_until...)-/
lemma cons_take_meet_of_not_mem (p : G.walk x z) (q : G.walk y z) (hadj : G.adj u x) (hu : u ∉ q.support)
: ((cons hadj p).take_until (meet (cons hadj p ) q) (meet_mem _ q)).support = u::(p.take_until (meet p q)(meet_mem p q)).support :=
begin
  have h1:= meet_cons_not_mem p q hadj hu,
  have h3: meet p q ≠ u,{
    intro hf, apply hu (hf ▸ meet_mem' p q),},
  have h2:= take_until_cons_ne_self hadj p (meet_mem p q) h3,
  rw  take_until_eq_eq (cons hadj p) (meet_mem (cons hadj p) q) h1 at h2,
  apply_fun walk.support at h2,rwa [support_copy,support_cons] at h2,
end

/-- If v belongs to p.take_until meet p q and also belongs to q then v = meet p q -/
lemma meet_take_mem_imp (p : G.walk x z) (q : G.walk y z) : 
v ∈ (p.take_until (meet p q) (meet_mem p q)).support → v ∈ q.support → v = meet p q :=
begin
  intros hp hq,
  induction p,
  have : v ∈(nil' p).support:=support_take_until_subset (nil' p) _ hp,
  rw support_nil at this,
  rw meet_nil, exact mem_singleton.1 this,
  by_cases h1: p_u ∈ q.support,
  rw meet_cons_mem p_p q p_h h1 at *,
  rw cons_take_meet_of_mem p_p q p_h h1 at hp, exact mem_singleton.1 hp,
  by_cases v = p_u, subst v,
  exact (meet_cons_mem p_p q p_h hq).symm,
  rw cons_take_meet_of_not_mem p_p q p_h h1 at hp, 
  cases hp, contradiction,
  rw meet_cons_not_mem p_p q p_h h1,
  exact p_ih q hp hq,
end

/-- `shortcut p q` is a path if p and q are paths -/
lemma shortcut_is_path {x y z : V} {p : G.walk x z} {q: G.walk y z} (hp : p.is_path) (hq : q.is_path): 
(shortcut p q).is_path:=
begin
  apply append_disj_paths (hp.take_until (meet_mem p q))  (hq.take_until (meet_mem' p q)).reverse,
  intros v hvp hvq,
  apply take_until_rev_tail q (meet_mem' p q),
  rwa meet_take_mem_imp p q hvp _ at hvq,
  rw support_reverse at hvq,
  apply support_take_until_subset q _ (mem_reverse.1 (tail_subset _ hvq)),
end

/-- If p.bypass = p then p is a path -/
lemma bypass_eq_self_imp_path {p: G.walk x y } (h: p.bypass = p ) : p.is_path:= (h ▸ bypass_is_path p)

/-- If p is a walk and p.bypass ≠ p then p.bypass is strictly shorter than p -/
lemma bypass_ne_self_imp_lt {p: G.walk x y} (h: p.bypass ≠ p) : p.bypass.length < p.length:=
begin
  induction p with _ u v z hadj hw ih, contradiction,
  simp only [bypass, walk.length_cons],
  split_ifs with h1, 
  apply lt_succ_of_le ((length_drop_until_le _ h1).trans (length_bypass_le hw)),
  simp only [walk.length_cons, add_lt_add_iff_right],
  apply ih, 
  intro hf,
  simp only [*, bypass, not_false_iff, dif_neg, ne.def, eq_self_iff_true, heq_iff_eq, and_self, not_true] at h, 
  exact h, 
end

/-- any shortest walk is a path-/
lemma shortest_is_path {p : G.walk x y} (hp : p.length = G.dist x y) : p.is_path:=
begin
  apply bypass_eq_self_imp_path , by_contra, 
  apply not_lt_of_ge (dist_le p.bypass),
  apply lt_of_lt_of_le ((bypass_ne_self_imp_lt h)) hp.le, 
end

/-- length of a path is length upto z + length from z -/
lemma take_until_drop_length (p : G.walk x y) (hz : z ∈ p.support) : 
p.length = (p.take_until z hz).length + (p.drop_until z hz).length   :=
begin
  rw ← walk.length_append, congr, rwa take_spec p hz, 
end


/-- If p is a shortest x y walk and z ∈ p then p.take_until z is a shortest x z walk  -/
lemma shortest_to (hconn : G.connected) (p: G.walk x y) (hp: p.length = G.dist x y) (hz : z ∈ p.support) :
G.dist x z = (p.take_until z hz).length:=
begin
  apply le_antisymm ,
  apply dist_le,
  by_contra,
  apply lt_irrefl (G.dist x y), 
  calc 
    G.dist x y ≤ G.dist x z + G.dist z y : hconn.dist_triangle
    ...        < (p.take_until z hz).length + G.dist z y : add_lt_add_right (lt_of_not_ge h) _
    ...        ≤ (p.take_until z hz).length + (p.drop_until z hz).length :  add_le_add_left (dist_le (p.drop_until z hz)) _
    ...        = G.dist x y : (take_until_drop_length p hz) ▸ hp,
end


/-- If p is a shortest x y walk and z ∈ p then p.drop_until z is a shortest z y walk  -/
lemma shortest_from (hconn : G.connected) (p: G.walk x y) (hp: p.length = G.dist x y) (hz : z ∈ p.support) :
G.dist z y = (p.drop_until z hz).length :=
begin
  apply  le_antisymm ,
  apply dist_le,
  by_contra,
  apply lt_irrefl (G.dist x y), 
  calc G.dist x y ≤ G.dist x z + G.dist z y : hconn.dist_triangle
        ...       < G.dist x z + (p.drop_until z hz).length : add_lt_add_left (lt_of_not_ge h) _
        ...       ≤ (p.take_until z hz).length + (p.drop_until z hz).length : add_le_add_right (dist_le _ ) _
        ...       = G.dist x y : (take_until_drop_length p hz) ▸ hp,
end


/-- Given any shortest x y walk p and a vertex lying z ∈ p, the distance triangle inequality is equality for x z y.-/
lemma triangle_eq (hconn : G.connected) (p: G.walk x y) (hp: p.length = G.dist x y) (hz : z ∈ p.support) :
 G.dist x y = G.dist x z + G.dist z y :=
begin
  rw [shortest_to hconn p hp hz, shortest_from hconn p hp hz,← hp], 
  exact take_until_drop_length p hz,
end



/-- If xy is an edge in a shortest x-z walk then distance from x to z is distance from y to z + 1 -/
lemma shortest_path_edge_odd {p : G.walk x z} (hconn : G.connected) (hp : p.length = G.dist x z) (he : ⟦(x,y)⟧∈ p.edges): 
G.dist x z = G.dist y z + 1:=
begin
  rw [triangle_eq hconn p hp (snd_mem_support_of_mem_edges  p he),add_comm, add_right_inj], 
  apply le_antisymm,
  exact dist_le (walk.cons (edges_subset_edge_set p he) walk.nil),
  apply connected.pos_dist_of_ne hconn (edges_subset_edge_set p he).ne, 
end


/-- If the shortcut from Pyx and Qzx from y to z contains the edge zy then the distances x-z and y-z have different parities -/
lemma shortcut_edge_imp  {p1: G.walk x z} {p2: G.walk y z} (hconn : G.connected)(hp1: p1.length= G.dist x z) (hp2: p2.length= G.dist y z)
 (he: ⟦(y,x)⟧ ∈ (shortcut p1 p2).edges) : ¬2 ∣ G.dist x z+ G.dist y z :=
begin
  cases shortcut_edges_subset p1 p2 he, 
  rw sym2.eq_swap at h, rw add_comm,
  have:= shortest_path_edge_odd hconn hp1  h, rw [this,← add_assoc,← two_mul],
  exact two_not_dvd_two_mul_add_one _,    
  have:= shortest_path_edge_odd hconn hp2  h, rw [this,← add_assoc,← two_mul],
  exact two_not_dvd_two_mul_add_one _,
end

/-- If y is on a shortest x-z walk then y is no further from z than x -/
lemma mem_shortest_path_closer {p: G.walk x z} (hconn: G.connected) (hp: p.length = G.dist x z) (hy : y ∈ p.support ): 
G.dist y z ≤ G.dist x z:=
begin
  rw shortest_from hconn p hp hy, rw ← hp,
  exact walk.length_drop_until_le _ _,
end

/-- If y is on a shortest x-z walk then x is no further from y than z -/
lemma mem_shortest_path_closer' {p: G.walk x z} (hconn: G.connected) (hp: p.length = G.dist x z) (hy : y ∈ p.support ): 
G.dist x y ≤ G.dist x z:=
begin
  rw shortest_to hconn p hp hy, rw ← hp,
  exact walk.length_take_until_le _ _,
end

/-- If dist x z ≤ dist y z and x ≠ y then y cannot lie on any shortest x z walk -/
lemma not_mem_shortest_of_le {p: G.walk x z} (hconn: G.connected) (hxz: G.dist x z ≤ G.dist y z) 
(hp: p.length = G.dist x z) (hne: x ≠ y): y ∉ p.support:=
begin
  by_contra, 
  have :=le_antisymm hxz (mem_shortest_path_closer hconn hp h),
  apply hne, apply hconn.dist_eq_zero_iff.1,
  rw triangle_eq hconn p hp h at this,
  exact add_left_eq_self.1 this,
end

/-- If G is connected and there is an edge joining two vertices x and y whose distances 
from a vertex z have the same parity then G contains an odd-length cycle -/
lemma parity_adj_imp_odd_cycle (hconn: G.connected)(hadj: G.adj y x) (he: 2 ∣ G.dist x z + G.dist y z) :
∃ c : G.walk y y, c.is_cycle ∧ odd c.length :=
begin
-- get a shortest walk from x to z
  obtain ⟨p1,hp1⟩:=hconn.exists_walk_of_dist x z,
-- get a shortest walk from y to z
  obtain ⟨p2,hp2⟩:=hconn.exists_walk_of_dist y z,
-- these walks are both paths (because they are shortest walks)
-- these paths meet  at some vertex v (since they both end at z) so we can append them by
-- following p1 from x to v and then follow p2 in reverse from v to y.
-- this "shortcut" is still a path, but now from x to y
  have sp:=shortcut_is_path (shortest_is_path hp1) (shortest_is_path hp2),
-- we can now close this path into a cycle using the fact that xy is an edge
  refine ⟨walk.cons hadj (shortcut p1 p2),_,_⟩,
-- to prove this is in fact a cycle we need to check that the edge xy was not already used in the path
  apply path.cons_is_cycle ⟨shortcut p1 p2,sp⟩,
-- but if it were then the shortest paths from x to z and y to z would differ in length by exactly 1 and hence 
-- 2 could not divide the sum of their lengths
  intro hf, apply shortcut_edge_imp hconn hp1 hp2 hf he,
-- now just need to check that the length of the cycle is infact odd 
  rw [shortcut,walk.length_cons, walk.length_append], 
  rw [triangle_eq hconn p1 hp1 (meet_mem p1 p2),triangle_eq hconn p2 hp2 ((meet_mem' p1 p2))] at he,
  rw [add_comm (G.dist y (meet p1 p2)),←add_assoc,add_comm _ (G.dist (meet p1 p2) z),add_comm (G.dist x (meet p1 p2)),←add_assoc,←two_mul] at he,
  rw [← shortest_to hconn p1 hp1 _, walk.length_reverse, ← shortest_to hconn p2 hp2], 
  rw [add_assoc,add_comm, @dist_comm _ _ y _, nat.dvd_add_left (dvd_mul_right 2 _)] at he,  
  obtain ⟨k,hk⟩:=he,
  use k, nth_rewrite 1 dist_comm, rw hk,
end

/-- If G is connected and z ∈ V then we can try to define a 2-colouring by distance from z using "bool = {tt, ff}"-/
noncomputable 
def colour_bool (hconn : G.connected) (z : V): V → bool :=λ x, ite (even (G.dist x z)) tt ff  

/-- G has no_odd_cycle iff -/
def no_odd_cycle (G: simple_graph V): Prop := ¬ ∃ (v:V), ∃ (c: G.walk v v), c.is_cycle ∧ odd c.length

/-- If G is connected and has no odd cycle then the colouring by distance from an arbitrary z ∈ V is valid-/
theorem no_odd_cycle_imp_two_col (hconn : G.connected) (z : V) (nodd: G.no_odd_cycle): 
 ∀ (x y :V), G.adj x y → colour_bool hconn z x ≠ colour_bool hconn z y:=
begin
  intros x y hadj hf,
  unfold colour_bool at hf, split_ifs at hf,
  apply nodd, use x, apply parity_adj_imp_odd_cycle hconn hadj _,
  exact z,
  obtain ⟨a,ha⟩:=h,obtain ⟨b,hb⟩:=h_1, use (b+a),
  rwa [ha, hb,two_mul, ← add_assoc , ← add_assoc , add_comm (b+a), ← add_assoc],
  exact hf,
  rw ← odd_iff_not_even at *,
  apply nodd, use x, apply parity_adj_imp_odd_cycle hconn hadj _,
  exact z,
  obtain ⟨a,ha⟩:=h,obtain ⟨b,hb⟩:=h_1,  use (a+b+1),
  rw [hb,ha, add_comm (2*b +1), add_assoc, add_comm 1, add_assoc, ← two_mul 1, ← add_assoc, ← mul_add, ← mul_add],
end


/-- If G has no odd cycle then it can be two-coloured (by bool tt/ff)-/
noncomputable
def two_colouring (hconn : G.connected) (z : V) (nodd: G.no_odd_cycle) :
 G.coloring bool:=⟨colour_bool hconn z, λ a b h, no_odd_cycle_imp_two_col hconn z nodd a b h⟩

/-- Any connected nonempty graph with no odd cycle has χ(G) ≤ 2 -/
lemma chromatic_number_le_two_of_no_odd_cycle (hconn : G.connected) (z : V) (nodd: G.no_odd_cycle) : 
G.chromatic_number ≤ 2:=
begin
  have :=coloring.to_colorable (two_colouring hconn z nodd),
  rw fintype.card_bool at this, 
  exact  chromatic_number_le_of_colorable this,
end

end simple_graph