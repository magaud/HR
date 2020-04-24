Require Export ZArith.

Module Type Num.

Parameter A:Set.

Parameter a0:A.
Parameter a1:A.
Parameter plusA : A -> A -> A.
Parameter multA : A -> A -> A.
Parameter oppA : A -> A.
Parameter divA : A -> A -> A.
Parameter modA : A -> A -> A.
Parameter absA : A-> A.

Parameter equalA : A -> A -> Prop.

Parameter leA : A -> A -> Prop.
Parameter ltA : A -> A -> Prop.

Notation " x == y" := (equalA x y) (at level 80).
Notation "x + y " := (plusA  x y).
Notation "x * y " := (multA  x y). 
Notation "x / y " := (divA  x y).
Notation "x %% y" := (modA  x y) (at level 100).

Notation "0" := (a0).
Notation "1" := (a1).
Notation "- x" := (oppA x).
Notation "| x |" := (absA x) (at level 60).
Notation "x <= y" := (leA x y).
Notation "x < y" := (ltA x y).

Parameter equalA_refl : forall x, x == x.
Parameter equalA_sym : forall x y, x == y -> y ==x.
Parameter equalA_trans : forall x y z, x == y -> y ==z -> x==z.

Parameter plus_neutral : forall x,0 + x == x.
Parameter plus_comm : forall x y,  x + y ==  y + x.
Parameter plus_assoc : forall x y z,  x + (y + z) == (x + y) + z.
Parameter plus_opp : forall x, x + (- x) == 0.

Parameter abs_pos : forall x, 0 <=|x|.
Parameter abs_pos_val : forall x, 0 <=x -> |x|==x. 
Parameter abs_neg_val : forall x, x <=0 -> |x|==-x. 
Parameter abs_minus : forall x, | - x| == |x|.
Parameter abs_max : forall x, x <= |x|.
Parameter abs_new : forall x a, x<= a -> -x <=a -> |x|<=a.
Parameter abs_new2 : forall x a, |x|<= a -> -a <= x .

Parameter abs_triang : forall x y, |x+y| <= |x| + | y |. 
Parameter abs_prod : forall x y, |x * y| == |x| * |y|.

(* specification of division *)

Parameter div_mod : forall a b, 0< a\/a< 0 -> b == a*(b / a) + (b %% a). 
Parameter div_mod2 : forall a b, 0< a\/a< 0 -> a*(b/a) == b + - (b %% a).

Parameter div_mod3 : forall a b, 0 < a -> |(b %% a)| < a. 
Parameter div_mod3a : forall a b, 0 < a -> (b %% a) < a. 
Parameter div_mod3b : forall a b, 0 < a -> 0<=(b %% a). 
Parameter div_mod3_abs: forall a b:A, 0< b \/ b< 0 -> | a %% b | <= |b|.

Parameter div_le : forall a b c, 0 < c -> a <= b -> a / c <= b / c. 
Parameter div_le2 : forall a b, 0 < a -> 0<= b -> a*(b/a) <= b. 

Parameter div_pos : forall a b, 0<=a -> 0<b -> 0<=a/b. 
Parameter div_idg : forall x y, 0 < y -> (x * y) / y == x. 

Parameter mult_le : forall a b c d,
   0 <= a -> a <= b -> 0 <= c -> c <= d -> a*c <= b * d.

Parameter mult_neutral : forall x, 1 * x == x.
Parameter mult_distr_l : forall x y z, (x+y)*z == x*z + y*z.


Parameter mult_comm : forall x y, x * y == y * x.
Parameter mult_assoc : forall x y z, x * (y * z) ==(x * y) * z.
 
Parameter mult_absorb : forall x, x * 0 == 0.

Parameter le_refl : forall x, x <= x.
Parameter le_trans : forall x y z, x <= y -> y <= z -> x <= z .
Parameter lt_plus : forall x y z t, x < y -> z < t -> (x + z) < (y + t).
Parameter le_plus : forall x y z t, x <= y -> z <= t -> (x + z) <= (y + t).
Parameter le_lt_plus : forall x y z t, x <= y -> z < t -> (x + z) < (y + t).

Parameter le_plus_inv : forall x y z, (x + z) <= (y + z) -> x <= y .
Parameter lt_plus_inv : forall x y z, (x + z) < (y + z) -> x < y .
Parameter le_mult_simpl : forall x y z , (0 <= z) -> (x <=y)-> (x * z) <= (y *z).
Parameter le_mult : forall x y z, 0 <= x -> y <=z -> x*y <= x*z.
Parameter le_mult_general : 
  forall x y z t, 0 <= x -> x <= y -> 0 <= z -> z  <= t -> x*z <= y*t.
Parameter le_mult_neg : forall x y z, x < 0 -> y <=z -> x*z <= x*y.


Parameter le_mult_inv : forall x y z, 0 < x -> (x * y) <= (x * z) -> y <= z .
Parameter lt_mult_inv : forall x y z, 0 < x -> (x * y) < (x * z) -> y < z .
Parameter le_mult_inv2 : forall x y z, x < 0 -> (x * y) <= (x * z) -> z <= y .
Parameter lt_mult_inv2 : forall x y z, x < 0 -> (x * y) < (x * z) -> z < y .

Parameter lt_mult : forall x y z, 0 < x -> y <z -> x*y < x*z.
Parameter mult_pos : forall x y : A, 0<x -> 0<y -> 0<x*y.

Parameter lt_0_1 : (0 < 1).
Parameter lt_m1_0 : (-a1 < 0).

Parameter lt_trans : forall x y z, x < y -> y < z -> x < z .
Parameter le_lt_trans : forall x y z, x <= y -> y < z -> x < z .
Parameter lt_le_trans : forall x y z, x < y -> y <= z -> x < z .

Parameter lt_le : forall x y, (x < y) -> (x <= y).
Parameter lt_le_2 : forall x y, (x < y) -> (x+1 <= y). (* connecting lt and le *)
Parameter le_lt_False : forall x y, x <= y -> y < x -> False.

Parameter le_id : forall x y, x <= y -> y <= x -> x == y.
Parameter contradict_lt_le : forall s x, s < x -> x <= s -> False.
Parameter not_lt_0_0 : ~0 < 0.

(** non-standard and lim *)

Parameter lim:A->Prop.

Parameter  ANS1 : lim 1.
Parameter  ANS2a : forall x y, lim x -> lim y -> lim (x + y).
Parameter  ANS2b : forall x y, lim x -> lim y -> lim (x * y).
Parameter  ANS4 :  forall x, (exists y, lim y/\ | x | <= | y |)-> lim x.

Parameter std:A->Prop.

Parameter std_A0_dec : forall x, std x -> {x < 0}+{x == 0}+{0 < x}.

Parameter std_lim : forall x, std x -> lim x.

Parameter ANS1' : std 1. 
Parameter ANS2a' : forall x y : A, std x -> std y -> std (x + y). 
Parameter ANS2a_minus : forall x, std x -> std (-x ).

Parameter std0 : std 0. 

(** induction principle *)

Parameter nat_like_induction : 
  forall P : A -> Type, 
    P a0 ->
    (forall n:A, (std n /\ 0 <= n) -> P n -> P (plusA n a1)) ->
    forall n:A, (std n /\ 0<= n) -> P n.

Parameter nat_like_induction_r1 :
forall H:std 0 /\ 0<=0, forall P : A -> Type, 
    forall (h0: P a0), 
    forall hr : (forall n:A, (std n /\ 0 <= n) -> P n -> P (plusA n a1)),
    nat_like_induction P h0 hr a0 H = h0.

Parameter nat_like_induction_r2 :
forall P : A -> Type, 
    forall n:A, forall H:std n/\0<=n,
    forall Hn':std (n+1)/\0<=(n+1),
forall (h0: P a0), 
    forall hr : (forall n:A, (std n /\ 0 <= n) -> P n -> P (plusA n a1)),
    nat_like_induction P h0 hr (n + 1) Hn' = 
    hr n H (nat_like_induction P h0 hr n H).

End Num.
