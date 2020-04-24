Require Export Arith. (* to use ring for natural numbers *)
Require Export Ltac. 
Require Export Numbers_facts.

Lemma Zmult_lt_reg_l: forall n m p : Z, (0 < p)%Z -> (p * n  < p * m)%Z -> (n < m)%Z.
Proof.
intros.
rewrite (Zmult_comm p n) in *.
rewrite (Zmult_comm p m) in *.
eapply Zmult_lt_reg_r; eassumption.
Qed.

(** *************************************************************************************************************)
(**                      Laugwitz-Schmieden                                                                     *)
(** *************************************************************************************************************)

Module LS <: Num_facts.

Definition A :=nat->Z.

(** Operations **)

Definition a0 : A := fun (n:nat) => 0%Z.
Definition a1: A := fun (n:nat) => 1%Z.

Definition plusA (u v:A) : A := fun (n:nat) => Zplus (u n) (v n).
Definition oppA (u:A) : A := fun (n:nat) => Z.opp (u n).

Definition minusA x y := plusA x (oppA y).

Definition multA (u v:A) : A := fun (n:nat) => Zmult (u n) (v n).

Definition divA (u v:A) : A := fun (n:nat) => Z.div (u n) (v n).
Definition modA (u v:A) : A := fun (n:nat) => Z.modulo (u n) (v n).

Definition absA (u:A) : A := fun (n:nat) => Z.abs (u n).

Notation "x + y " := (plusA  x y).
Notation "x * y " := (multA  x y).
Notation "x / y " := (divA  x y).
Notation "x mod% y" := (modA  x y) (at level 60).
Notation "0" := (a0). 
Notation "1" := (a1). 
Notation "- x" := (oppA x).
Notation "| x |" := (absA x) (at level 60).

(** Relations **)
Definition equalA (u v:A) := 
   exists N:nat, forall n:nat, n>N -> (u n)=(v n).

Notation "x =A y" := (equalA x y) (at level 80).

Definition leA (u v:A) := 
   exists N:nat, forall n:nat, n>N -> Z.le (u n) (v n).

Definition ltA (u v:A) := 
   exists N:nat, forall n:nat, n>N -> Z.lt (u n) (v n).

Notation "x <=A y" := (leA x y) (at level 50).
Notation "x <A y" := (ltA x y) (at level 50).

Definition std (u:A) := exists N:nat, forall n m, n>N -> m>N -> (u n)=(u m).

Definition non_std (u:A) := ~std u.

Definition lim (a:A) := exists p, std p /\ leA a0 p /\ ltA (absA a) p.

(** Tactics **)

Ltac gen_eq n0 :=  (match goal with |[ H : forall n:nat, n > ?X -> _ |- _ ] => 
   let myH:=fresh "Hyp" in assert (myH:(n0 > X)) by (unfold sum_plus1 in *;omega); generalize (H n0 myH); clear H; intro end).

Ltac gen_props := 
match goal with 
  [|- forall n:nat, _ ] => let id:= fresh "p" in let Hid := fresh "Hp" in (intros id Hid; repeat (gen_eq id)) 
| [|- False] => let l:= collect_nats in repeat (gen_eq (sum_plus1 l)) 
end .

Ltac unfold_intros := unfold lim, std, leA, ltA, equalA, absA, minusA, multA, plusA, divA, modA, oppA, A, a0, a1; intros.

Ltac solve_ls_w_l x :=
unfold_intros;
destruct_exists;
let l:= collect_nats in exists (sum_plus1 l); simpl;
gen_props;
(apply x|| eapply x); solve [eassumption | omega].

Ltac autorew_aux := 
match goal with [H:(_=_)%Z |- _ ] => rewrite <- H end.

Ltac autorew := repeat autorew_aux.

Ltac solve_ls :=
(unfold_intros;
solve [ intros; solve [omega | ring] |
destruct_exists; try gen_props; intros; omega | 
destruct_exists; let l:= collect_nats in exists (sum_plus1 l); intros; ring | 
destruct_exists; let l:= collect_nats in exists (sum_plus1 l); simpl; gen_props; autorew; solve [assumption | omega | ring]]). 

(*** Equality **)

Lemma equalA_refl : forall x, x =A x.
Proof.
solve_ls.
Qed.

Lemma equalA_sym : forall x y, x =A y -> y =A x.
Proof.
solve_ls.
Qed.

Lemma equalA_trans : forall x y z, x =A y -> y =A z -> x=A z.
Proof.
solve_ls.
Qed.

Instance equalA_equiv : Equivalence equalA.
Proof.
split; red; [apply equalA_refl | apply equalA_sym | apply equalA_trans ].
Qed.

(** Morphisms **)

Instance plusA_morphism : Proper (equalA ==> equalA ==> equalA) plusA.
Proof.
repeat red; solve_ls. 
Qed.

Instance oppA_morphism : Proper (equalA ==> equalA) oppA.
Proof.
repeat red; solve_ls. 
Qed.

Instance multA_morphism : Proper (equalA ==> equalA ==> equalA) multA.
Proof.
repeat red; solve_ls.
Qed.

Instance absA_morphism : Proper (equalA ==> equalA) absA.
Proof.
repeat red; solve_ls. 
Qed.

Instance leA_morphism : Proper (equalA ==> equalA ==> Logic.iff)  leA.
Proof.
repeat red; unfold_intros; split; solve_ls.
Qed.

Instance ltA_morphism : Proper (equalA ==> equalA ==> Logic.iff) ltA.
Proof.
repeat red; unfold_intros; split; solve_ls.
Qed.

Instance divA_morphism : Proper (equalA ==> equalA ==> equalA) divA.
Proof.
repeat red; solve_ls.
Qed.

Instance modA_morphism : Proper (equalA ==> equalA ==> equalA) modA.
Proof.
repeat red; unfold_intros; solve_ls.
Qed.

(** Implementation of axioms of Numbers.v and Numbers_facts.v **)

(** Ring properties **)

Lemma plus_neutral : forall x:A,0 + x =A x.
Proof.
solve_ls.
Qed.

Lemma plus_comm : forall x y,  x + y =A  y + x.
Proof.
solve_ls.
Qed.

Lemma plus_assoc : forall x y z,  x + (y + z) =A (x + y) + z.
Proof.
solve_ls.
Qed.

Lemma plus_opp : forall x:A, x + (- x) =A a0.
Proof.
solve_ls.
Qed.

Lemma mult_neutral : forall x, a1 * x =A x.
Proof.
solve_ls.
Qed.

Lemma mult_comm : forall x y, x * y =A y * x.
Proof.
solve_ls.
Qed.

Lemma mult_assoc : forall x y z, x * (y * z) =A (x * y) * z.
Proof.
solve_ls.
Qed.

Lemma mult_absorb : forall x, x * a0 =A a0.
Proof.
solve_ls.
Qed.

Lemma mult_distr_l : forall x y z, (x+y)*z =A x*z + y*z.
Proof.
solve_ls.
Qed.

Definition Radd_0_l := plus_neutral.
Definition Radd_comm := plus_comm.
Definition Radd_assoc :=plus_assoc.
Definition Rmul_1_l :=mult_neutral.
Definition Rmul_comm :=mult_comm.
Definition Rmul_assoc := mult_assoc.
Definition Rdistr_l := mult_distr_l.

Lemma Rsub_def : forall x y : A, (minusA x y) =A (plusA x (oppA y)).
Proof.
intros; unfold minusA; apply equalA_refl.
Qed.

Definition Ropp_def := plus_opp.

Lemma stdlib_ring_theory : ring_theory a0 a1 plusA multA minusA oppA equalA.
Proof.
constructor.
exact Radd_0_l. 
exact Radd_comm. 
exact Radd_assoc.
exact Rmul_1_l. 
exact Rmul_comm.
exact Rmul_assoc.
exact Rdistr_l.
exact Rsub_def.
exact Ropp_def.
Qed.

Add Ring A_ring : stdlib_ring_theory (abstract).

Lemma mult_distr_r : forall x y z, x*(y+z) =A x*y + x*z.
Proof.
intros; ring.
Qed.

(** absA **)

Lemma abs_pos : forall x, a0 <=A |x|.
Proof.
unfold_intros.
exists 0%nat.
intros; simpl.
assert ((x n)<>0\/x n=0)%Z by omega.
destruct H0.
assert (0 < Z.abs (x n))%Z by (apply Z.abs_pos; assumption).
omega.
rewrite H0; simpl; omega.
Qed.

Lemma abs_pos_val : forall x, a0<=A x -> |x|=A x.
Proof.
solve_ls_w_l Z.abs_eq.
Qed.

Lemma abs_neg_val : forall x, x<=A a0 -> |x|=A -x. 
Proof.
solve_ls_w_l Z.abs_neq.
Qed.

Lemma abs_new : forall x a, x<=A a -> -x <=A a -> |x|<=A a.
Proof.
unfold_intros; destruct_exists.
let l := collect_nats in exists (sum_plus1 l).
gen_props.
assert (Hom:(x p<0)%Z\/(x p>=0)%Z)by omega.
elim Hom; clear Hom; intros Hom'.
rewrite Z.abs_neq.
assumption.
omega.
rewrite Z.abs_eq.
assumption.
omega.
Qed.

Lemma abs_new2 : forall x a, |x|<=A a -> -a <=A x .
Proof.
unfold_intros; destruct_exists.
let l := collect_nats in exists (sum_plus1 l).
gen_props.
assert (Hom:(x p<0)%Z\/(x p>=0)%Z)by omega.
elim Hom; clear Hom; intros Hom'.
rewrite Z.abs_neq in *.
omega.
omega.
rewrite Z.abs_eq in *.
omega.
omega.
Qed.

Lemma abs_triang : forall x y, |x+y| <=A |x| + | y |.
Proof.
solve_ls_w_l Z.abs_triangle.
Qed.

Lemma abs_prod : forall x y, |x * y| =A |x| * |y|.
Proof.
solve_ls_w_l Z.abs_mul.
Qed.

Lemma div_mod : forall a b, 0<A a\/a<A 0 -> b =A a*(b / a) + (b mod% a). 
Proof.
intros; destruct H.
revert a b H.
solve_ls_w_l Z_div_mod_eq_full.
revert a b H.
solve_ls_w_l Z_div_mod_eq_full.
Qed.

Lemma div_mod2 : forall a b, 0<A a\/a<A 0 -> a*(b/a) =A b + - (b mod% a).
Proof.
intros a b H; generalize (div_mod a b H).
revert a b H.
solve_ls.
Qed.

Lemma div_mod3a : forall a b, 0 <A a -> (b mod% a) <A a.
Proof.
solve_ls_w_l Z_mod_lt.
Qed.

Lemma div_mod3b : forall a b, 0 <A a -> 0 <=A (b mod% a).
Proof.
solve_ls_w_l Z_mod_lt.
Qed.

Lemma div_mod3 : forall a b, 0<A a -> |(b mod% a)| <A a.
Proof.
intros.
rewrite abs_pos_val.
apply div_mod3a.
assumption.
apply div_mod3b.
assumption.
Qed.

Lemma lt_le : forall x y, (x <A y) -> (x <=A y).
Proof.
solve_ls.
Qed.

Lemma div_mod3_abs: forall a b:A, 0<A b \/ b<A 0 -> | a mod% b | <=A |b|.
Proof.
intros; destruct H.
rewrite (abs_pos_val b).
apply lt_le; apply div_mod3.
assumption.
apply lt_le; assumption.
revert a b H.
unfold_intros.
destruct H; destruct_exists.
exists (x+1)%nat.
gen_props.
rewrite (Z.abs_neq (b p)).
generalize (Z_mod_neg (a p) (b p) H); intros H'; destruct H'.
rewrite Z.abs_neq.
omega.
assumption.
omega.
Qed.

Lemma div_le : forall a b c, 0 <A c -> a <=A b -> a / c <=A b / c.
Proof.
solve_ls_w_l Z_div_le.
Qed.

Lemma div_pos : forall a b, 0 <=A a -> 0 <A b -> 0 <=A a/b.
Proof.
solve_ls_w_l Z_div_pos.
Qed.

Lemma bingo : forall x y:Z, (x<y -> x<>y)%Z.
Proof.
unfold_intros.
omega.
Qed.

Lemma bingo2 : forall x y:Z, (x>y -> x<>y)%Z.
Proof.
unfold_intros.
omega.
Qed.

Lemma div_idg : forall x y, a0 <A y -> (x * y) / y =A x.
Proof.
unfold_intros.
destruct_exists.
let l:=collect_nats in exists (sum_plus1 l).
gen_props.
apply Z_div_mult_full.
apply bingo2.
omega.
Qed.

Lemma mult_le : forall a b c d,
   a0 <=A a -> a <=A b -> a0 <=A c -> c <=A d -> a*c <=A b * d.
Proof.
solve_ls_w_l Zmult_le_compat.
Qed.

Lemma le_refl : forall x, x <=A x.
Proof.
solve_ls.
Qed.

Lemma le_trans : forall x y z, x <=A y -> y <=A z -> x <=A z .
Proof.
solve_ls.
Qed.

Lemma lt_plus : forall x y z t, x <A y -> z <A t -> (x + z) <A (y + t).
Proof.
solve_ls.
Qed.

Lemma mult_pos : forall x y : A, 0<A x -> 0<A y -> 0<A x*y.
Proof.
solve_ls_w_l Z.mul_pos_pos.
Qed.

Lemma lt_plus_inv : forall x y z, (x + z) <A (y + z) -> x <A y .
Proof.
solve_ls. 
Qed.

Lemma le_plus : forall x y z t, x <=A y -> z <=A t -> (x + z) <=A (y + t).
Proof.
solve_ls. 
Qed.

Lemma le_lt_plus : forall x y z t, x <=A y -> z <A t -> (x + z) <A (y + t).
Proof.
solve_ls. 
Qed.

Lemma le_plus_inv : forall x y z, (x + z) <=A (y + z) -> x <=A y .
Proof.
solve_ls. 
Qed.

Lemma le_mult_simpl : forall x y z , (a0 <=A z) -> (x <=A y)-> (x * z) <=A (y *z).
Proof.
solve_ls_w_l Zmult_le_compat_r.
Qed.

Lemma le_mult : forall x y z, a0 <=A x -> y <=A z -> x*y <=A x*z.
Proof.
solve_ls_w_l Zmult_le_compat_l.
Qed.

Lemma lt_mult_inv : forall x y z, a0 <A x -> (x * y) <A (x * z) -> y <A z .
Proof.
solve_ls_w_l Zmult_lt_reg_l. 
Qed.

Lemma Zlt_mult_inv2 : forall x y z:Z, (x < 0 -> (x * y) < (x * z) -> z < y)%Z .
Proof.
intros.
apply Zmult_lt_reg_l with (- x)%Z.
omega.
apply Zplus_lt_reg_l with (x* z + x*y)%Z.
ring_simplify.
assumption.
Qed.

Lemma lt_mult_inv2 : forall x y z, x <A 0 -> (x * y) <A (x * z) -> z <A y .
Proof.
solve_ls_w_l Zlt_mult_inv2.
Qed.

Lemma Zle_mult_inv2 : forall x y z:Z, (x < 0 -> (x * y) <= (x * z) -> z <= y)%Z.
Proof.
intros.
apply Zmult_le_reg_r with (-x)%Z.
omega.
ring_simplify.
eapply Zplus_le_reg_l with (x*y + z*x)%Z.
ring_simplify.
apply H0.
Qed.

Lemma le_mult_inv2 : forall x y z, x <A 0 -> (x * y) <=A (x * z) -> z <=A y .
Proof.
solve_ls_w_l Zle_mult_inv2.
Qed.

Lemma lt_mult : forall x y z, 0 <A x -> y <A z -> x*y <A x*z.
Proof.
solve_ls_w_l Zmult_lt_compat_l.
Qed.

Lemma Zle_mult_inv : forall x y z:Z, (0 < x)%Z -> (x * y <= x * z)%Z -> (y <= z)%Z.
Proof.
intros.
eapply Zmult_lt_0_le_reg_r.
eassumption.
rewrite (Zmult_comm y x).
rewrite (Zmult_comm z x).
eassumption.
Qed.

Lemma le_mult_inv : forall x y z, a0 <A x -> (x * y) <=A (x * z) -> y <=A z .
Proof.
solve_ls_w_l Zle_mult_inv.
Qed.

Lemma le_mult_general : 
  forall x y z t, 0 <=A x -> x <=A y -> 0 <=A z -> z  <=A t -> x*z <=A y*t.
Proof.
solve_ls_w_l Zmult_le_compat.
Qed.

Lemma le_mult_neg : forall x y z, x <A 0 -> y <=A z -> x*z <=A x*y.
Proof.
solve_ls_w_l Z.mul_le_mono_neg_l.
Qed.

Lemma lt_0_1 : (a0 <A a1).
Proof.
solve_ls.
Qed.

Lemma lt_m1_0 : (-a1 <A 0).
Proof.
solve_ls.
Qed.

Lemma lt_trans : forall x y z, x <A y -> y <A z -> x <A z .
Proof.
solve_ls.
Qed.

Lemma le_lt_trans : forall x y z, x <=A y -> y <A z -> x <A z .
Proof.
solve_ls.
Qed.

Lemma lt_le_trans : forall x y z, x <A y -> y <=A z -> x <A z .
Proof.
solve_ls.
Qed.

Lemma lt_le_2 : forall x y, (x <A y) -> (x+1 <=A y).
Proof.
solve_ls.
Qed.

Lemma Znot_le_lt : forall x y:Z, ~(x <= y)%Z -> (y < x)%Z.
Proof.
intros; omega.
Qed.

Lemma abs_minus : forall x, | - x| =A |x|.
Proof.
solve_ls_w_l Z.abs_opp.
Qed. 

Lemma abs_max : forall x, x <=A |x|.
Proof.
unfold_intros.
destruct_exists.
exists 0%nat.
intros.
rewrite Z.abs_max.
assert (H':((x n)<= -(x n) \/ (x n) >= - (x n))%Z) by omega.
destruct H'.
rewrite Zmax_right.
omega.
omega.
rewrite Zmax_left.
omega.
omega.
Qed.

Lemma le_id : forall x y, x <=A y -> y <=A x -> x =A y.
Proof.
solve_ls.
Qed.

Lemma not_lt_0_0 : ~a0 <A a0.
Proof.
unfold_intros.
intro H; destruct H.
assert (0<0)%Z.
apply (H (x+1)%nat).
omega.
omega.
Qed.

Lemma contradict_lt_le : forall s x, s <A x -> x <=A s -> False.
Proof.
solve_ls.
Qed.

Lemma le_lt_False : forall x y, x <=A y -> y <A x -> False.
Proof.
solve_ls.
Qed.

Lemma div_le2 : forall a b, 0 <A a -> 0<=A b -> a*(b/a) <=A b.
Proof.
intros.
rewrite div_mod2.
setoid_replace b with (b+0) at 3 by ring.
apply le_plus.
apply le_refl.
apply le_plus_inv with (b mod%a).
ring_simplify.
apply div_mod3b.
assumption.
left.
assumption.
Qed.

(** properties of lim **)

Lemma  ANS1 : lim a1.
Proof.
unfold lim.
exists (fun (n:nat) => 2%Z).
split.
unfold std.
exists 0%nat.
intros; trivial.
split.
unfold leA, ltA, a0; simpl.
exists 0%nat.
intros; solve [auto with zarith].
rewrite abs_pos_val.
unfold ltA, a1; intros.
exists 0%nat.
intros; simpl; omega.
unfold leA; intros.
exists 0%nat.
unfold a0, a1.
intros; simpl; omega. 
Qed.

Lemma ANS2a : forall x y, lim x -> lim y -> lim (x + y).
Proof.
intros x y Hx Hy.
elim Hx.
intros pp (Hstdpp, (Hle0pp,Habspp)).
elim Hy.
intros qq (Hstdqq, (Hle0qq,Habsqq)).
unfold lim.

unfold absA,ltA,a0 in *.
elim Habspp.
intros a Ha.
elim Habsqq.
intros b Hb.

elim Hle0pp.
intros r Hr.
elim Hle0qq.
intros s Hs.

elim Hstdpp.
intros ep Hep.
elim Hstdqq.
intros eq Heq.

exists (fun (n:nat) => (Zplus (pp (a+r+ep+1)%nat) (qq (b+s+eq+1)%nat))).
split.
unfold std.
exists (0)%nat.
intros; trivial.
split.
unfold leA, a0.
exists (plus a (plus b (plus r s)))%nat.
intros.
assert (Z.le 0 (pp (a+r+ep+1)%nat)).
apply Hr.
omega.
assert (Z.le 0 (qq (b+s+eq+1)%nat)).
apply Hs.
omega.
omega.
unfold plusA.
exists (plus ep (plus eq (plus a b)))%nat.
intros.

apply Z.le_lt_trans with (m:=Zplus (Z.abs (x n)) (Z.abs (y n))).
apply Z.abs_triangle.
assert (forall a b c d:Z, Z.lt a b -> Z.lt c d -> Z.lt (Zplus a c) (Zplus b d)).
intros; omega.
apply H0.
replace (pp (a + r + ep + 1)%nat) with (pp n).
apply Ha.
omega.
apply Hep.
omega.
omega.
replace (qq (b + s + eq + 1)%nat) with (qq n).
apply Hb.
omega.
apply Heq.
omega.
omega.
Qed.

Lemma ANS2b : forall x y, lim x -> lim y -> lim (x * y).
Proof.
intros x y Hx Hy.
elim Hx.
intros pp (Hstdpp, (Hle0pp,Habspp)).
elim Hy.
intros qq (Hstdqq, (Hle0qq,Habsqq)).
unfold lim.

unfold absA,ltA,a0 in *.
elim Habspp.
intros a Ha.
elim Habsqq.
intros b Hb.

elim Hle0pp.
intros r Hr.
elim Hle0qq.
intros s Hs.

elim Hstdpp.
intros ep Hep.
elim Hstdqq.
intros eq Heq.

exists (fun (n:nat) => (Zmult (Z.abs (pp (a+r+ep+1)%nat)+1%Z) (Z.abs (qq (b+s+eq+1)%nat)+1%Z))).
split.
unfold std.
exists (0)%nat.
intros; trivial.
split.
unfold leA, a0.
exists (plus a (plus b (plus r s)))%nat.
intros.
solve [auto with zarith].

unfold multA.
exists (plus ep (plus eq (plus a b)))%nat.
intros.
rewrite Zabs_Zmult.
apply Zmult_lt_compat.
split.
solve [auto with zarith].
rewrite (Z.abs_eq (pp (a + r + ep + 1)%nat)).
apply Z.lt_le_trans with (m:= pp (a + r + ep + 1)%nat ).
replace (pp (a + r + ep + 1)%nat) with (pp n).
apply Ha.
omega.
apply Hep.
omega.
omega.
omega.
apply Hr.
omega.
split.
solve [auto with zarith].
rewrite (Z.abs_eq (qq (b + s + eq + 1)%nat)).
apply Z.lt_le_trans with (m:= qq (b + s + eq + 1)%nat ).
replace (qq (b + s + eq + 1)%nat) with (qq n).
apply Hb.
omega.
apply Heq.
omega.
omega.
omega.
apply Hs.
omega.
Qed.

Lemma ANS2a' : forall x y : A, std x -> std y -> std (x + y). 
Proof.
Admitted. (* easy : ANS2' *)

Lemma ANS1' : std 1. 
Proof.
Admitted. (* easy : ANS1' *)

Lemma std0 : std 0. 
Proof.
Admitted. (* easy : std 0 *)

Lemma ANS2a_minus : forall x, std x -> std (-x ).
Proof.
Admitted. (* easy : ANS2a_minus *)

Lemma ANS4 :  forall x, (exists y, lim y/\ | x | <=A | y |)-> lim x.
Proof.
intros.
elim H; clear H.
intros y (Hlimy,Hy).
unfold lim in *.
elim Hlimy.
intros n (Hstdn, (Hle0n,Hyn)).
exists n.
split.
solve [auto].
split.
solve [auto].
apply le_lt_trans with (y:=(|y|)); assumption.
Qed.

Definition std_alt (u:A) :=exists N:nat, exists a, forall n:nat, n > N -> u n = a.

Lemma std_std_alt : forall u:A, std u <-> std_alt u.
Proof.
intros u; split.
intros H ; unfold std, std_alt in *.
destruct H as [N HN].
exists N.
exists (u (plus N 1)).
intros.
apply HN.
easy.
omega.
intros H; unfold std, std_alt in *.
destruct H as [N HN].
exists N.
intros.
destruct HN as [a Ha].
apply eq_trans with a.
now apply Ha.
now (symmetry; apply Ha).
Qed.

Lemma std_A0_dec : forall x, std x -> {x <A 0}+{x =A 0}+{0 <A x}.
(* to be fixed with Set-exists *)
Proof.
intros x H.
assert (H':std_alt x) by now apply std_std_alt.
clear H.
unfold std_alt in H'.
assert (H'':{N:nat & {a:Z | forall n, n>N -> x n = a}}).
admit. (* only requires std to be defined using Set-exists *)
destruct H'' as [N [a Ha]].
assert (Hdec:({a<0%Z}+{a=0%Z}+{a>0%Z})%Z).
destruct a.
left;right; reflexivity.
right; apply Zgt_pos_0.
left; left; apply Zlt_neg_0.
destruct Hdec as [[HH | HH] | HH].
left; left.
exists N.
intros; unfold a0.
now rewrite  Ha.
left;right.
exists N.
now subst.
right.
exists N.
intros; unfold a0.
rewrite Ha.
omega.
easy.
Admitted.

Lemma std_lim : forall x, std x -> lim x.
(* lim x -> std x is false, e.g. (-1)^n *)
Proof.
intros x Hstdx.
unfold lim, std in *.
elim Hstdx.
intros N HN.
exists (fun (n:nat) => (Z.abs (x (N+1)%nat)+1)%Z).
split.
exists 0%nat; intros; trivial.
split.
unfold leA.
exists 0%nat; intros; simpl.
unfold a0.
solve [auto with zarith].
unfold ltA.
exists N.
intros.
unfold absA.
rewrite (HN (N+1)%nat n).
solve [auto with zarith].
solve [auto with zarith].
assumption.
Qed.

Instance lim_morphism : Proper (equalA ==> Logic.iff) lim.
repeat red.
unfold_intros.
split.

unfold_intros; destruct_exists.
destruct H1 as [H1' [H2' H3']].
exists H0.
split.
assumption.
split.
assumption.
elim H3'.
intros x0 Hx0.
exists (H+x0+1)%nat.
intros.
rewrite <- H2.
apply Hx0.
omega.
omega.

unfold_intros; destruct_exists.
destruct H1 as [H1' [H2' H3']].
exists H0.
split.
assumption.
split.
assumption.
elim H3'.
intros x0 Hx0.
exists (H+x0+1)%nat.
intros.
rewrite H2.
apply Hx0.
omega.
omega.
Qed.

Instance std_morphism : Proper (equalA ==> Logic.iff) std.
repeat red.
unfold_intros.
split.

unfold_intros; destruct_exists.
let l:= collect_nats in exists (sum_plus1 l); simpl in *.
intros.
transitivity (x n).
symmetry; apply H2; omega.
transitivity (x m).
apply H1; omega.
apply H2; omega.

unfold_intros; destruct_exists.
let l:= collect_nats in exists (sum_plus1 l); simpl in *.
intros.
transitivity (y n).
apply H2; omega.
transitivity (y m).
apply H1; omega.
symmetry; apply H2; omega.
Qed.

(** beta may be w or some non-standard Laugwitz-Schmieden number which is <= w *)
Definition beta : A := fun (n:nat) => (Z_of_nat n).

Lemma  Abeta : 0 <A beta.
Proof.
unfold ltA,a0,beta.
exists 1%nat.
intros.
omega.
Qed.

Lemma beta_std : ~std beta.
Proof.
intro H; unfold std in *.
elim H; clear H; intros N HN.
unfold beta in *.
assert (H1:(S N>N)%nat).
omega.
assert (H2:(S (S N)>N)%nat).
omega.
generalize (HN (S N)%nat (S(S N))%nat H1 H2); intro Heq.
assert (S N=S (S N)).
apply inj_eq_rev; assumption.
injection H; intros Hinj.
assert (Hth:(forall n:nat, ~n=(S n))).
intros n; elim n.
simpl; discriminate.
intros n0 Hn0 H'.
apply Hn0.
injection H'.
solve [auto].
generalize (Hth N); intros HthN.
solve [auto].
Qed.

Lemma beta_lim : ~ lim beta.
Proof.
intro H; unfold lim in *.
elim H; clear H; intros p (Hstdp,(Hle0p,Hwp)).
unfold ltA,a0 in *.
elim Hstdp.
intros b Hb.
elim Hwp.
intros a Ha.
elim Hle0p.
intros c Hc.
(* w (p (a+b+c+1) + a + b + c + 1) = p (a+b+c+1) + a+b+c+1 *)
(* p (p (a+b+c+1) + a + b + c + 1) = p (a + b + c + 1) because p(a+b+c+1)>=0 et Hb: p is std *)
pose (px:=p (a+b+c+1)%nat).
assert (0<= px)%Z.
apply Hc.
omega.
pose (x:=((Z.abs_nat px)+a+b+c+1)%nat).
assert ((|beta |) (x) < p (x))%Z.
apply Ha.
unfold px,x in *.
omega.

assert  ((|beta |) (x) >= p (x))%Z.
unfold absA in *.
unfold beta.
unfold x.
replace (p (Z.abs_nat px + a + b + c + 1)%nat)%Z with 
(p (a+b+c+1)%nat)%Z.
rewrite Z.abs_eq.
replace (Z.abs_nat px + a + b + c + 1)%nat with (Z.abs_nat (px + (Z_of_nat (a + b + c + 1))))%nat.
rewrite inj_Zabs_nat.
rewrite Z.abs_eq.
unfold px.
omega.
omega.
rewrite Zabs_nat_Zplus.
rewrite Zabs_nat_Z_of_nat.
ring.
unfold px; apply Hc.
omega.
solve [auto with zarith].
solve [auto with zarith].
apply Hb.
omega.
omega.
omega.
Qed.

Lemma nat_Z : forall a:Z, (0 <= a)%Z -> exists qnat, Z.of_nat qnat = a.
Proof.
intros.
exists (Z.to_nat a).
apply Z2Nat.id; assumption.
Qed.

Lemma std_alt_lt_beta : forall a, std_alt a /\ 0<=A a -> a <A beta.
Proof.
intros.
destruct H as [Hn Hp].
destruct Hn as [n Hn].
destruct Hn as [q Hq].
destruct Hp as [p Hp].
unfold beta, ltA.
assert (Hq0: (0<=q)%Z).
generalize (Hq (n+p+1)%nat); intros.
generalize (Hp (n+p+1)%nat); intros.
rewrite <- H.
apply H0.
omega.
omega.
elim (nat_Z q Hq0).
intros qnat Hqnat.
exists (n+qnat+p)%nat.
intros;rewrite Hq by omega.
rewrite <- Hqnat.
omega.
Qed.

Lemma lim_lt_beta : forall a, lim a/\ 0<=A a -> a <A beta.
Proof.
unfold lim;intros.
destruct H as [[c H] H1].
destruct H as [Hex [Hex2 Hex3]].
assert (std_alt c) by (apply std_std_alt; assumption).
rewrite abs_pos_val in Hex3 by assumption.
apply lt_trans with c.
assumption.
apply std_alt_lt_beta; split; assumption.
Qed.

(** induction *)

Parameter nat_like_induction : 
  forall P : A -> Type, 
    P a0 ->
    (forall n:A, (std n /\ 0 <=A n) -> P n -> P (plusA n a1)) ->
    forall n:A, (std n /\ 0<=A n) -> P n.

(*

Definition nat2A : nat -> {n:A | std n /\ 0<=A n}.
Proof.
fix 1.
intros n; case n.
exists a0.
clear nat2A n; abstract (split; [apply std0 | apply le_refl]).
intros p. 
case (nat2A p).
intros xp Hxp.
exists (xp+a1).
clear nat2A n p;
abstract (split; [apply ANS2a'; [intuition | apply ANS1']| setoid_replace 0 with (0+0) by ring; apply le_plus; [intuition| apply lt_le;apply lt_0_1]]).
Defined.

Lemma A_is_nat : 
forall a:A, std a /\ 0<=A a -> exists n:nat, a=proj1_sig (nat2A n).
Proof.
intros.
apply (nat_like_induction (fun (a:A) => exists n : nat, a = proj1_sig (nat2A n))).
exists 0%nat.
simpl; reflexivity.
intros n Hn Hex.
destruct Hex as [p Hp].
exists (S p)%nat.
simpl.
destruct (nat2A p) as [x Hx].
simpl in *.
now apply f_equal2.
assumption.
Qed.

*)

Parameter nat_like_induction_r1 :
forall H:std 0 /\ 0<=A0, forall P : A -> Type, 
    forall (h0: P a0), 
    forall hr : (forall n:A, (std n /\ 0 <=A n) -> P n -> P (plusA n a1)),
    nat_like_induction P h0 hr a0 H = h0.

Parameter nat_like_induction_r2 :
forall P : A -> Type, 
    forall n:A, forall H:std n/\0<=A n,
    forall Hn':std (n+1)/\0<=A(n+1),
forall (h0: P a0), 
    forall hr : (forall n:A, (std n /\ 0 <=A n) -> P n -> P (plusA n a1)),
    nat_like_induction P h0 hr (n + 1) Hn' = 
    hr n H (nat_like_induction P h0 hr n H).

End LS.


