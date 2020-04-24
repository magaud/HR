Require Export Bridges_order2_AX.

Module lub_spec_AX (N:Num_w).

Import N.
Module Export XX:=mBridges2(N).

Axiom proof_irr :forall A:Prop, forall x y:A, x=y.

Definition minA (x y:A) := if (A0_dec (x + -y)) then x else y.

Definition least_upper_bound (S:subset) (b:HRw) : Prop := 
  (forall s:HRw, (S s -> b [>=] s)) /\ 
                       (forall b':HRw, b [>] b' -> exists o:HRw, S o/\ o [>] b').

Definition has_least_upper_bound (s:subset) : Prop := exists b, least_upper_bound s b.

Lemma minA_lim : forall x y:A, ~lim x -> ~lim y -> ~lim (minA x y).
Proof.
intros; unfold minA; destruct (A0_dec (x + - y)); assumption.
Qed.

Lemma minA_le : forall x y:A, 0<= x -> 0<=y -> 0<= minA x y.
Proof.
intros; unfold minA; destruct (A0_dec (x + - y)); assumption.
Qed.

Lemma HRwgt_1 : forall m, (m [+] [1]) [>] m.
Proof.
intros m; unfold HRwgt; destruct m; simpl.
exists a1.
split.
apply ANS1.
split.
apply lt_0_1.
ring_simplify.
apply le_refl.
Qed.

Lemma HRwgt_upper_bound : forall X:subset, forall m, upper_bound X m -> upper_bound X (HRwplus m [1]).
Proof.
unfold upper_bound; intros.
apply HRwgt_trans with m.
apply HRwgt_1.
apply H; assumption.
Qed.

Lemma HRwgt_upper_bound_2 : forall X:subset, forall x y, upper_bound X x -> y [>] x -> upper_bound X y.
Proof.
unfold upper_bound; intros.
apply HRwgt_trans with x.
assumption.
apply H; assumption.
Qed.

(* properties to move into Numbers.v *)

(*Parameter overspill_principle : forall P:A -> Prop, (forall n:A, lim n /\ 0<=n -> P n) ->
   (exists v:A, ~lim v (* infinitely large *) /\ 0<v /\ (forall m:A, 0<=m /\ m <=v -> P m)).
*)

Parameter overspill_principle' : forall P:A -> Prop, (forall n:A, std n /\ 0<=n -> P n) ->
   (exists v:A, ~lim v (* infinitely large *) /\ 0<v /\ (forall m:A, 0<=m /\ m <=v -> P m)).

Parameter overspill_principle2 : 
forall P:A -> A -> Prop, (forall n:A, std n /\ 0<=n -> forall m:A, std m /\ 0<=m -> P n m) ->
   (exists v:A, ~lim v (* infinitely large *) /\ 0<v /\ (forall n:A, 0<=n /\ n <=v -> forall m:A, 0<=m /\ m <=v -> P n m)).




Lemma ANS4_special : forall n k:A, (lim n /\ 0<=n) -> (0 <=k /\ k <= n) -> lim k /\ 0<=k.
Proof.
intros n k (Hlimn, Hlen) (Hlimk, Hlek).
split.
apply ANS4.
exists n.
split.
assumption.
rewrite abs_pos_val by assumption.
rewrite abs_pos_val by assumption.
assumption.
assumption.
Qed.

Lemma H0 : lim 0 /\0<=0.
Proof.
split; [apply lim0 | apply le_refl].
Qed.

Parameter ANS52 :
forall P : A -> Prop,
(forall u : forall n:A, std n /\ 0 <= n -> A,
  forall H0: std 0 /\ 0<=0, P (u 0 H0) -> 
  (forall n:A, forall Hn : std n /\ 0 <= n,
     (forall k:A, forall Hk': std k /\ 0<= k, forall Hk:0 <= k /\ k <= n,  forall Hn1 : std (n+1)/\0<=(n+1), P (u k Hk') 
       -> P(u (plusA n 1) Hn1))) -> 
    (** {u:A->A | ... } *)
    {v:A->A |forall n:A, forall Hn:std n /\ 0<= n,  
              forall k:A,  forall Hk': std k /\ 0<= k, forall Hk:0 <= k /\ k <= n, P (v k) /\ v k = u k Hk'}).

(*
Parameter ANS5 :
forall P :A -> Prop,
(forall u : forall n:A, lim n /\ 0 <= n -> A,
  P (u 0 H0) -> 
  (forall n:A, forall Hn : lim n /\ 0 <= n,
     (forall k:A, forall Hk:0 <= k /\ k <= n,  forall Hn1 : lim (n+1)/\0<=(n+1), P (u k (ANS4_special n k Hn Hk)) 
       -> P(u (plusA n 1) Hn1))) -> 
    (** {u:A->A | ... } *)
    sigT(fun v => forall n:A, forall Hn:lim n /\ 0<= n, 
              forall k:A,  forall Hk:0 <= k /\ k <= n, P (v k) /\ v k = u k (ANS4_special n k Hn Hk))).
*)
Lemma std_lim_pos :  forall k:A, std k /\ 0<= k -> lim k /\ 0<=k.
Proof.
intros k (Hk1,Hk2).
split.
apply std_lim; assumption.
assumption.
Qed.

Lemma H0std : std 0 /\ 0 <= 0.
Proof.
split.
apply std0.
apply le_refl.
Qed.

Definition extends (u:(forall k:A, std k /\ 0<= k -> A)) : (A->A).
intros x.

Check (ANS52 (fun x => True) u H0std I).
elim 
  (ANS52 (fun x => True) u H0std I  (fun x y z t a b c => I)).
intros v Hv.
exact (v x).
Defined.

Lemma extends_id : forall u:(forall k:A, std k /\ 0<=k -> A),
forall n,  forall H:std n /\ 0 <= n, u n H = (extends u) n.
Proof.
intros u n H.
unfold extends.
case  (ANS52 (fun _ : A => True) u H0std I
     (fun (x : A) (_ : std x /\ 0 <= x) (z : A) (_:std z /\ 0<= z) (_ : 0 <= z /\ z <= x) (_ : std (x+1) /\ 0 <= (x+1))
        (_ : True) => I)).
simpl.
intros.
assert (Hk : 0 <= n /\ n <= n).
split.
solve [intuition].
apply le_refl.
generalize (a n H n H Hk) .
intros.
(*rewrite (proof_irr _ H (ANS4_special n n H Hk)).*)
solve [intuition].
Qed.

Parameter min_lim : A ->  (forall k:A, std k /\ 0<= k ->A) -> A.
(* defines the min (k = 0 to n (1st argument) of the elements of a sequence *)

Parameter min_lim_def : 
forall n:A, forall Hn : std n/\0<=n,
forall (b:forall k:A, (std k /\ 0<=k) -> A), forall k:A, forall Hk:0<= k /\ k <= n, 
  forall Hk':std k/\0<=k, min_lim n b <= b k Hk'.

Parameter min_lim_prop :
forall P, forall n:A, forall b:forall k:A, (std k /\ 0<=k) -> A, 
 (forall k:A, forall Hk:std k/\0 <= k, k <= n -> P(b k Hk )) -> P (min_lim n b).

Parameter min : forall n:A, (A -> A) -> A.

Parameter min_def :
forall n:A, forall b:A-> A, forall k:A, 0 <= k/\ k <= n -> min n b <= b k.

Parameter min_prop :
forall P, forall n:A, std n -> forall b:A-> A, (forall k:A, std k -> 0 <= k/\ k <= n -> P(b k)) -> P (min n b).

Parameter min_def2 : forall (n m:A), forall b:A-> A,  m<=n -> min n b <= min m b. 


Lemma lim_pos_P : forall x, lim x /\ 0<x -> P x.
Proof.
intros x (Hx1,Hx2).
unfold P.
exists x.
split.
assumption.
split.
assumption.
rewrite abs_pos_val.
setoid_replace x with (x*1) at 1 by ring.
apply le_mult.
apply lt_le; assumption.
setoid_replace 1 with (0+1) by ring.
apply lt_le_2; apply Aw.
apply lt_le; assumption.
Qed.

Lemma has_limit : 
forall u:forall n, std n/\ 0<=n-> HRw, forall x:HRw, x [>] [0] -> 
forall eps : HRw, eps [>] [0] -> 
  (forall n:A, forall Hn:std n/\ 0<=n, (HRwequal (u n Hn) (HRwmult (power two_third n Hn) x))) ->
  exists n:A,  std n/\0 <=n /\ forall H:std n/\ 0 <= n, eps [>] u n H.
Proof.
intros.
elim (power_lim two_third (proj1 two_third_prop) (proj2 two_third_prop) x H (eps) H1).
intros n Hn.
exists n.
repeat split.
solve [intuition].
solve [intuition].
intros.
setoid_rewrite H2.
rewrite HRwmult_comm.
decompose [and] Hn.
apply H7.
Qed.

End lub_spec_AX.
