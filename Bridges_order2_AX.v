Require Export LUB_spec.

Module mBridges2(N:Num_w).

Import N.
Module Export HH := lub_spec(N).

Axiom A0_dec : forall x, {x < 0}+{x==0}+{0 < x}.
(** holds for axiomatic non-standard integers but not prouvable in Laugwitz-Schmieden : counter-example : (-1)^n *)

Axiom not_le_lt : forall x y, ~x <= y -> y < x.
(** holds for axiomatic non-standard integers not prouvable in Laugwitz_schmiden : counter-example : b_n = a_n + (-1)^n *) 

Lemma R2_2 : forall x y,  x [>] y -> forall z, x [>] z \/ z [>] y.
Proof.
intros x; case x; clear x.
intros xx Hxx.
intros y; case y; clear y.
intros yy Hyy.
intros H; unfold HRwgt in H.
intros z; case z; clear z.
intros zz Hzz.
simpl.
elim H.
intros n (Hlim,(Hlt,Hn)).
setoid_replace (xx+ -yy) with (xx + -yy +zz + - zz) in Hn by ring.
setoid_replace (n * (xx + - yy + zz + - zz)) with (n*(xx+ -zz) + n*(zz+ -yy)) in Hn by ring.

simpl.
elim (A0_dec ((xx + (- zz)) + - (zz + (- yy)))). (* occurs in R2_2 *)
intros a; elim a; clear a.
(* negative *)
intros.
right.
exists (n+n).
split.
apply ANS2a; assumption.
split.
setoid_replace 0 with (0+0) by ring; apply lt_plus; assumption.
apply le_trans with (y:= (n * (xx + - zz) + n * (zz + - yy))).
assumption.
setoid_replace ((n + n) * (zz + - yy)) with (n*(zz+ -yy) + n*(zz + - yy)) by ring.
apply le_plus.
rewrite (mult_comm  n (xx + -zz)).
rewrite (mult_comm  n (zz + -yy)).
apply le_mult_simpl.
apply lt_le; assumption.
apply le_plus_inv with (z:= - (zz + - yy)).
setoid_replace (zz + - yy + - (zz + - yy)) with 0 by ring.
apply lt_le.
assumption.
apply le_refl.

(* zero *)
intros.
left.
exists (n+n).
split.
apply ANS2a; assumption.
split.
setoid_replace 0 with (0+0) by ring; apply lt_plus; assumption.
apply le_trans with (y:= (n * (xx + - zz) + n * (zz + - yy))).
assumption.
setoid_replace ((n + n) * (xx + - zz)) with (n*(xx+ -zz) + n *(xx + - zz)) by ring.
apply le_plus.
rewrite (mult_comm  n (xx + -zz)).
apply le_refl.
rewrite (mult_comm  n (xx + -zz)).
rewrite (mult_comm  n  (zz + - yy)).
apply le_mult_simpl.
apply lt_le.
assumption.
apply le_plus_inv with (z:= - (zz + - yy)).
rewrite b.
setoid_replace (zz + - yy + - (zz + - yy))  with 0 by ring.
apply le_refl.

(* positive *)
intros.
left.
exists (n+n).
split.
apply ANS2a; assumption.
split.
setoid_replace 0 with (0+0) by ring; apply lt_plus; assumption.
apply le_trans with (y:= (n * (xx + - zz) + n * (zz + - yy))).
assumption.
setoid_replace ((n + n) * (xx + - zz)) with (n*(xx+ -zz) + n *(xx + - zz)) by ring.
apply le_plus.
rewrite (mult_comm  n (xx + -zz)).
apply le_refl.
rewrite (mult_comm  n (xx + -zz)).
rewrite (mult_comm n  (zz + - yy)).
apply le_mult_simpl.
apply lt_le.
assumption.

apply le_plus_inv with (z:= - (zz + - yy)).
setoid_replace (zz + - yy + - (zz + - yy)) with 0 by ring.
apply lt_le.
assumption.
Qed.

Lemma R2_3 : forall x y, ~HRwdiff x y -> HRwequal x y.  
Proof.
intros x; elim x; intros xx Hxx.
intros y; elim y; intros yy Hyy.
clear x y.
intros Hxy.
unfold HRwdiff, HRwgt, HRwequal in *.
firstorder.
elim (A0_dec (xx+ -yy)). (* occurs in R2_3 *)
intros Hdec.
elim Hdec.
intros Hxxyy.
rewrite abs_neg_val.
setoid_replace (n * - (xx + - yy)) with (n * (yy + - xx)) by ring.
apply lt_le.
apply not_le_lt.
intro.
apply (H2 n); repeat split; assumption.
apply lt_le; assumption.
intros Heq.
rewrite Heq.
rewrite abs_pos_val.
setoid_replace (n * 0  ) with 0 by ring.
apply lt_le.
apply Aw.
apply le_refl.
intros.
rewrite abs_pos_val.
apply lt_le.
apply not_le_lt.
intro; apply (H1 n).
repeat split; solve [ apply lt_le; assumption | assumption].
apply lt_le; assumption.
Qed.

Lemma not_HRwgt_HRwge : forall a b : HRw, ~ ( a [>] b)-> b [>=] a.
Proof.
intros a b; destruct a as [a' Ha']; destruct b as [b' Hb'].
unfold HRwgt, HRwge in *.
intros.
firstorder.
generalize (H n); intros.
apply lt_le.
apply not_le_lt.
intro.
apply H8.
split.
assumption.
split.
assumption.
assumption.
Qed.

End mBridges2.