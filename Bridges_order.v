Require Export Heyting_field.
Require Export HRwgt.

Module mBridges(N:Num_w).

Import N.
Module Export HH := mHeyting(N).
(** R2 *)
Lemma R2_1 : forall x y, ~(x [>] y /\ y [>] x).
intros X Y (HXY,HYX).
generalize (HRwgt_Zgt X Y HXY).
generalize (HRwgt_Zgt Y X HYX).
elim X; intros xx Hxx.
elim Y; intros yy Hyy.
intros.
eapply le_lt_False; eauto.
apply lt_le; assumption.
Qed.

Lemma R2_4 : forall X Y,  X [>] Y -> forall Z,  X [+] Z [>] Y [+] Z.
Proof.
intros X; case X; intros xx Hxx.
intros Y; case Y; intros yy Hyy.
simpl; intros HXY Z; case Z; intros zz Hzz.
simpl.
elim HXY.
intros n Hn.
exists n.
setoid_replace (xx + zz + - (yy + zz)) with (xx + - yy) by ring.
assumption.
Qed.

Lemma R2_5_aux1 : w * w <= (a1 + a1) * w * w + -((1+1) * (w / (1+1)) * w).
Proof.
rewrite (div_mod2 (1+1) w).
rewrite mult_distr_l.
setoid_replace ((1 * w + 1 * w) * w + - ((w + - (w %% 1 + 1)) * w))
with ((1 * w + 1 * w) * w + - w * w + (w %% 1 + 1) * w)
by ring.
setoid_replace (w * w) with (w * w+0) by ring.
apply le_plus.
ring_simplify.
apply le_refl.
setoid_replace 0 with ((w %% 1 + 1)*0) by ring.
apply le_mult.
apply div_mod3b.
setoid_replace 0 with (0+0) by ring.
apply lt_plus; apply lt_0_1.
apply lt_le; apply Aw.
left.
setoid_replace 0 with (0+0) by ring.
apply lt_plus; apply lt_0_1.
Qed.

Lemma ANS3bis : ~lim (w / (1+1)).
Proof.
intro.
apply ANS3.
rewrite (div_mod (1+1) w).
apply ANS2a.
apply ANS2b.
apply ANS2a; apply ANS1.
assumption.
apply ANS4.
exists (1+1).
split.
apply ANS2a; apply ANS1.
(*pattern (1+1) at 1; *)
rewrite abs_pos_val.
rewrite abs_pos_val.
apply lt_le; apply div_mod3a.
setoid_replace 0 with (0+0) by ring.
apply lt_plus; apply lt_0_1.
setoid_replace 0 with (0+0) by ring.
apply le_plus; apply lt_le; apply lt_0_1.
apply div_mod3b.
setoid_replace 0 with (0+0) by ring.
apply lt_plus; apply lt_0_1.
left.
setoid_replace 0 with (0+0) by ring.
apply lt_plus; apply lt_0_1.
Qed.

Lemma R2_5 : forall X Y, X [>] [0] /\  Y [>] [0] -> X [*] Y [>] [0].
Proof.
intros X; case X; intros xx Hxx.
intros Y; case Y; intros yy Hyy.
simpl; intros (HX, HY).
elim HX; intros n (Hlimn,(Hlen,Hn)).
elim HY; intros m (Hlimm,(Hlem,Hm)).
setoid_replace (xx + -0) with xx in Hn by ring.
setoid_replace (yy + -0) with yy in Hm by ring.
exists ((m*n)+(m*n)).
setoid_replace (xx*yy/w +- 0) with (xx*yy/w) by ring.
split.
apply ANS2a; apply ANS2b; assumption.
split.
setoid_replace 0 with (0+0) by ring.
apply lt_plus.
setoid_replace 0 with (m*0) by ring.
apply lt_mult; assumption.
setoid_replace 0 with (m*0) by ring.
apply lt_mult; assumption.

apply le_mult_inv with w.
apply Aw.
setoid_replace (w* ((m * n + m * n) * (xx * yy / w)))
with ((m * n + m * n) * (w * (xx * yy / w))) by ring.
apply le_trans with  ((a1 + a1) * w * w + -((1+1) * (w / (1+1)) * w)).
apply R2_5_aux1.
rewrite div_modw2.
rewrite mult_distr_r.
setoid_replace ((m * n + m * n) * (xx * yy)) with 
((1+1)*(n*xx)*(m*yy)) by ring.
apply le_plus.
repeat rewrite <- mult_assoc.
apply le_mult.
setoid_replace 0 with (0+0) by ring.
apply le_plus;apply lt_le; apply lt_0_1.
setoid_replace (n * (xx * (m * yy))) with ((n*xx)*(m*yy)) by ring.
apply le_mult_general.
apply lt_le; apply Aw.
assumption.
apply lt_le; apply Aw.
assumption.
(*ici*)
assert (m*n <= w/(1+1)).
apply le_mult_inv with (1+1).
setoid_replace 0 with (0+0) by ring.
apply lt_plus; apply lt_0_1.
rewrite div_mod2.
apply le_plus_inv with (w%% (1+1)).
ring_simplify.
apply lt_le; apply lim_lt_w.
split.
repeat (apply ANS2a || apply ANS2b || apply ANS1 || assumption).
apply ANS4.
exists (a1+a1).
split.
apply ANS2a; apply ANS1.
rewrite (abs_pos_val (1+1)).
apply lt_le; apply div_mod3.
setoid_replace 0 with (0+0) by ring.
apply lt_plus; apply lt_0_1.
setoid_replace 0 with (0+0) by ring.
apply le_plus; apply lt_le; apply lt_0_1.
setoid_replace 0 with ((1+1)*m*0 + 0) by ring.
apply le_plus.
apply le_mult.
setoid_replace 0 with ((1+1)*0) by ring.
apply le_mult.
setoid_replace 0 with (0+0) by ring.
apply le_plus; apply lt_le; apply lt_0_1.
apply lt_le; assumption.
apply lt_le; assumption.
apply div_mod3b.
setoid_replace 0 with (0+0) by ring.
apply lt_plus; apply lt_0_1.
left; setoid_replace 0 with (0+0) by ring; apply lt_plus; apply lt_0_1.
apply le_trans with  (- (1+1)*(m * n) * w).
setoid_replace ( - ((1 + 1) * (w / (1 + 1)) * w) )
with  ( (-(1 + 1) * w)* (w / (1 + 1))  )
by ring.
setoid_replace (- (1 + 1) * (m * n) * w) with ((- (1 + 1) * w) * (m * n)) by ring.
apply le_mult_neg.
apply lt_plus_inv with ( (1+1)* w).
ring_simplify.
setoid_replace 0 with (0+0) by ring.
setoid_replace ((1+1)* w) with (w + w) by ring.
apply lt_plus; apply Aw.
assumption.
setoid_replace ((m * n + m * n) * - (xx * yy %% w))
with (- (1+1)* (m*n) * (xx * yy %% w)) by ring.
apply le_mult_neg.
apply lt_plus_inv with ((1+1)* (m*n)).
ring_simplify.
setoid_replace 0 with (m*0+m*0) by ring.
setoid_replace ((1+1)* m * n) with (m*n + m*n) by ring.
apply lt_plus;apply lt_mult; assumption.
apply lt_le;apply div_mod3a.
apply Aw.
Qed.

Lemma HRwgt_HRwplus_inv_r : forall X Y Z:HRw,  X [+] Z [>] Y [+] Z ->  X [>] Y.
Proof.
intros X Y Z.
elim X; intros xx Hxx.
elim Y; intros yy Hyy.
elim Z; intros zz Hzz.
unfold HRwgt; simpl.
intros.
elim H.
intros n (Hlim, (H0, H')).
ring_simplify in H'.
exists n.
split.
assumption.
split.
assumption.
ring_simplify.
assumption.
Qed.

Lemma HRwgt_HRwplus_inv_l : forall a b c, c [+] a [>] c [+] b -> a [>] b.
Proof.
intros X Y Z.
elim X; intros xx Hxx.
elim Y; intros yy Hyy.
elim Z; intros zz Hzz.
unfold HRwgt; simpl.
intros.
elim H.
intros n (Hlim, (H0, H')).
ring_simplify in H'.
exists n.
split.
assumption.
split.
assumption.
ring_simplify.
assumption.
Qed.

Lemma HRwgt_HRwplus_l: forall a b d, b [>] d -> a [+] b [>] a [+] d.
Proof.
intros a b d Hbd; destruct a; destruct b; destruct d; unfold HRwgt in *; simpl.
elim Hbd.
intros n Hn.
exists n.
setoid_replace ((x + x0 + - (x + x1))) with (x0 + - x1) by ring.
assumption.
Qed.

Lemma HRwgt_HRwplus_r: forall a c b, a [>] c -> a[+] b [>] c [+] b.
Proof.
intros; now apply R2_4.
Qed.

Lemma HRwgt_trans : forall X Y Z,  X [>] Y ->  Y [>] Z ->  X [>] Z.
Proof.
intros X; case X; intros xx Hxx.
intros Y; case Y; intros yy Hyy.
intros Z; case Z; intros zz Hzz.
simpl.
intros.
elim H; intros n1 (Hn1,(Hn1', Hn1'')); clear H.
elim H0; intros n2 (Hn2, (Hn2', Hn2'')); clear H0.
exists (n1+n2).
split.
apply ANS2a; assumption.
split.
setoid_replace 0 with (0+0) by ring.
apply lt_plus; assumption.
assert (0 <= xx + - yy).
eapply le_mult_inv with n1.
assumption.
apply le_trans with w.
ring_simplify.
apply lt_le; apply Aw.
assumption.

assert (w + w <= (n1+n2)* (xx + - zz)).
setoid_replace ((n1+n2)*(xx + -zz)) with ((n1+n2)*(xx + -yy) + (n1+n2)*(yy + -zz)) by ring.
apply le_plus.
apply le_trans with (n1 * (xx + - yy)).
assumption.
apply le_mult_simpl.
assumption.
setoid_replace n1 with (n1+0) by ring.
setoid_replace (n1+0+n2) with (n1+n2) by ring.
apply le_plus.
apply le_refl.
apply lt_le; assumption.

apply le_trans with (n2 * (yy + - zz)).
assumption.
apply le_mult_simpl.
eapply le_mult_inv with n2.
assumption.
apply le_trans with w.
ring_simplify.
apply lt_le; apply Aw.
assumption.

setoid_replace n2 with (0+n2) by ring.
setoid_replace (n1 + (0 + n2)) with (n1+n2) by ring.
apply le_plus.
apply lt_le; assumption.
apply le_refl.

setoid_replace w with (0 + w) by ring. 
apply le_trans with (w + w).
apply le_plus.
apply lt_le; apply Aw.
apply le_refl.
assumption.
Qed.

(** R3 *)
Lemma Archimedes : forall X:HRw, exists n:HRw, n [>] X.
Proof.
intros x; elim x.
intros xx Hxx; unfold P in *.
elim Hxx; intros n (Hlim, (Hle0, H)).
assert (HP:(P(xx+ w))).
apply Padd.
assumption.
apply Pw.
(* we choose n = xx[+] *)
exists (exist
       (fun x0 : A => exists n1 : A, lim n1 /\ 0 < n1 /\ (|x0 |) <= n1 * w)
       (xx+ w) HP).
simpl.
exists n.
split.
solve [auto].
split.
solve [auto].
setoid_replace (xx + w + - xx) with w by ring.
setoid_replace w with (1* w) by ring.
setoid_replace (n * (1 * w)) with (n* w) by ring.
apply mult_le.
apply lt_le. 
apply lt_0_1.
setoid_replace 1 with (0+1) by ring.
apply lt_le_2.
assumption.
apply lt_le; apply Aw.
apply le_refl.
Qed.

Lemma HRwgt_HRwopp : forall x y, x [>] y -> -w y [>] -w x.
Proof.
intros x y; case x; intros xx Hxx; case y; intros yy Hyy.
simpl.
intros.
elim H.
intros n (Hlim,(Hle,H')).
exists n.
repeat split.
assumption.
assumption.
setoid_replace (- yy + - - xx) with (xx + - yy) by ring.
assumption.
Qed.

(** Additionnal lemmas (prouvable with the axioms of Numbers.v) *)

Lemma HRwequal_HRwgt_False : forall x y, x [=] y -> x [>] y -> False.
Proof.
unfold HRwequal, HRwgt in *; destruct x as [x Hx]; destruct y as [y Hy]; simpl.
intros Heq; intro Hdiff.
destruct Hdiff as [n [ Hn1 [Hn2 Hn3]]].
assert (Hn1':lim (n+1)).
apply ANS2a; [assumption | apply ANS1].
assert (Hn2':(ltA 0 (plusA n 1))).
setoid_replace 0 with (0+0) by ring.
apply lt_plus.
assumption.
apply lt_0_1.
generalize (Heq (n+1) Hn1' Hn2'); clear Heq; intros Heq.
assert (Hpos:(0 < x + - y)).
apply lt_mult_inv with n.
assumption.
setoid_replace (n * 0) with 0 by ring.
apply lt_le_trans with w.
apply Aw.
assumption.
rewrite abs_pos_val in Heq.
assert ((n+1) * (x + - y) <= n * (x + - y)).
apply le_trans with w; assumption.
assert ((n+1)<= n).
eapply le_mult_inv.
apply Hpos.
rewrite (mult_comm _ (n+1)).
rewrite (mult_comm _ n).
assumption.
eapply contradict_lt_le.
2: apply H0.
setoid_replace n with (n+0) at 1 by ring.
apply le_lt_plus.
apply le_refl.
apply lt_0_1.
apply lt_le; assumption.
Qed.

Lemma w_not_neg : w <= 0 -> False.
Proof.
intros; eapply contradict_lt_le; [apply Aw | assumption].
Qed.

(*******************************)
(* Least-upper-bound principle *)
(*******************************)

(* preliminary lemmas *)

Lemma HRw1_HRw0 : HRwdiff [1] [0].
Proof.
unfold HRwdiff; left; unfold HRwgt; simpl.
exists a1.
split.
apply ANS1.
split.
apply lt_0_1.
ring_simplify.
apply le_refl.
Qed.

Lemma lemma_HRw3 : HRwdiff HRw3 [0].
Proof.
unfold HRwdiff.
left.
unfold HRwgt; simpl.
exists 1.
split.
apply ANS1.
split.
apply lt_0_1.
setoid_replace (1*(w + w + w + -0)) with (w + w + w) by ring.
pattern w at 1 ; setoid_replace w with (w+0+0) by ring.
setoid_replace (w + 0 + 0 + (w + 0 + 0) + (w + 0 + 0)) with (w+ w+ w) by ring.
apply le_plus.
apply le_plus.
apply le_refl.
apply lt_le; apply Aw.
apply lt_le; apply Aw.
Qed.

Definition one_third := (HRwinv HRw3  lemma_HRw3).
Definition two_third := HRwmult ([2]) (HRwinv HRw3  lemma_HRw3).

Lemma three_one_third : (one_third [+] one_third [+] one_third) [=] [1].
Proof.
unfold one_third, HRwequal, HRw3.
simpl.
unfold P in *.
intros.
apply le_trans with (n+n+n).
setoid_replace (n+n+n) with (n*(1+1+1)) by ring.
apply le_mult.
apply lt_le; assumption.
apply le_mult_inv with ((1+1+1) * w).
setoid_replace 0 with ((1+1+1)*0) by ring.
apply lt_mult.
setoid_replace 0 with (0+0+0) by ring.
apply lt_plus.
apply lt_plus; apply lt_0_1.
apply lt_0_1.
apply Aw.
setoid_replace ((1 + 1 + 1) * w *
(|w * w / (w + w + w) + w * w / (w + w + w) + w * w / (w + w + w) + - w |))
with 
(|(1 + 1 + 1) * w *
(w * w / (w + w + w) + w * w / (w + w + w) + w * w / (w + w + w) + - w )|).
2: repeat rewrite abs_prod; rewrite (abs_pos_val w).
2: rewrite (abs_pos_val (1+1+1)).
2: ring.
2: setoid_replace 0 with (0+0+0) by ring.
2:repeat apply le_plus; apply lt_le; apply lt_0_1.
2: apply lt_le; apply Aw.

setoid_replace ((1+1+1) * w) with (w + w + w) by ring.
setoid_replace ((w + w + w) *
 (w * w / (w + w + w) + w * w / (w + w + w) + w * w / (w + w + w) + - w))
with
(( w + w + w) * (w * w / (w + w + w)) + (w + w + w ) * (w* w / (w + w + w)) + (w + w + w)* (w* w / (w + w + w)) + (w + w  + w) * ( - w))
by ring. 


rewrite div_mod2.
setoid_replace (w * w + - (w * w %% w + w + w) + (w * w + - (w * w %% w + w + w)) +
 (w * w + - (w * w %% w + w + w)) + (w + w + w) * - w ) with
(- (w * w %% w + w + w) + - (w * w %% w + w + w) + - (w * w %% w + w + w))
by ring.
eapply le_trans.
apply abs_triang.
setoid_replace ((w + w + w) * (1 + 1 + 1)) with ((w + w + w) + (w + w + w) + (w + w + w)) by ring.
apply le_plus.
eapply le_trans.
apply abs_triang.
apply le_plus.
rewrite abs_minus;apply lt_le; apply div_mod3.
setoid_replace 0 with (0+0+0) by ring.
repeat apply lt_plus; apply Aw.
rewrite abs_minus;apply lt_le; apply div_mod3.
setoid_replace 0 with (0+0+0) by ring.
repeat apply lt_plus; apply Aw.
rewrite abs_minus;apply lt_le; apply div_mod3.
setoid_replace 0 with (0+0+0) by ring.
repeat apply lt_plus; apply Aw.
left; setoid_replace 0 with (0+0+0) by ring; repeat apply lt_plus; apply Aw.
apply lt_le; apply lim_lt_w.
split.
repeat apply ANS2a; assumption.
setoid_replace 0 with (0+0+0) by ring; repeat apply le_plus; apply lt_le; assumption.
Qed.

Lemma two_one_third : two_third [=] (one_third [+] one_third).
Proof.
unfold two_third, one_third, HRw2 ; ring.
Qed.

Lemma HRwminus_one_third : forall x, (x [+] -w (one_third [*] x)) [=](two_third [*] x).
Proof.
intros.
setoid_replace x with ((one_third [+] one_third [+] one_third)[*] x) at 1.
unfold two_third, one_third, HRw2; ring.
rewrite three_one_third; rewrite HRwmult_one; apply HRwequal_refl.
Qed.

Lemma lim_opp : forall n, lim n -> lim (-n).
Proof.
intros.
apply ANS4.
exists n.
split.
assumption.
rewrite abs_minus.
apply le_refl.
Qed.
(*
Lemma ANS3ter : forall n, 0<n -> lim n -> ~lim (n * w).
Proof.
intros.
intro.
apply ANS3.
apply ANS4.
exists (n * w).
split.
assumption.
rewrite abs_pos_val.
rewrite abs_pos_val.
apply le_plus_inv with (- w).
ring_simplify; unfold minusA.
setoid_replace (w * n + - w) with (w * (n + - a1)) by ring.
setoid_replace 0 with (w*0) by ring.
apply le_mult.
apply lt_le; apply Aw.
apply le_plus_inv with 1.
ring_simplify.
setoid_replace 1 with (0+1)  by ring.
apply lt_le_2; assumption.
setoid_replace 0 with (n*0) by ring.
apply le_mult.
apply lt_le; assumption.
apply lt_le; apply Aw.
apply lt_le; apply Aw.
Qed.
*)
Lemma lemma1 : forall n p u,  0 <n -> lim n -> 0<p -> lim p -> 0<u -> lim u -> n < p -> n * w <= p * w + - u.
Proof.
intros.
apply le_plus_inv with (- n * w).
apply le_plus_inv with u.
ring_simplify.
rewrite mult_comm.
rewrite <- mult_distr_r.
apply le_trans with w.
apply lt_le; apply lim_lt_w.
split; [assumption| apply lt_le; assumption].
setoid_replace w with (w*(0+1)) at 1 by ring.
apply le_mult.
apply lt_le; apply Aw.
apply lt_le_2.
apply lt_plus_inv with n.
ring_simplify.
assumption.
Qed.

Lemma rew_a1 : forall x, - x == (-a1)*x.
Proof.
intros; ring.
Qed.

Lemma two_third_prop : two_third [>] [0] /\ [1] [>] two_third.
Proof.
split.
pose (x:=(1+1)).
unfold HRwgt; unfold two_third.
simpl.
exists x.
repeat split.
unfold x; repeat (apply ANS2a || apply ANS2b); apply ANS1.
unfold x; setoid_replace 0 with (0+0) by ring; apply lt_plus; apply lt_0_1.
ring_simplify.
apply le_mult_inv with w.
apply Aw.
rewrite mult_assoc.
rewrite (mult_comm w x).
rewrite <- mult_assoc.
rewrite div_modw2.
apply le_mult_inv with (w + w + w).
setoid_replace 0 with (0+0+0) by ring.
repeat apply lt_plus; apply Aw.
setoid_replace ((w + w + w) * (x *
((w + w) * (w * w / (w + w + w)) + - ((w + w) * (w * w / (w + w + w)) %% w))))
with (x * (w + w) *
((w + w + w) * (w * w / (w + w + w))) + x*(w + w + w)* - ((w + w) * (w * w / (w + w + w)) %% w)) by ring.
rewrite div_mod2.
apply le_trans with (x * (w + w) * (w * w + (- a1)*(w + w + w)) +
x * (w + w + w) * ((-a1)* w)).
ring_simplify;unfold minusA.
setoid_replace ((1 + (1 + 1)) * w * w * w) with (w  * w * (1 + (1 + 1)) * w) by ring.
setoid_replace ((1 + 1) * w * w * w * x + - ((1 + (1 + 1) * ((1 + 1) * (1 + 1))) * w * w * x))
with (w* w * ((1 + 1) * w * x + - ((1 + (1 + 1) * ((1 + 1) * (1 + 1))) * x))) by ring.
rewrite <- mult_assoc.
apply le_mult.
setoid_replace 0 with (w*0) by ring.
apply le_mult;apply lt_le; apply Aw.
setoid_replace ((1+1) * w * x) with (((1+1) * x) * w) by ring.

apply lemma1.
setoid_replace 0 with (0+(0+0)) by ring; repeat apply lt_plus; apply lt_0_1.
repeat apply ANS2a; apply ANS1.
unfold x.
setoid_replace 0 with ((1+1)*(0+0)) by ring.
apply lt_mult.
setoid_replace 0 with (0+0) by ring; apply lt_plus; apply lt_0_1.
apply lt_plus; apply lt_0_1.
unfold x.
apply ANS2b ; repeat apply ANS2a; apply ANS1.
unfold x.
setoid_replace 0 with ((1 + (1 + 1) * ((1 + 1) * (1 + 1))) * (0 + 0)) by ring.
apply lt_mult.
setoid_replace 0 with (0+0) by ring.
apply lt_plus.
apply lt_0_1.
setoid_replace 0 with ((1 + 1) * 0) by ring.
apply lt_mult.
setoid_replace 0 with (0+0) by ring.
apply lt_plus; apply lt_0_1.
setoid_replace 0 with ((1+1)*0) by ring.
apply lt_mult;
setoid_replace 0 with (0+0) by ring; apply lt_plus; apply lt_0_1.
apply lt_plus; apply lt_0_1.
unfold x; repeat (apply ANS2a || apply ANS2b); apply ANS1.
unfold x.
rewrite mult_distr_l.
setoid_replace (1 * (1+1)) with (1+1) by ring.
rewrite plus_assoc.
apply le_lt_plus.
apply le_refl.
setoid_replace 1 with (1+0) by ring.
apply le_lt_plus; ring_simplify.
apply le_refl.
apply lt_0_1.
(**)
apply le_plus.
apply le_mult.
setoid_replace 0 with (x*(0+0)) by ring.
apply le_mult.
apply lt_le; unfold x.
setoid_replace 0 with (0+0) by ring. 
apply lt_plus; apply lt_0_1.
apply le_plus; apply lt_le; apply Aw.
apply le_plus.
apply le_refl.
setoid_replace ( - (w * w %% w + w + w)) with ((-a1)*(w * w %% w + w + w)) by ring.
apply le_mult_neg.
apply lt_m1_0.
apply lt_le; apply div_mod3a.
setoid_replace 0 with (0+0+0) by ring.
repeat apply lt_plus; apply Aw.
apply le_mult.
setoid_replace 0 with (x* (0+0+0)) by ring.
apply le_mult.
apply lt_le; unfold x.
setoid_replace 0 with (0+0) by ring.
apply lt_plus; apply lt_0_1.
repeat apply le_plus; apply lt_le; apply Aw.
setoid_replace (- ((w + w) * (w * w / (w + w + w)) %% w)) with
((-a1)* ((w + w) * (w * w / (w + w + w)) %% w)) by ring.
apply le_mult_neg.
apply lt_m1_0.
apply lt_le; apply div_mod3a.
apply Aw.

unfold two_third; simpl.
left; setoid_replace 0 with (0+0+0) by ring; repeat apply lt_plus; apply Aw.
pose (x:=(1+(1+1))).
exists x.
repeat split.
unfold x; repeat apply ANS2a; apply ANS1. 
unfold x; setoid_replace 0 with (0 + 0) by ring.
apply le_lt_plus.
apply lt_le; apply lt_0_1.
setoid_replace 0 with (0+0) by ring.
apply le_lt_plus.
apply lt_le; apply lt_0_1.
apply lt_0_1.
apply le_mult_inv with w.
apply Aw.
ring_simplify; unfold minusA.
setoid_replace (w * x * ((w + w) * (w * w / (w + w + w)) / w)) 
with (x * (w * ((w + w) * (w * w / (w + w + w)) / w))) by ring.
rewrite div_modw2.
apply le_mult_inv with (w + w + w).
setoid_replace 0 with (0+0+0) by ring; repeat apply lt_plus; apply Aw.
rewrite mult_distr_r.
setoid_replace ((w + w + w) *
-
(x *
 ((w + w) * (w * w / (w + w + w)) + - ((w + w) * (w * w / (w + w + w)) %% w))))
with
(-a1 *
(x *
 ((w + w) * ((w + w + w)* (w * w / (w + w + w))) + (w + w + w) * - ((w + w) * (w * w / (w + w + w)) %% w))))
by ring.
rewrite div_mod2.
apply le_trans with ((w + w + w) * (w * w * x) +
- (1) *
(x *
 ((w + w) * (w * w + 0 +
  (w + w + w) * - 0)))).
unfold x; ring_simplify; apply le_refl.
apply le_plus.
apply le_refl.
apply le_mult_neg.
apply lt_m1_0.
apply le_mult.
unfold x; setoid_replace 0 with (0 + (0 + 0)) by ring; repeat apply le_plus; apply lt_le; apply lt_0_1.
apply le_trans with ((w + w) * (w * w) +
(w + w + w) * - ((w + w) * 0)).
apply le_plus.
apply le_mult.
setoid_replace 0 with (0+0) by ring; apply le_plus; apply lt_le;apply Aw.
setoid_replace (w * w) with (w * w + (-a1)*0) by ring.
apply le_plus.
ring_simplify; apply le_refl.
setoid_replace (w * w + - (1) * 0) with (w* w) by ring.
setoid_replace (- (w * w %% w + w + w)) with (-a1 * (w * w %% w + w + w)) by ring.
apply le_mult_neg.
apply lt_m1_0.
apply div_mod3b.
setoid_replace 0 with (0+0+0) by ring.
repeat apply lt_plus; apply Aw.
apply le_mult.
setoid_replace 0 with (0+0+0) by ring; repeat apply le_plus; apply lt_le; apply Aw.
ring_simplify; unfold minusA.
rewrite rew_a1.
setoid_replace 0 with ((-a1)*0) by ring.
apply le_mult_neg.
apply lt_m1_0.
apply div_mod3b.
apply Aw.
ring_simplify.
apply le_refl.
left; setoid_replace 0 with (0+0+0) by ring; repeat apply lt_plus; apply Aw.
Qed.

Lemma HRw2_mult : forall x, [2] [*] x [=] x [+] x.
Proof.
unfold HRw2; intros; ring.
Qed.

(** HRwge **)
Definition HRwge (y x:HRw) := forall n, lim n /\ 0 < n ->
match y with exist _ yy Hyy =>
match x with exist _ xx Hxx =>
 n * (xx + - yy) <= w
end end.

Notation "a [>=] b" := (HRwge a b) (at level 80).

Lemma HRwge_prop : 
forall a b,  b [>=] a <-> (forall c, a [>] c -> b [>] c).
Proof.
intros a b.
split.
destruct a as [aa Haa]; destruct b as [bb Hbb]; unfold HRwge; simpl; clear Haa Hbb.
intros Hab c; destruct c as [cc Hcc]; unfold HRwgt, HRwge; simpl.
intros H'; destruct H' as [n (Hlim, (H2,H3))].
exists (n+n).
assert (Hlim2:lim (n+n)).
apply ANS2a; assumption.
assert (Hnn:0<n+n).
setoid_replace 0 with (0+0) by ring.
apply lt_plus; assumption.
split.
solve [intuition].
split.
solve [intuition].
generalize (Hab (n+n) (conj Hlim2 Hnn)).
intros H'.
generalize (Hab n (conj Hlim H2)).
intros H''.
setoid_replace w with ((-a1) * w + (w + w)) by ring.
setoid_replace (bb + - cc) with (bb + - aa + (aa + - cc)) by ring.
setoid_replace ((n+n) * (bb + - aa + (aa + - cc))) with ((- a1) * ((n+n) * (aa + - bb)) + (n+n) *(aa + - cc)) by ring.
apply le_plus.
apply le_mult_neg.
apply lt_m1_0.
apply H'.
setoid_replace  ((n + n) * (aa + - cc)) with (n*(aa + - cc) + n*(aa + - cc)) by ring.
apply le_plus; assumption.

intros Hyp.
unfold HRwge.
intros p (Hlimp,Hp0).
destruct a as [aa Haa].
destruct b as [bb Hbb].
pose (cp:= aa + - (w/p)).
assert (Hcp:P cp).
clear Hyp;unfold cp, P in *.
elim Haa.
intros n (Hlim,(Hn0,Hn)).
exists (n+1).
split.
apply ANS2a.
assumption.
apply ANS1.
split.
setoid_replace 0 with (0+0) by ring.
apply lt_plus.
assumption.
apply lt_0_1.
apply le_trans with (|aa|+ | - (w/p)|).
apply abs_triang.
apply le_mult_inv with p.
assumption.
rewrite (mult_distr_r p).
rewrite mult_distr_l.
rewrite (mult_distr_r p).
apply le_plus.
apply le_mult.
apply lt_le; assumption.
assumption.
rewrite <- (abs_pos_val p) at 1.
rewrite <- abs_prod.
setoid_replace (p* - (w/p)) with (- (p * (w/p))) by ring.
rewrite div_mod2.
ring_simplify.
rewrite abs_neg_val.
ring_simplify.
apply le_trans with w.
unfold minusA.
apply le_plus_inv with (w%%p).
ring_simplify.
setoid_replace w with (w+0) at 1 by ring.
apply le_plus.
apply le_refl.
apply div_mod3b.
assumption.
setoid_replace w with (w*(0+1)) at 1 by ring.
apply le_mult.
apply lt_le; apply Aw.
apply lt_le_2.
assumption.

apply le_plus_inv with w.
ring_simplify.
apply le_trans with p.
apply lt_le; apply div_mod3a.
assumption.
apply lt_le.
apply lim_lt_w.
split; [assumption|apply lt_le; assumption].
left; assumption.
apply lt_le; assumption.

assert (exist (fun x : A => P x) aa Haa [>]  exist (fun x:A => P x) cp Hcp).
unfold HRwgt; unfold cp; simpl.
exists (p+1).
split.
apply ANS2a.
assumption.
apply ANS1.
split.
setoid_replace 0 with (0+0) by ring.
apply lt_plus.
assumption.
apply lt_0_1.
setoid_replace (aa + - (aa + - (w / p))) with (w/p) by ring.
setoid_replace ((p+1)*(w/p)) with (p*(w/p) + (w/p)) by ring.
rewrite div_mod2.
rewrite <- plus_assoc.
setoid_replace w with (w+0) by ring.
apply le_plus.
ring_simplify;apply le_refl.
setoid_replace (w+0) with w by ring.
apply le_mult_inv with p.
assumption.
ring_simplify.
rewrite div_mod2.
apply le_plus_inv with (p* (w%%p) + (w%%p)).
ring_simplify.
apply lt_le.
apply lim_lt_w.
split.
apply ANS2a.
apply ANS2b.
assumption.
apply ANS4.
exists p.
split.
assumption.
rewrite (abs_pos_val p).
rewrite (abs_pos_val (w %% p)).
apply lt_le; apply div_mod3a.
assumption.
apply div_mod3b.
assumption.
apply lt_le; assumption.
apply ANS4.
exists p.
split.
assumption.
rewrite (abs_pos_val p).
rewrite (abs_pos_val (w %% p)).
apply lt_le; apply div_mod3a.
assumption.
apply div_mod3b.
assumption.
apply lt_le; assumption.
setoid_replace 0 with (p*0+0) by ring.
apply le_plus.
apply le_mult.
apply lt_le; assumption.
apply div_mod3b.
assumption.
apply div_mod3b.
assumption.
left; assumption.
left; assumption.
generalize (Hyp _ H); intros H'; unfold HRwgt,cp in H'; simpl.
elim H'.
intros m (Hm1, (Hm2, Hm3)).
assert (Hm3':m*(aa+ - bb) <= m*(w / p) + - w).
apply le_plus_inv with (- m * (aa + - bb)+ w).
ring_simplify.
setoid_replace ( - m * aa + m * bb + m * (w / p)) with (m * (bb + - (aa + - (w /p)))) by ring.
assumption.
apply le_mult_inv with m.
assumption.
assert (Hm3'': m * (p * (aa + - bb)) <= m * (p* (w / p)) + - (p * w)).
setoid_replace (m * (p * (aa + - bb))) with (p * (m * (aa + - bb))) by ring.
setoid_replace (m * (p * (w / p)) + - (p * w)) with (p * (m * (w / p) + - w)) by ring.
apply le_mult.
apply lt_le; assumption.
assumption.
rewrite div_mod2 in Hm3''.
apply le_trans with (m * (w + - (w %% p)) + - (p * w)).
assumption.
setoid_replace (m * (w + - (w %% p)) + - (p * w) ) with (m * w + (m * (- (w %% p)) + - (p * w))) by ring.
setoid_replace (m* w) with (m* w+(0+0)) by ring.
apply le_plus.
ring_simplify;apply le_refl.
apply le_plus.
apply le_plus_inv with (m * (w %% p)).
ring_simplify.
setoid_replace 0 with (m*0) by ring.
apply le_mult.
apply lt_le; assumption.
apply div_mod3b.
assumption.
apply le_plus_inv with (p * w).
ring_simplify.
setoid_replace 0 with (p* 0) by ring. 
apply le_mult.
apply lt_le; assumption.
apply lt_le; apply Aw.
left; assumption.
Qed.

Lemma HRwge_prop1 : (forall a b : HRw, a [>=] b -> forall c : HRw, b [>] c -> a [>] c).
Proof.
intros a b Hab; now apply HRwge_prop.
Qed.

Lemma HRwge_prop2 : (forall a b : HRw, (forall c : HRw, b [>] c -> a [>] c) -> a [>=] b).
Proof.
intros a b H; now apply HRwge_prop.
Qed.

Lemma HRwge_refl : forall x, x [>=] x.
Proof.
intros x; destruct x; simpl.
intros n (Hlim, H).
setoid_replace (n*(x + - x)) with 0 by ring.
apply lt_le; apply Aw.
Qed.


Lemma Zge_HRwge : forall x y:HRw, (proj1_sig x) <= (proj1_sig y) -> y [>=] x.
Proof.
intros x y; case x; intros xx Hxx; case y; intros yy Hyy.
unfold HRwge; simpl.
intros.
apply le_trans with (n*0).
apply le_mult.
apply lt_le; solve [intuition].
eapply le_plus_inv with yy.
ring_simplify.
assumption.
setoid_replace (n*0) with 0 by ring.
apply lt_le; apply Aw.
Qed.

Lemma HRwge_HRwopp : forall x y,  x [>=] y -> (HRwopp y) [>=] (HRwopp x).
Proof.
intros x y; destruct x as [xx Hx]; destruct y as [yy Hy]; unfold HRwge; simpl.
intros.
setoid_replace (- xx + - - yy) with (yy + - xx) by ring.
solve [intuition].
Qed.

Lemma HRwequal_prop :
forall (a b:HRw), a [=] b <-> (b [>=] a) /\ (a [>=] b).
Proof.
intros a b; unfold HRwequal, HRwge; destruct a; destruct b; simpl; split; [intros Hab | intros Hba].
split.
intros.
apply le_trans with (n * (|x + - x0 |)).
apply le_mult.
apply lt_le; now intuition.
setoid_replace (x + - x0) with (- (x0 + - x)) by ring.
apply abs_max.
now apply Hab.
intros.
apply le_trans with (n * (|x + - x0 |)).
apply le_mult.
apply lt_le; now intuition.
rewrite <- abs_minus.
setoid_replace (- (x + - x0)) with (x0 + - x) by ring.
apply abs_max.
now apply Hab.
intros.
destruct Hba as [H1 H2].
setoid_replace n with (|n|).
rewrite <- abs_prod.
apply abs_new.
apply H1; now split.
setoid_replace (- (n * (x + - x0))) with (n * (x0 + - x) ) by ring.
apply H2; now split.
rewrite abs_pos_val.
reflexivity.
apply lt_le; assumption.
Qed.

Lemma HRwdiff_prop :
forall a b, HRwdiff a b <-> (a [>] b) \/ (b [>] a).
Proof.
solve [intros; unfold HRwdiff; intuition].
Qed.

Lemma HRwgt_HRwge_trans : forall x y z,  x [>] y ->  y [>=] z ->  x [>] z.
Proof.
intros x y z; destruct x as [xx Hxx]; destruct y as [yy Hyy]; destruct z as [zz Hzz]; unfold HRwge,HRwgt; simpl.
intros HXY HYZ.
elim HXY.
intros n Hn.
exists (n+n).
split.
apply ANS2a; solve [intuition].
split.
setoid_replace 0 with (0+0) by ring; apply lt_plus; solve [intuition].
setoid_replace (xx + - zz) with (xx + - yy + yy + - zz) by ring.
setoid_replace ((n + n) * (xx + - yy + yy + - zz)) with ((n + n) * (xx + - yy) + (n+n)*(yy + - zz)) by ring.
setoid_replace w with ((w + w) + - w) by ring.
apply le_plus.
setoid_replace ((n + n) * (xx + - yy)) with (n * (xx + - yy) + n * (xx + - yy)) by ring.
apply le_plus; solve [intuition].
setoid_replace (- w) with ((-a1)* w) by ring.
setoid_replace ((n + n) * (yy + - zz))  with ((-a1)* ((n + n) * (zz + - yy))) by ring.
apply le_mult_neg.
apply lt_m1_0.
apply HYZ.
split.
apply ANS2a; solve [intuition].
setoid_replace 0 with (0+0) by ring.
apply lt_plus; solve [intuition].
Qed.

Lemma HRwgt_HRwge : forall X Y,  X [>] Y -> X [>=] Y.
Proof.
intros x y Hgt.
eapply HRwge_prop2.
intros.
eapply HRwgt_trans.
apply Hgt.
apply H.
Qed.

Lemma contradict_HRwgt_HRwge :  forall s x, s [>] x -> x [>=] s -> False.
Proof.
intros s x; destruct s; destruct x; unfold HRwgt, HRwge; simpl.
intros H1 H2.
elim H1; intros q (Hlimq, (Hq, H)).
assert (~(x0 + - x == a0)).
intro Heq; rewrite Heq in H; ring_simplify in H.
eapply contradict_lt_le with (s:=0) (x:=w).
apply Aw.
assumption.
assert (Hq1:(lim (q+1)/\(0< q+1))).
split.
apply ANS2a.
assumption.
apply ANS1.
setoid_replace 0 with (0+0) by ring.
apply le_lt_plus.
apply lt_le.
assumption.
apply lt_0_1.
generalize (H2 (q+1) Hq1); intros H3.
assert (x0 + - x ==0).
apply le_id.
setoid_replace 0 with (w + (- a1)* w) by ring.
setoid_replace (x0 + - x) with ((q + 1) * (x0 + - x) + - q * (x0 + - x)) by ring.
apply le_plus.
assumption.
apply le_plus_inv with (z:=q*(x0+ - x) + w).
setoid_replace (- q * (x0 + - x) + (q * (x0 + - x) + w)) with w by ring.
setoid_replace (- (1) * w + (q * (x0 + - x) + w)) with (q * (x0 + - x)) by ring.
assumption.
assert (0<= q*(x0+-x)).
apply le_trans with w.
apply lt_le; apply Aw.
assumption.
setoid_replace 0 with (q*0) in H4 by ring.
eapply le_mult_inv with q.
assumption.
assumption.
solve [intuition].
Qed.

Lemma HRwge_HRwplus_inv_l : forall a b c:HRw, c [+] a [>=] c [+] b ->  a [>=] b.
Proof.
intros a b c Hge.
apply HRwge_prop.
generalize (HRwge_prop1 (c[+] a) (c[+] b) Hge); intros Hge'.
intros d Hbd.
apply HRwgt_HRwplus_inv_l with c.
apply Hge'.
apply HRwgt_HRwplus_l.
assumption. 
Qed.

Lemma HRwge_HRwplus_inv_r : forall a b c:HRw, a [+] c [>=]  b[+] c ->  a [>=] b.
Proof.
intros a b c Hge.
apply HRwge_prop.
generalize (HRwge_prop1 (a[+] c) (b[+] c) Hge); intros Hge'.
intros d Hbd.
apply HRwgt_HRwplus_inv_r with c.
apply Hge'.
apply HRwgt_HRwplus_r.
assumption. 
Qed.

End mBridges.

(* Local Variables: *)
(* coq-prog-name: "/Users/magaud/.opam/4.05.0/bin/coqtop" *)
(* coq-load-path: ( ("." "Top") ) *)
(* suffixes: .v *)
(* End: *)