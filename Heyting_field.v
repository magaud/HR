Require Export HRw_spec.
Require Export HRwequal.

Module mHeyting (N:Num_w).

Import N.
Module Export KK := mHRwspec(N).

(** R1: HRw is a Bridges-Heyting ordered field *)
(* 1 *)
Lemma HRwplus_comm : forall x y, x [+] y [=] y [+] x.
Proof.
intros x; elim x.
intros x0 H0.
intros y; elim y.
intros.
simpl.
intros.
setoid_replace (x0 + x1 + - (x1 + x0)) with 0 by ring.
rewrite abs_pos_val.
setoid_replace (n*0) with 0 by ring.
apply lt_le; apply Aw.
apply le_refl.
Qed.

(* 2 *)
Lemma HRwplus_assoc : 
  forall x y z, (HRwplus (HRwplus x y) z) [=] (HRwplus x (HRwplus y z)).
Proof.
intros x; elim x.
intros xx Hxx.
intros y; elim y.
intros yy Hyy.
intros z; elim z.
intros zz Hzz.
simpl.
intros.
setoid_replace (xx + yy + zz + - (xx + (yy + zz))) with 0 by ring.
rewrite abs_pos_val.
setoid_replace (n*0) with 0 by ring.
apply lt_le; apply Aw.
apply le_refl.
Qed.

(* 3 *)
Lemma HRwplus_zero : forall x, HRwplus [0] x [=] x.
Proof.
intros x; elim x.
intros xx Hxx.
simpl.
intros.
setoid_replace (0 + xx + -xx) with 0 by ring.
rewrite abs_pos_val.
setoid_replace (n*0) with 0 by ring.
apply lt_le; apply Aw.
apply le_refl.
Qed.

(* 4 *)
Lemma HRwplus_opp : forall x, HRwplus x (HRwopp x) [=] [0].
Proof.
intros x; elim x.
intros xx Hxx.
simpl.
intros.
setoid_replace (xx + -xx + -0) with 0 by ring.
rewrite abs_pos_val.
setoid_replace (n*0) with 0 by ring.
apply lt_le; apply Aw.
apply le_refl.
Qed.

(* 5 *)
Lemma HRwmult_comm :  forall x y : HRw, x [*] y [=]  y [*] x.
Proof.
intros x ; elim x.
intros xx Hxx.
intros y ; elim y.
intros yy Hyy.
simpl.
intros.
elim Hyy; intros py (Hlimy, (H0y, Hy)).
elim Hxx; intros px (Hlimx, (H0x, Hx)).
(*apply le_trans with (n*(py + px + 1 + 1)).*)
apply le_mult_inv with w.
apply Aw.
setoid_replace n with (|n|) 
 by (rewrite abs_pos_val; [reflexivity| apply lt_le; assumption]).
setoid_replace w with (|w|) at 1
 by (rewrite abs_pos_val; [reflexivity| apply lt_le; apply Aw]).
repeat rewrite <- (abs_prod ).
setoid_replace (w * (n * (xx * yy / w + - (yy * xx / w)))) with 
(n*(w* (xx*yy/w) + - (w*(yy*xx/w)))) by ring.
rewrite div_modw2.
rewrite div_modw2.
rewrite (mult_comm xx).
setoid_replace (n * (yy * xx + - (yy * xx %% w) + - (yy * xx + - (yy * xx %% w))) ) with 0 by ring.
rewrite abs_pos_val.
setoid_replace 0 with (w*0) by ring.
apply le_mult; apply lt_le; apply Aw.
apply le_refl.
Qed.

(* 6 *)

Lemma abs_triang4 : forall a b c d, forall va vb vc vd, |a|<=va -> |b|<=vb-> |c|<=vc-> |d|<=vd -> |a+b+c+d|<= va+vb+vc+vd.
Proof.
intros.
eapply le_trans.
apply abs_triang.
apply le_plus.
eapply le_trans.
apply abs_triang.
apply le_plus.
eapply le_trans.
apply abs_triang.
apply le_plus.
assumption.
assumption.
assumption.
assumption.
Qed.

Lemma HRwmult_assoc : forall x y z : HRw, HRwmult (HRwmult x y) z [=] HRwmult x (HRwmult y z).
Proof.
intros x; elim x.
intros xx Hxx.
intros y; elim y.
intros yy Hyy.
intros z; elim z.
intros zz Hzz.
simpl.
intros.
elim Hzz; intros pz (Hlimz, (H0z, Hz)).
elim Hxx; intros px (Hlimx, (H0x, Hx)).
apply le_trans with (n*(pz + px + 1 + 1)).
apply le_mult.
apply lt_le; assumption.
apply le_mult_inv with (w* w).
setoid_replace 0 with (w*0) by ring.
apply lt_mult; apply Aw.
setoid_replace (w * w * (pz + px + 1 + 1)) with (w * (w * pz) + w * w +  w * (w * px) + w * w) by ring.
apply le_trans with (|zz| * w + w * w + |xx| * w + w * w).
setoid_replace (w * w * (|xx * yy / w * zz / w + - (xx * (yy * zz / w) / w) |)) with
(|w * w * (xx * yy / w * zz / w + - (xx * (yy * zz / w) / w) ) |).
rewrite mult_distr_r.
rewrite <- mult_assoc.
rewrite (div_modw2 (xx * yy / w * zz)).
setoid_replace (w * w * - (xx * (yy * zz / w) / w)) with ( - (w * w * (xx * (yy * zz / w) / w))) by ring.
rewrite <- mult_assoc.
rewrite (div_modw2 (xx * (yy * zz / w))).
repeat rewrite mult_distr_r.

rewrite mult_assoc.
rewrite div_modw2.
rewrite mult_distr_l.
setoid_replace (w * (xx * (yy * zz / w))) with (xx * (w * (yy * zz / w))) by ring.
rewrite div_modw2.
rewrite mult_distr_r.
rewrite mult_assoc.
setoid_replace (xx * yy * zz + - (xx * yy %% w) * zz + w * - (xx * yy / w * zz %% w) +
 - (xx * yy * zz + xx * - (yy * zz %% w) + w * - (xx * (yy * zz / w) %% w)))
with
( - (xx * yy %% w) * zz + w * - (xx * yy / w * zz %% w) + xx * (yy * zz %% w) + w * (xx * (yy * zz / w) %% w))
by ring.

repeat rewrite plus_assoc.
apply abs_triang4.
rewrite abs_prod.
rewrite <- (mult_comm (|zz|)).
apply le_mult.
apply abs_pos.
rewrite abs_minus.
apply lt_le; apply div_modw3.
rewrite abs_prod.
rewrite (abs_pos_val w).
apply le_mult.
apply lt_le; apply Aw.
rewrite abs_minus.
apply lt_le; apply div_modw3.
apply lt_le; apply Aw.
rewrite abs_prod.
apply le_mult.
apply abs_pos.
apply lt_le; apply div_modw3.
rewrite abs_prod.
rewrite (abs_pos_val w).
apply le_mult.
apply lt_le; apply Aw.
apply lt_le; apply div_modw3.
apply lt_le; apply Aw.

repeat rewrite abs_prod.
rewrite (abs_pos_val w).
reflexivity.
apply lt_le; apply Aw.
repeat rewrite plus_assoc.
apply le_plus.
apply le_plus.
apply le_plus.
setoid_replace ((|zz |) * w ) with (w * |zz|) by ring.
apply le_mult.
apply lt_le; apply Aw.
setoid_replace (w * pz) with (pz * w) by ring.
assumption.
apply le_mult.
apply lt_le; apply Aw.
apply le_refl.
setoid_replace ((|xx |) * w ) with (w * |xx|) by ring.
apply le_mult.
apply lt_le; apply Aw.
setoid_replace (w * px) with (px * w) by ring.
assumption.
apply le_mult.
apply lt_le; apply Aw.
apply le_refl.
apply lt_le; apply lim_lt_w.
split.
apply ANS2b.
assumption.
apply ANS2a.
apply ANS2a.
apply ANS2a; assumption.
apply ANS1.
apply ANS1.
setoid_replace 0 with (n*0) by ring.
apply le_mult.
apply lt_le; assumption.
setoid_replace 0 with (0+0+0+0) by ring.
apply le_plus.
apply le_plus.
apply le_plus.
apply lt_le; assumption.
apply lt_le; assumption.
apply lt_le;apply lt_0_1.
apply lt_le;apply lt_0_1.
Qed.

(* 7 *)

Lemma HRwmult_one : forall x, [1] [*] x [=] x.
Proof.
intros x ; elim x.
intros xx Hxx.
simpl.
intros.
setoid_replace ((w*xx)) with ((xx* w)) by ring.
rewrite div_idg.
setoid_replace (xx + - xx) with 0 by ring.
rewrite abs_pos_val.
ring_simplify.
apply lt_le; apply Aw.
apply le_refl.
apply Aw.
Qed.

(* 8 *)

Lemma HRwmult_inv : forall x, forall H: HRwdiff x [0], 
  x [*] (HRwinv x H) [=] [1]. 
Proof.
intros x; elim x.
intros xx Hxx.
intros H.
unfold HRwequal.
simpl.
intros.
elim Hxx; intros p (Hlimp, (H0p, Hp)).
apply le_trans with (n * (p+1)).
apply le_mult.
apply lt_le; assumption.
apply le_mult_inv with w.
apply Aw.
setoid_replace (w * (|xx * (w * w / xx) / w + - w |)) with (| w * (xx * (w * w / xx) / w + - w )|).
setoid_replace (w* (p+1)) with (p* w + w) by ring.
rewrite (div_mod2 xx (w* w)).
rewrite mult_distr_r.
rewrite (div_modw2 (w * w + - (w * w %% xx))).
setoid_replace (w * w + - (w * w %% xx) + - (w * w + - (w * w %% xx) %% w) + w * - w) with (- (w * w %% xx) + - (w * w + - (w * w %% xx) %% w)) by ring.
eapply le_trans.
apply abs_triang.
rewrite abs_minus.
rewrite abs_minus.
apply le_plus.
apply le_trans with (|xx|).
apply div_mod3_abs.
apply (HRwdiff0_diff0_spec_or xx Hxx); assumption.
assumption.

apply lt_le; apply div_modw3.
apply (HRwdiff0_diff0_spec_or xx Hxx); assumption.
rewrite abs_prod.
rewrite (abs_pos_val w).
reflexivity.
apply lt_le; apply Aw.
apply lt_le; apply lim_lt_w.
split.
apply ANS2b.
assumption.
apply ANS2a.
assumption.
apply ANS1.
setoid_replace 0 with (n*0) by ring.
apply le_mult.
apply lt_le.
assumption.
apply lt_le.
apply lt_le_trans with p.
assumption.
setoid_replace p with (p+0) at 1 by ring.
apply le_plus.
apply le_refl.
apply lt_le;apply lt_0_1.
Qed.

(* 9 *)

Lemma HRw_distr : forall x y z, x [*] (y [+] z) [=] (x [*] y) [+] (x [*] z).
Proof.
intros x; elim x.
intros xx Hxx.
intros y; elim y.
intros yy Hyy.
intros z; elim z.
intros zz Hzz.
simpl.
intros.
apply le_trans with (n* (1+1+1)).
apply le_mult.
apply lt_le; assumption.
apply le_mult_inv with w.
apply Aw.
setoid_replace (w * (1+1+1)) with (w + w + w) by ring.
setoid_replace 
(w * (|xx * (yy + zz) / w + - (xx * yy / w + xx * zz / w) |))
with
(| w* (xx * (yy + zz) / w + - (xx * yy / w + xx * zz / w)) |).
rewrite mult_distr_r.
setoid_replace (w * - (xx * yy / w + xx * zz / w)) with
(- (w * (xx * yy / w)) + - (w * (xx * zz / w))) by ring.
rewrite div_modw2.
rewrite div_modw2.
rewrite div_modw2.
setoid_replace (xx * (yy + zz) + - (xx * (yy + zz) %% w) +
 (- (xx * yy + - (xx * yy %% w)) + - (xx * zz + - (xx * zz %% w))))
with
(- (xx * (yy + zz) %% w) +
 (xx * yy %% w) + (xx * zz %% w))
by ring.
eapply le_trans.
apply abs_triang.
apply le_plus.
eapply le_trans.
apply abs_triang.
apply le_plus.
rewrite abs_minus.
apply lt_le; apply div_modw3.
apply lt_le; apply div_modw3.
apply lt_le; apply div_modw3.

rewrite abs_prod.
rewrite (abs_pos_val w).
reflexivity.
apply lt_le; apply Aw.

apply lt_le; apply lim_lt_w.
split.
apply ANS2b.
assumption.
apply ANS2a.
apply ANS2a; apply ANS1.
apply ANS1.
setoid_replace 0 with (n*0) by ring.
apply le_mult.
apply lt_le; assumption.
setoid_replace 0 with (0+0+0) by ring.
apply le_plus.
apply le_plus.
apply lt_le; apply lt_0_1.
apply lt_le; apply lt_0_1.
apply lt_le; apply lt_0_1.
Qed.

(* HRwequal and its compatibility properties *)

Instance HRwequal_equiv : Equivalence HRwequal.
Proof.
split; red; [apply HRwequal_refl | apply HRwequal_sym | apply HRwequal_trans ].
Qed.

Instance HRwplus_morphism : Proper (HRwequal ==> HRwequal ==> HRwequal) HRwplus.
Proof.
red;red.
unfold HRwequal.
intros x y; case x; intros xx Hxx; case y; intros yy Hyy.
intros  H x0 y0; case x0; intros xx0 Hxx0; case y0; intros yy0 Hyy0 H'.
simpl.
intros.
apply le_mult_inv with (a1+a1).
setoid_replace 0 with (0+0) by ring.
apply lt_plus; apply lt_0_1.
rewrite mult_assoc.
apply le_trans with ((1+1)*n*(|xx+ -yy| + |xx0 + (- yy0) |)).
apply le_mult.
setoid_replace 0 with (0+0) by ring.
setoid_replace ((1+1)*n) with (n+n) by ring.
apply le_plus; apply lt_le; assumption.
setoid_replace (xx + xx0 + - (yy + yy0)) with ((xx + -yy) + (xx0 + -yy0)) by ring.
apply abs_triang.
ring_simplify.
setoid_replace  ((1 + 1) * w) with (w + w) by ring.
apply le_plus.
apply H.
apply ANS2b.
apply ANS2a; apply ANS1.
assumption.
setoid_replace 0 with (0+0) by ring.
setoid_replace ((1+1)*n) with (n+n) by ring.
apply lt_plus; assumption.
apply H'.
apply ANS2b.
apply ANS2a; apply ANS1.
assumption.
setoid_replace 0 with (0+0) by ring.
setoid_replace ((1+1)*n) with (n+n) by ring.
apply lt_plus; assumption.
Qed.

Add Morphism HRwopp with 
signature (HRwequal ==> HRwequal) as HRwopp_mor.
Proof.
unfold HRwequal.
intros x y; case x; intros xx Hxx; case y; intros yy Hyy H.
simpl.
intros.
setoid_replace (- xx + - - yy) with (oppA (xx + - yy)) by ring.
rewrite abs_minus.
apply H; assumption.
Qed.

Lemma abs_triang2 : forall x a b, 0<x -> (x * |a+b|) <=(x * |a|)+(x * |b|).
Proof.
intros.
rewrite <- (abs_pos_val x).
do 3 rewrite <- abs_prod.
rewrite mult_distr_r.
apply abs_triang.
apply lt_le; assumption.
Qed.

Instance HRwmult_morphism : Proper (HRwequal ==> HRwequal ==> HRwequal) HRwmult.
Proof.
(* forall x y : HRw, x =w y -> forall x0 y0 : HRw, x0 =w y0 -> x [*] x0 =w y [*] y0 *)
unfold HRwequal.
intros a b; case a; intros aa Haa; case b; intros bb Hbb Hab.
intros c d; case c; intros cc Hcc; case d; intros dd Hdd Hcd.
simpl.
unfold P in Hcc.
elim Hcc; intros kc (Hlimc, (Hltc, Hc)).
elim Hbb; intros kb (Hlimb, (Hltb, Hb)).

intros m Hlimm Hltm.

assert (Hn: forall n:A, lim n -> 0 < n ->  n * (|aa*cc/w + - (bb * dd / w) |) <= (kc+kb+a1+a1) * w).
intros n Hlimn Hltn.
unfold P in Hcc.
apply le_mult_inv with w.
apply Aw.
setoid_replace (w * (n * (|aa * cc / w + - (bb * dd / w) |))) with
(n * (|w*( (aa * cc) / w )+ (-a1)* (w * ((bb * dd) / w)) |)).
rewrite div_modw2.
rewrite div_modw2.
setoid_replace (aa * cc + - (aa * cc %% w) + - (1) * (bb * dd + - (bb * dd %% w)) ) 
with  (aa * cc + - bb * dd + (- (aa * cc %% w) + (bb * dd %% w)) )  by ring.
eapply le_trans.
apply abs_triang2.
assumption.
setoid_replace (aa *cc + - bb * dd) with ((aa + - bb) *cc + (cc + - dd)*bb) by ring.
eapply le_trans with (((n * |(aa + - bb) * cc| )+ n*|(cc + - dd) * bb |) +
n * (| - (aa * cc %% w) + (bb * dd %% w) |)) .
apply le_plus.
apply abs_triang2.
assumption.
apply le_refl.
setoid_replace (w*((kc+kb+1+1)* w)) with ((kc* w * w) + (kb* w * w) + (w* w) + (w* w)) by ring.
repeat rewrite <- plus_assoc.
repeat apply le_plus.
rewrite abs_prod.
setoid_replace (n * ((|aa + - bb |) * (|cc |))) with (((n * |aa + - bb |) * ( |cc |))) by ring.
setoid_replace (kc * w * w) with (w * (kc * w)) by ring.
apply le_mult_general.
setoid_replace 0 with (n*0) by ring.
apply le_mult.
apply lt_le; assumption.
apply abs_pos.
apply Hab; assumption.
apply abs_pos.
assumption.
rewrite abs_prod.
rewrite mult_assoc.
setoid_replace (kb * w * w) with (w * (kb * w)) by ring.
apply le_mult_general.
setoid_replace 0 with (n*0) by ring.
apply le_mult.
apply lt_le; assumption.
apply abs_pos.
apply Hcd; assumption.
apply abs_pos.
assumption.
eapply le_trans.
apply abs_triang2.
assumption.
apply le_plus.
apply le_trans with (n * w).
apply le_mult.
apply lt_le; assumption.
rewrite abs_minus.
apply lt_le; apply div_modw3.
rewrite mult_comm.
apply le_mult.
apply lt_le; apply Aw.
apply lt_le; apply lim_lt_w; [split ; [assumption | apply lt_le; assumption]].
apply le_trans with (n * w).
apply le_mult.
apply lt_le; assumption.
apply lt_le; apply div_modw3.
rewrite mult_comm.
apply le_mult.
apply lt_le; apply Aw.
apply lt_le; apply lim_lt_w; [split ; [assumption | apply lt_le; assumption]].

rewrite <- (abs_pos_val n).
do 2 rewrite <- abs_prod.
setoid_replace (w * (|n * (aa * cc / w + - (bb * dd / w)) |)) with (|w| * (|n * (aa * cc / w + - (bb * dd / w)) |)) 
 by (rewrite (abs_pos_val w); [reflexivity | apply lt_le; apply Aw]).
rewrite <- abs_prod.
setoid_replace (w * (n * (aa * cc / w + - (bb * dd / w)))) 
with (n * (w * (aa * cc / w) + - (1) * (w * (bb * dd / w))))
by ring.
reflexivity.
apply lt_le; assumption.

apply le_mult_inv with (kc+kb+1+1).
setoid_replace 0 with (0+0+0+0) by ring.
repeat apply lt_plus; solve [assumption | apply lt_0_1].
rewrite mult_assoc.
apply Hn.
apply ANS2b.
repeat apply ANS2a; solve [assumption | apply ANS1].
assumption.
rewrite mult_comm.
setoid_replace 0 with (m*0) by ring.
apply lt_mult.
assumption.
setoid_replace 0 with (0+0+0+0) by ring.
repeat apply lt_plus; solve [assumption | apply lt_0_1]. 
Qed.

(** HRw and its usual operations has a ring structure *)

Lemma HRwth : (@ring_theory HRw [0] [1] HRwplus HRwmult HRwminus HRwopp HRwequal).
Proof.
constructor. 
apply HRwplus_zero.
apply HRwplus_comm.
symmetry; apply HRwplus_assoc.
apply HRwmult_one.
apply HRwmult_comm.
intros;apply HRwequal_sym;apply HRwmult_assoc.
intros; rewrite (HRwmult_comm (x [+] y) z); 
rewrite (HRwmult_comm x z); rewrite (HRwmult_comm y z); apply HRw_distr.
unfold HRwminus; intros;apply HRwequal_refl.
apply HRwplus_opp.
Qed.

Add Ring HRw_ring : HRwth.

End mHeyting.