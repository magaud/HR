Require Export Bridges_order.

Module lub_spec (N:Num_w).

Import N.
Module Export XX:=mBridges(N).

(** LUB specifications *)
Definition subset := HRw->Prop.

Definition upper_bound (X:subset) (m:HRw) : Prop := forall x:HRw, X x -> m [>] x.

Definition bound_above  (X:subset) := exists m:HRw, upper_bound X m.

Definition non_empty (X:subset):= {x:HRw| X x}. (** actually implements the axiom of choice *)

Definition power (x:HRw) (n:A) : std n /\ 0<=n -> HRw.
intros Hn.
apply (nat_like_induction (fun _ => HRw)) with (n:=n).
exact [1].
intros k Hk xk.
apply (HRwmult xk x).
assumption.
Defined.

Parameter power_lim : forall x, x [>] [0] -> [1] [>] x -> forall a:HRw, a [>] [0] ->
  forall eps:HRw, eps [>] [0] -> 
  exists n:A, std n/\0 <=n /\ forall H:std n/\ 0 <= n, eps [>] (a[*] (power x n H)).
(*0<x<1 -> a >0 -> \forall eps, eps > 0, exists n, a [*] x^n < eps *)
(* one must choose an n such that n > ln (eps) / ln (x)  in order to show this property - may be adapted from Coq reals *)


(** Technical lemmas *) 

Lemma test1 : 
([2] [*] (HRwinv [3] lemma_HRw3)) [=] ((HRwinv [3] lemma_HRw3) [+] HRwinv [3] lemma_HRw3).
Proof.
intros; unfold HRw2; ring.
Qed.

Lemma test2 : forall a b, (HRwinv [3] lemma_HRw3 [*] b) [+] (([2] [*] HRwinv [3] lemma_HRw3) [*] a) [=]
((HRwinv [3] lemma_HRw3) [*] a)[+] (HRwinv [3] lemma_HRw3 [*] b) [+] (HRwinv [3] lemma_HRw3  [*] a).
intros; unfold HRw2; ring.
Qed.

Lemma HRwgt_one_third : one_third [>] [0].
Proof.
unfold HRwgt, one_third, HRw3, HRw2.
simpl.
exists (1+1+1+1+1+1).
split.
repeat apply ANS2a;apply ANS1.
split.
setoid_replace 0 with (0+0+0+0+0+0) by ring.
repeat apply lt_plus; apply lt_0_1.
setoid_replace (w * w / (w + w + w) + - 0) with (w * w / (w + w + w)) by ring.
apply le_mult_inv with (x:=w).
apply Aw.
setoid_replace  (w * ((1 + 1 + 1 + 1 + 1 + 1) * (w * w / (w + w + w))))
with ((1+1) * ((w+ w + w) * (w * w / (w + w + w)))) by ring.
rewrite div_mod2.
setoid_replace ((1 + 1) * (w * w + - (w * w %% w + w + w))) with ((1+1)* (w* w) + - (1+1)*(w* w %% (w+ w + w))) by ring.
apply le_trans with (w* w + (w * w + - (1+1)*(w+ w+ w))).
pattern (w* w) at 1; setoid_replace (w* w) with ((w* w) +0) by ring.
apply le_plus.
ring_simplify; apply le_refl.
setoid_replace (w * w + 0 + - (1 + 1) * (w + w + w)) with (w * (w + - (1+1+1+1+1+1))) by ring.
setoid_replace 0 with (w * 0) by ring.
apply le_mult.
apply lt_le; apply Aw.
apply le_plus_inv with (1+1+1+1+1+1).
ring_simplify.
apply lt_le; apply lim_lt_w.
split.
repeat( apply ANS2a || apply ANS2b); apply ANS1.
setoid_replace 0 with ((1+1)*(0+ (0+0))) by ring.
apply le_mult.
setoid_replace 0 with (0+0) by ring.
apply le_plus; apply lt_le; apply lt_0_1.
repeat apply le_plus; apply lt_le; apply lt_0_1.
setoid_replace ((1+1) * (w* w)) with (w * w + w* w) by ring.
rewrite plus_assoc.
apply le_plus.
apply le_refl.
apply le_mult_neg.
apply lt_plus_inv with (1+1).
ring_simplify.
setoid_replace 0 with (0+0) by ring.
apply lt_plus; apply lt_0_1.
apply lt_le.
apply div_mod3a.
setoid_replace 0 with (0+0+0) by ring.
repeat apply lt_plus; apply Aw.
left; setoid_replace 0 with (0+0+0) by ring; repeat apply lt_plus; apply Aw.
Qed.

Lemma HRwgt_morphism1 : 
  forall x y : HRw, x [=] y -> forall x0 y0 : HRw, x0 [=] y0 -> (x [>] x0 -> y [>] y0).
Proof.
intros x y Hxy t z Htz; 
  destruct x as [x Hx]; destruct y as [y Hy]; destruct z as [z Hz]; destruct t as [t Ht]; simpl.
unfold HRwequal in *.
intros.
destruct H as [n [Hlim [Hn0 Hn]]].
exists (n+n+n).
assert (H3lim : lim (n+n+n)).
repeat apply ANS2a; assumption.
assert (H3n:0<n+n+n).
setoid_replace 0 with (0+0+0) by ring.
repeat apply lt_plus; assumption.
split.
apply H3lim.
split.
apply H3n.
setoid_replace ((n+n+n)*(y+ -z)) with ((n+n+n)*(y + -x)+ n*(x + -t)+n*(x+ - t) +n*(x + - t) +(n+n+n)*(t + -z)) by ring.
apply le_trans with (oppA w + w + w + w + (oppA w)).
ring_simplify.
apply le_refl.
apply le_plus.
apply le_plus.
apply le_plus.
apply le_plus.
apply abs_new2.
rewrite abs_prod.
rewrite (abs_pos_val (n+n+n)) by (apply lt_le; apply H3n).
setoid_replace (y + - x) with (- (x + - y)) by ring. 
rewrite abs_minus.
apply Hxy.
apply H3lim.
apply H3n.
assumption.
assumption.
assumption.
apply abs_new2.
rewrite abs_prod.
rewrite (abs_pos_val (n+n+n)) by (apply lt_le; apply H3n).
apply Htz.
apply H3lim.
apply H3n.
Qed.

Instance HRwgt_morphism : Proper (HRwequal ==> HRwequal ==> Logic.iff) HRwgt.
Proof.
repeat red; split.
apply HRwgt_morphism1; assumption.
apply HRwgt_morphism1; symmetry; assumption.
Qed.

Lemma HRwge_morphism1 : 
  forall x y : HRw, x [=] y -> forall x0 y0 : HRw, x0 [=] y0 -> (x [>=] x0 -> y [>=] y0).
Proof.
intros.
generalize (HRwge_prop1 _  _ H1); intros.
apply HRwge_prop2.
intros.
setoid_rewrite <- H.
apply H2.
setoid_rewrite H0.
assumption.
Qed.

Instance HRwge_morphism : Proper (HRwequal ==> HRwequal ==> Logic.iff) HRwge.
repeat red.
intros; split.
apply HRwge_morphism1; assumption.
apply HRwge_morphism1; symmetry; assumption.
Qed.

Lemma R2_4' : forall X Y, X [>=] Y -> forall Z, X [+] Z [>=] Y [+] Z.
Proof.
intros x y Hxy z.
eapply HRwge_prop2.
generalize (HRwge_prop1 _ _ Hxy).
intros.

generalize (H (c [+] -w z)).
intros.

eapply HRwgt_HRwplus_inv_r with (-w z).
rewrite HRwplus_assoc.
rewrite HRwplus_opp.
rewrite HRwplus_comm.
rewrite HRwplus_zero.
apply H1.
eapply HRwgt_HRwplus_inv_r with (z).
rewrite HRwplus_assoc.
rewrite (HRwplus_comm (-w z) z).
rewrite HRwplus_opp.
rewrite (HRwplus_comm c [0]).
rewrite HRwplus_zero.
assumption.
Qed.

Lemma step_thirds : forall a b:HRw, a [>] b ->
((HRwinv [3] lemma_HRw3 [*] b) [+] (([2] [*] HRwinv [3] lemma_HRw3) [*] a)) [>]
((([2] [*] HRwinv [3] lemma_HRw3) [*] b) [+] (HRwinv [3] lemma_HRw3 [*] a)).
Proof. 
intros a b Hab.
apply HRwgt_HRwplus_inv_r 
  with (Z:= -w ((([2] [*] HRwinv [3] lemma_HRw3) [*] b) [+] (HRwinv [3] lemma_HRw3 [*] a))).
ring_simplify; unfold HRwminus.
setoid_replace (-w ((HRwinv [3] lemma_HRw3)[*] a)) with ((HRwinv [3] lemma_HRw3)[*] (-w a)) by ring.
setoid_replace (-w (HRwinv [3] lemma_HRw3)) with ((HRwinv [3] lemma_HRw3)[*] (-w [1])) by ring.
repeat rewrite HRwmult_assoc.
repeat rewrite <- HRw_distr.
setoid_replace (((-w [1]) [*] (b [*] [2])) [+] b) with (-w b) by (unfold HRw2; ring).
rewrite HRwplus_assoc.
setoid_replace (([2][*] a)[+] (-w a)) with a by (unfold HRw2;ring).
apply R2_5.
split.
apply HRwgt_one_third.
apply HRwgt_HRwplus_inv_l with b.
ring_simplify; assumption.
Qed.

Lemma two_thirds_one_third : forall x : HRw, x [=] ((two_third [*] x) [+] (one_third [*] x)).
Proof.
intros.
setoid_rewrite two_one_third.
setoid_rewrite HRwmult_comm.
setoid_rewrite <- HRw_distr.
setoid_rewrite three_one_third.
ring.
Qed.

Lemma HRw1_3 : forall a b , a [>] b -> 
((HRwinv [3] lemma_HRw3) [*] a) [>] ((HRwinv [3] lemma_HRw3) [*] b).
Proof.
intros a b Hab.
eapply HRwgt_HRwplus_inv_r with (-w (one_third [*] b)).
unfold one_third; ring_simplify; unfold HRwminus.
setoid_replace (-w (HRwinv [3] lemma_HRw3 [*] b)) with ((HRwinv [3] lemma_HRw3) [*] (-w b)) by ring.
rewrite <- HRw_distr.
apply R2_5.
split.
apply HRwgt_one_third.
apply HRwgt_HRwplus_inv_l with b.
ring_simplify; assumption.
Qed.

(** properties of power *)
Lemma power_0 : forall a, forall H0: std 0 /\ 0<= 0, (power a 0 H0) [=] [1]. 
Proof.
intros a H0.
unfold power.
rewrite nat_like_induction_r1.
reflexivity.
Qed.

Lemma power_n1 : forall a, forall n, forall Hn:std n /\ 0<=n, forall Hn1: std (n+1)/\ 0<= (n+1), 
  power a (n+1) Hn1 [=] power a n Hn [*] a.
Proof.
intros a n Hn Hn1.
unfold power at 1.
rewrite nat_like_induction_r2 with (H:=Hn).
unfold power.
reflexivity.
Qed.

Lemma HRwgt_HRwmult : forall a b c, a [>] [0] -> b [>] c -> (a [*] b) [>] (a[*] c).
Proof.
intros.
apply HRwgt_HRwplus_inv_r with (-w (a[*] c)).
setoid_replace (((a [*] c) [+] (-w (a [*] c)))) with [0] by ring.
setoid_replace ((a[*] b) [+] (-w (a [*] c))) with (a[*](b [+] -w c)) by ring.
apply R2_5.
split.
assumption.
apply HRwgt_HRwplus_inv_r with c.
ring_simplify.
assumption.
Qed.

Lemma power_HRwgt : forall a,  a [>] [0] -> forall n, forall H:(std n /\0<=n), power a n H [>] [0].
Proof.
intros a Ha n Hn.
apply (nat_like_induction (fun (x:A) => forall Hx: std x /\ 0<=x, power a x Hx [>] [0])).
intros; rewrite power_0.
exists 1.
split.
apply ANS1.
split.
apply lt_0_1.
ring_simplify.
apply le_refl.
intros.
rewrite power_n1 with (Hn:=H).
setoid_replace [0] with (a[*] [0]) by ring.
rewrite <- (HRwmult_comm a).
apply HRwgt_HRwmult.
assumption.
eapply H0.
apply Hn.
Qed.

Lemma lt_power_Sn_n : forall a, forall n, forall Hn:std n /\ 0<=n, forall Hn1: std (n+1)/\ 0<= (n+1),
  a [>] [0] -> [1] [>] a -> (power a n Hn) [>] (power a (n+1) Hn1). 
Proof.
intros.
rewrite power_n1 with (Hn:=Hn).
setoid_replace (power a n Hn) with ((power a n Hn)[*] [1]) at 1 by ring.
apply HRwgt_HRwmult.
apply power_HRwgt.
assumption.
assumption.
Qed.

End lub_spec.
