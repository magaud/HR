Require Export HRwgt.
Require Export Setoid.

Module mHRwspec (N:Num_w).

Import N.
Module Export GG := mHRwgt(N).

Lemma Padd : forall x y, P x -> P y -> P (x + y).
unfold P; intros x y Hx Hy.
elim Hx; intros nx Hnx.
elim Hy; intros ny Hny.
exists (nx+ny).
split.
eapply ANS2a.
intuition.
intuition.
split.
setoid_replace 0 with (0+0) by ring; apply lt_plus; solve [intuition].
eapply le_trans.
eapply abs_triang.
rewrite mult_comm.
setoid_replace (w * (nx+ny) ) with (w*nx + w*ny) by ring.
apply le_plus.
rewrite mult_comm.
intuition.
rewrite mult_comm.
intuition.
Qed.

Definition HRwplus (x y: HRw) : HRw := 
match x with exist _ xx Hxx =>
match y with exist _ yy Hyy => 
exist P (xx + yy) (Padd xx yy Hxx Hyy)
end end.

(* using the property that 0=1-1 and ANSx axioms *)
Lemma lim0 : lim 0.
Proof.
intros.
setoid_replace 0 with (plusA 1 (oppA 1)) by ring.
apply ANS2a.
apply ANS1.
apply ANS4.
exists 1.
split.
apply ANS1.
rewrite abs_neg_val.
setoid_replace (- - (1)) with 1 by ring.
rewrite abs_pos_val.
apply le_refl.
apply lt_le.
apply lt_0_1.
apply le_plus_inv with (z:=1).
setoid_replace (- (1) + 1) with 0 by ring.
setoid_replace (0+1) with 1 by ring.
apply lt_le.
apply lt_0_1.
Qed.

Lemma Popp : forall x, P x -> P (- x).
Proof.
unfold P; intros x Hx.
elim Hx; clear Hx; intros nx (Hlimx, (Hle0nx, Hnxw)).
exists nx.
split.
solve [auto].
split.
solve [auto].
apply le_trans with (|x|).
rewrite abs_minus.
apply le_refl.
assumption.
Qed.

Definition HRwopp (x: HRw) : HRw :=
match x with exist _ xx Hxx =>
exist P (- xx) (Popp xx Hxx)
end. 

Definition HRwminus (x y : HRw) : HRw := HRwplus x (HRwopp y).

Lemma Pprod : forall x y, P x -> P y -> P (( x * y) / w).
Proof.
unfold P; intros x y Hx Hy.
elim Hx; intros nx Hnx.
elim Hy; intros ny Hny.
exists (nx * (ny+1)).
split.
apply ANS2b.
intuition.
apply ANS2a; solve [intuition| apply ANS1].
split.
apply mult_pos.
solve [intuition].
setoid_replace 0 with (0+0) by ring.
apply lt_plus.
solve [intuition].
apply lt_0_1.
rewrite <- (div_idg ( nx * (ny+1) * w) w).
(* branches here *)
apply le_mult_inv with w.
apply Aw.
rewrite <- (abs_pos_val w) at 1.
rewrite <- abs_prod.
rewrite div_mod2.
rewrite div_idg.
apply le_trans with (|x * y| + | - (x * y %% w) |).
apply abs_triang.
setoid_replace (w* (nx * (ny+1) * w)) with ((w* (nx * ny * w))+w*w*nx) by ring.
apply le_plus.
setoid_replace (w * (nx * ny * w)) with ((nx*w)*(ny*w)) by ring.
rewrite abs_prod.
apply mult_le.
apply abs_pos.
intuition.
apply abs_pos.
intuition.

apply le_trans with w.
rewrite abs_minus.
apply lt_le; apply div_mod3.
apply Aw.
setoid_replace w with (w*1) at 1 by ring.
rewrite <- mult_assoc.
apply le_mult.
apply lt_le; apply Aw.
setoid_replace 1 with (0+1) by ring.
apply lt_le_2.
apply mult_pos.
apply Aw.
solve [intuition].
apply Aw.
left; apply Aw.
apply lt_le; apply Aw.
apply Aw.
Qed.

Definition HRwmult (x y: HRw) : HRw := 
match x with exist _ xx Hxx =>
match y with exist _ yy Hyy => 
exist P ((xx * yy) / w) (Pprod xx yy Hxx Hyy)
end end.

Definition HRwdiff (x y : HRw) : Prop := x [>] y \/ y [>] x.

Lemma HRwdiff0_diff0_spec_or : forall a : A, forall Ha : P a, 
  HRwdiff (exist (fun x : A => P x) a Ha) HRw0 ->  0<a\/a<0.
Proof.
intros; unfold HRwdiff in H; destruct H.
unfold HRw0, HRwgt in H.
left.
destruct H.
destruct H as [H1 [H2 H3]].
ring_simplify in H3.
apply lt_mult_inv with x.
assumption.
apply lt_le_trans with w.
ring_simplify.
apply Aw.
assumption.
right.
unfold HRw0, HRwgt in H.
destruct H.
destruct H as [H1 [H2 H3]].
ring_simplify in H3.
apply lt_mult_inv2 with (-x).
apply lt_plus_inv with x.
ring_simplify.
assumption.
apply lt_le_trans with w.
ring_simplify.
apply Aw.
assumption.
Qed.

Lemma HRwdiff0_diff0_spec2 : forall x, (exists n:A, lim n /\ 0 < n /\  w <= n*|x|) ->  |x|<>0.
Proof.
intros.
elim H.
intros n (Hlim,(Hlt,Hw)).
intro.
rewrite H0 in *.
eapply (le_lt_False w).
rewrite mult_absorb in *.
eassumption.
apply Aw.
Qed.

Lemma HRwdiff0_diff0_spec : forall x, (exists n:A, lim n /\ 0 < n /\  w <= n*|x|) ->  ~(|x|==0).
Proof.
intros.
elim H.
intros n (Hlim,(Hlt,Hw)).
intro.
rewrite H0 in *.
eapply (le_lt_False w).
rewrite mult_absorb in *.
eassumption.
apply Aw.
Qed.

Lemma Pdiv : forall x ,  HRwdiff x HRw0 -> P ((w * w ) /(proj1_sig x)).
Proof.
intros z Hz.
set (x:=(proj1_sig z)).
assert (Hx:(exists n:A, lim n /\ 0 < n /\  w <= n*|x|)).
unfold x; clear x.
revert Hz; case z.
intros xx Hxx H_HRwdiff.
elim H_HRwdiff.
simpl.
intros.
elim H; intros x (Hlim, (Hlt, Hw)).
setoid_replace (xx + -0) with xx in Hw by ring.
exists x; intuition.
assert (Habs:|xx|==xx).
apply abs_pos_val.
assert (0 <= x* xx).
apply le_trans with (y:=w).
apply lt_le; apply Aw.
assumption.
apply le_mult_inv with (x:=x).
assumption.
setoid_replace (x*0) with 0 by ring.
assumption.
rewrite Habs.
assumption.
simpl.
intros.
elim H; intros x (Hlim, (Hlt, Hw)).
rewrite plus_neutral in Hw.
exists x; intuition.

assert (Habs:|xx|==-xx).
apply abs_neg_val.
assert (0 <= x* -xx).
apply le_trans with (y:=w).
apply lt_le; apply Aw.
assumption.
apply le_mult_inv with (x:=x).
assumption.
setoid_replace (x*0) with 0 by ring.
apply le_plus_inv with (z:=x* -xx).
setoid_replace (x * xx + x * - xx) with 0 by ring.
setoid_replace (0 + x * - xx) with (x* -xx) by ring.
assumption.
rewrite Habs.
assumption.

destruct z; simpl in *; subst x.
unfold P.
assert (0<x0\/x0<0).
apply (HRwdiff0_diff0_spec_or x0 p Hz).
destruct H.

elim Hx; intros n Hn.
exists (n+1).
split.
apply ANS2a; solve [intuition | apply ANS1].
split.
setoid_replace 0 with (0+0) by ring; apply lt_plus; solve [intuition | apply lt_0_1].
apply le_mult_inv with x0.
assumption.
rewrite <- (abs_pos_val x0) at 1.
rewrite <- abs_prod.
rewrite div_mod2.
apply le_trans with (| w * w| + | - (w* w %% x0)|).
apply abs_triang.
rewrite (abs_pos_val x0) in Hn.
setoid_replace (x0 * ((n +1) * w)) with (x0 * (n * w) + x0* w) by ring.
apply le_plus.
rewrite abs_prod.
rewrite abs_pos_val.
setoid_replace (x0*(n*w)) with (w * (n*x0)) by ring.
apply le_mult.
apply lt_le; apply Aw.
solve [intuition].
apply lt_le; apply Aw.
apply le_trans with x0.
rewrite abs_minus.
apply lt_le; apply div_mod3.
assumption.
setoid_replace x0 with (x0*1) at 1 by ring.
apply le_mult.
apply lt_le; assumption.
setoid_replace 1 with (0+1) by ring.
apply lt_le_2.
apply Aw.
apply lt_le; assumption.
left; assumption.
apply lt_le; assumption.

elim Hx; intros n Hn.
exists (n+1).
split.
apply ANS2a; solve [intuition | apply ANS1].
split.
setoid_replace 0 with (0+0) by ring; apply lt_plus; solve [intuition | apply lt_0_1].
rewrite abs_neg_val in Hn.
apply le_mult_inv2 with x0.
assumption.
setoid_replace (x0 * (|w * w / x0 |)) with (- ((-x0) * (|w * w / x0 |))) by ring.
rewrite <- (abs_neg_val x0) at 1.
rewrite <- (abs_prod x0).
rewrite div_mod2.
apply le_plus_inv with ((|w * w + - (w * w %% x0) |) + - x0 * ((n + 1) * w)).
ring_simplify; unfold minusA.
apply le_trans with (| w * w| + | - (w* w %% x0)|).
apply abs_triang.
apply le_plus.
rewrite abs_prod.
rewrite abs_pos_val.
setoid_replace (- x0*n*w) with (w * (n* - x0)) by ring.
apply le_mult.
apply lt_le; apply Aw.
solve [intuition].
apply lt_le; apply Aw.
apply le_trans with (-x0).
rewrite abs_minus.
apply le_trans with (|x0|).
apply div_mod3_abs.
right; assumption.
rewrite abs_neg_val.
apply le_refl.
apply lt_le; assumption.
setoid_replace (-x0) with ((-x0)*1) by ring.
setoid_replace (- (x0* w)) with (-x0 * w) by ring.
apply le_mult.
apply le_plus_inv with x0; ring_simplify; apply lt_le; assumption.
setoid_replace 1 with (0+1) by ring.
apply lt_le_2.
apply Aw.
right; assumption.
apply lt_le; assumption.
apply lt_le; assumption.
Qed.

Definition HRwinv (x : HRw) (H: HRwdiff x HRw0) : HRw := 
exist P ((w * w ) / (proj1_sig x)) (Pdiv x H).

Notation "x [+] y " := (HRwplus  x y) (at level 40).
Notation "x [*] y " := (HRwmult  x y)(at level 35).

Notation "[0]" := HRw0.
Notation "[1]" := HRw1.

Notation "-w x" := (HRwopp x) (at level 30).
Notation "x [=] y" := (HRwequal x y) (at level 80).

(* example : 
Lemma f: forall x y z, x +w -w y *w z [=] x +w (y *w z).
*)

Definition HRw2 : HRw := [1] [+] [1].
Notation "[2]" := HRw2.
Definition HRw3 : HRw := [2] [+] [1].
Notation "[3]" := HRw3.
End mHRwspec.
