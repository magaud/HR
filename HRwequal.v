Require Export HRw.

Module mHRwequal (N:Num_w).

Import N.
Module Export HH := mHRw(N).

(* Egalité à l'échelle Omega *)
Definition HRwequal (x y : HRw) : Prop :=
match x with exist _ xx Hxx =>
match y with exist _ yy Hyy => 
(forall n, lim n ->0 < n -> ( (n*|xx + (- yy)|) <= w))
end end.

Lemma HRwequal_refl : forall x, HRwequal x x.
Proof.
intros x; case x; intros xx Hxx; simpl.
intros.
setoid_replace (xx+ -xx) with 0 by ring.
rewrite abs_pos_val.
setoid_replace (n*0) with 0 by ring.
intros; apply lt_le; apply Aw.
apply le_refl.
Qed.

Lemma HRwequal_sym : forall x y, HRwequal x y -> HRwequal y x.
Proof.
intros x y; case x; intros xx Hxx; case y; intros yy Hyy; simpl.
intros.
assert  (|yy + - xx |==|xx + - yy |).
setoid_replace (yy + -xx) with (- (xx + - yy)) by ring.
rewrite abs_minus; reflexivity.
rewrite H2.
apply H; solve [intuition].
Qed.

Lemma HRwequal_trans : forall x y z, HRwequal x y -> HRwequal y z -> HRwequal x z.
Proof.
intros x; case x; intros xx Hxx;
intros y; case y; intros yy Hyy;
intros z; case z; intros zz Hzz.
simpl; intros Hxy Hyz n Hlim Hlt. 
apply le_mult_inv with (a1+a1).
setoid_replace 0 with (0+0) by ring.
apply lt_plus; apply lt_0_1.
apply le_trans with ((1+1)*n*(|xx + - yy| + |yy + - zz|)).
rewrite mult_assoc.
apply le_mult.
setoid_replace 0 with ((1+1)*0) by ring.
apply le_mult.
setoid_replace 0 with (0+0) by ring; apply le_plus; apply lt_le; apply lt_0_1.
apply lt_le; assumption.
setoid_replace (xx + -zz) with ((xx + -yy)+(yy + - zz)) by ring.
apply abs_triang.
ring_simplify.
setoid_replace ((1+1)* w) with (w + w) by ring.
setoid_replace ((1+1)*n) with (n+n) by ring.
apply le_plus.
apply Hxy.
apply ANS2a; assumption.
setoid_replace 0 with (0+0) by ring; apply lt_plus; assumption.
apply Hyz.
apply ANS2a; assumption.
setoid_replace 0 with (0+0) by ring; apply lt_plus; assumption.
Qed.

End mHRwequal.

