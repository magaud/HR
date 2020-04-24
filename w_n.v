Require Export ZArith.
Require Export LaugwitzSchmieden.

Module LSn <: Num_w.

Include LS. 

Definition w :A := fun (n:nat) => Z_of_nat n.

Lemma ANS3 : ~ lim w.
Proof.
apply beta_lim.
Qed.

Lemma  Aw : 0 <A w.
Proof.
unfold ltA,w,a0.
exists 1%nat.
induction n.
omega.
unfold Z.lt;simpl; trivial.
Qed.

Lemma lim_lt_w : forall a, lim a/\ leA 0 a -> ltA a w.
Proof.
apply lim_lt_beta.
Qed.

Lemma div_modw2 : forall a, w*(a/w) =A a + - (a mod% w).
Proof.
intros; apply div_mod2.
left; apply Aw.
Qed.

Lemma div_modw3 : forall a, |(a mod% w)| <A w.
Proof.
intros; apply div_mod3.
apply Aw.
Qed.

End LSn.
