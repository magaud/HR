Require Export Numbers_facts.

Module mHRw (N:Num_w).

Import N.

Definition P := fun (x:A) => exists n:A, (lim n /\ 0 < n /\  (|x| <= n*w)).

Definition HRw := {x:A | P x }.

Lemma HRw_P : forall x:HRw, P (proj1_sig x).
Proof.
intros x; case x.
simpl; trivial.
Qed.

Lemma P0 : P 0.
Proof.
unfold P.
exists 1.
split.
apply ANS1.
split.
apply lt_0_1.
rewrite mult_neutral.
rewrite abs_pos_val.
apply lt_le.
apply Aw.
apply le_refl.
Qed.

Definition HRw0 : HRw.
exists 0.
apply P0.
Defined.

Lemma P1 : P 1.
Proof.
unfold P.
exists 1.
split.
apply ANS1.
split.
apply lt_0_1.
rewrite mult_neutral.
rewrite abs_pos_val.
setoid_replace 1 with (0+1) by ring.
apply lt_le_2.
apply Aw.
apply lt_le.
apply lt_0_1.
Qed.

Definition HRw1_small : HRw.
exists 1.
apply P1.
Defined.

Lemma Pw : P w.
Proof.
unfold P.
exists 1.
split.
apply ANS1.
split.
apply lt_0_1.
rewrite abs_pos_val.
setoid_replace (1*w) with w by ring.
apply le_refl.
apply lt_le; apply Aw.
Qed.

Definition HRw1 : HRw.
exists w.
apply Pw.
Defined.

End mHRw.
