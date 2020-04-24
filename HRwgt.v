Require Export HRwequal.

Module mHRwgt (N:Num_w).

Import N.
Module Export LL := mHRwequal(N).

Definition HRwgt (y x : HRw) : Prop :=
match y with exist _ yy Hyy =>
match x with exist _ xx Hxx =>
(exists n, lim n /\ 0 < n /\ (w <= (n*(yy+ (-xx)))))
end end. 

Notation "x [>] y" := (HRwgt x y) (at level 80).

(* R2 *)

(* Links : ">=" -> "[>=]" , "[>]" -> ">" *)

Lemma HRwgt_Zgt : forall x y:HRw, x [>] y -> (proj1_sig y) < (proj1_sig x).
Proof.
intros x y; case x; intros xx Hxx; case y; intros yy Hyy.
simpl;intros Hexists.
elim Hexists; intros n (Hlim,(Hlt,H)).
apply lt_plus_inv with (oppA yy).
setoid_replace (yy + - yy) with a0 by ring.
apply lt_mult_inv with n . 
assumption.
setoid_replace (n * 0) with 0 by ring.
apply lt_le_trans with w.
apply Aw.
assumption.
Qed.

Lemma HRwgt_Zgt' : forall (a b:A) (Ha:P a) (Hb: P b), 
  (exist (fun (x:A) => P x) a Ha) [>] (exist (fun (x:A) => P x) b Hb) -> b < a.
Proof.
intros a b Ha Hb H.
change (proj1_sig (exist (fun (x:A) => P x) b Hb) < proj1_sig (exist (fun (x:A) => P x) a Ha)).
apply HRwgt_Zgt; assumption.
Qed.

End mHRwgt.