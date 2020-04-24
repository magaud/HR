Require Export LUB_spec.

Module integral (N:Num_w).

Import N.
Module Export XX:=lub_spec(N).

(*
Lemma integral_prop : forall a b, a*w b =w HRw0 -> a=w HRw0 \/ b=w HRw0.
Proof.
intros a; destruct a as [a Ha]; intros b; destruct b as [b Hb].
simpl; intros.
Admitted.
*)
End integral.