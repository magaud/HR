Require Export LaugwitzSchmieden.

Module LSw <: Num_w.

Include LS. 
(* Definitions in LS are available here thanks to the module type declaration for LS - see above - *)

Parameter w: nat->Z.
Axiom ANS3 : ~lim w.
Axiom Aw : 0<A w.

Axiom lim_lt_w : forall a, lim a/\ leA 0 a -> ltA a w.

Lemma div_modw2 : forall a, w*(a/w) =A a + - (a mod% w).
Proof.
intros a; apply div_mod2.
left; apply Aw.
Qed.

Lemma div_modw3 : forall a, |(a mod% w)| <A w.
Proof.
intros a; apply div_mod3.
apply Aw.
Qed.

End LSw.


