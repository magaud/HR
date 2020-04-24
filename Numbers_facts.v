Require Export Setoid Ring Ring_theory Morphisms.
Require Export Numbers.

Module Type Num_facts.

Include Num.

(* equality and morphims properties *)

Instance equalA_equiv : Equivalence equalA.
Proof.
split; red; [apply equalA_refl | apply equalA_sym | apply equalA_trans ].
Qed.

Instance plusA_morphism : Proper (equalA ==> equalA ==> equalA) plusA.
Admitted. (* plusA_morphism *)

Instance oppA_morphism : Proper (equalA ==> equalA) oppA.
Admitted. (* oppA_morphism *)

Instance multA_morphism : Proper (equalA ==> equalA ==> equalA) multA.
Admitted. (* multA_morphism *)

Instance absA_morphism : Proper (equalA ==> equalA) absA.
Admitted. (* absA_morphism *)

Instance leA_morphism : Proper (equalA ==> equalA ==> Logic.iff) leA.
Admitted. (* leA_morphism *)

Instance ltA_morphism : Proper (equalA ==> equalA ==> Logic.iff) ltA.
Admitted. (* ltA_morphism *)

Instance divA_morphism : Proper (equalA ==> equalA ==> equalA) divA.
Admitted. (* divA_morphism *)

Instance modA_morphism : Proper (equalA ==> equalA ==> equalA) modA.
Admitted. (* modA_morphism *)

Instance lim_morphism : Proper (equalA ==> Logic.iff) lim.
Admitted. (* lim_morphism *)

Instance std_morphism : Proper (equalA ==> Logic.iff) std.
Admitted. (* std_morphism *)

(* Building the ring *)

Definition minusA (x y:A) := plusA x (oppA y).
Definition Radd_0_l := plus_neutral.
Definition Radd_comm := plus_comm.
Definition Radd_assoc :=plus_assoc.
Definition Rmul_1_l :=mult_neutral.
Definition Rmul_comm :=mult_comm.
Definition Rmul_assoc := mult_assoc.
Definition Rdistr_l := mult_distr_l.

Lemma Rsub_def : forall x y : A, (minusA x y) == (plusA x (oppA y)).
Proof.
intros; unfold minusA; reflexivity.
Qed.

Definition Ropp_def := plus_opp.

Lemma stdlib_ring_theory : ring_theory a0 a1 plusA multA minusA oppA equalA.
Proof.
constructor.
exact Radd_0_l. 
exact Radd_comm. 
exact Radd_assoc.
exact Rmul_1_l. 
exact Rmul_comm.
exact Rmul_assoc.
exact Rdistr_l.
exact Rsub_def.
exact Ropp_def.
Qed.

Add Ring A_ring: (stdlib_ring_theory).

(* tests *)

Lemma mult_distr_r : forall x y z:A, x*(y+z) == x*y + x*z.
Proof.
intros; ring.
Qed.

End Num_facts.

Module Type Num_w.

Include Num_facts.

Parameter w:A.

Parameter  ANS3 : ~ lim w.
Parameter  Aw : 0 < w.

Parameter lim_lt_w : forall a, lim a/\ 0<= a -> a < w.

Parameter div_modw2 : forall a, w*(a/w) == a + - (a %% w).
Parameter div_modw3 : forall a, |(a %% w)| < w.

End Num_w.
