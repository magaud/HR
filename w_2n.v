Require Export LaugwitzSchmieden.
Require Import HRw_spec.

Module LS2n <: Num_w.

Include LS. 
(* Definitions in LS are available here thanks to the module type declaration for LS - see above - *)
Fixpoint power2 (n:nat) : Z :=
match n with 
| O => 1%Z
| S p => (2 * (power2 p))%Z
end.

Lemma power2_pos : forall n:nat, (0 < power2 n)%Z.
Proof.
induction n.
unfold power2; omega.
change (0 < 2 * (power2 n))%Z.
omega.
Qed.

Lemma n_power : forall n, (Z_of_nat n < power2 n)%Z.
Proof.
induction n.
simpl; omega.
change (Z.of_nat (S n) < 2* power2 n)%Z.
setoid_replace (Z.of_nat (S n)) with ((Z.of_nat n)+1)%Z 
  by (rewrite Nat2Z.inj_succ; unfold Z.succ; reflexivity).
omega.
Qed.

Definition w :A := fun (n:nat) => power2 n.

Lemma beta_w : leA beta w.
Proof.
unfold beta, w; unfold_intros.
exists 0%nat.
intros.
generalize (n_power n); intros; omega.
Qed.

Lemma Aw : 0 <A w.
Proof.
unfold ltA.
exists 0%nat.
intros; apply power2_pos.
Qed.

Lemma lim_lt_w : forall a, lim a/\ leA 0 a -> ltA a w.
intros.
apply lt_le_trans with beta.
apply lim_lt_beta.
assumption.
apply beta_w.
Qed.

Lemma div_modw2 : forall a, w*(a/w) =A a + - (a mod% w).
Proof.
intros.
apply div_mod2.
left; apply Aw.
Qed.

Lemma div_modw3 : forall a, |(a mod% w)| <A w.
Proof.
intros.
apply div_mod3.
apply Aw.
Qed.

Lemma  ANS3 : ~ lim w.
Proof.
intro H; unfold lim in *.
elim H; clear H; intros p (Hstdp,(Hle0p,Hwp)).
unfold ltA,a0 in *.
elim Hstdp.
intros b Hb.
elim Hwp.
intros a Ha.
elim Hle0p.
intros c Hc.
(* w (p (a+b+c+1) + a + b + c + 1) = p (a+b+c+1) + a+b+c+1 *)
(* p (p (a+b+c+1) + a + b + c + 1) = p (a + b + c + 1) because p(a+b+c+1)>=0 et Hb: p is std *)
pose (px:=p (a+b+c+1)%nat).
assert (0<= px)%Z.
apply Hc.
omega.
pose (x:=((Z.abs_nat px)+a+b+c+1)%nat).
assert ((|w |) (x) < p (x))%Z.
apply Ha.
unfold px,x in *.
omega.

assert  ((|w |) (x) >= p (x))%Z.
apply Z.le_ge.
apply Z.le_trans with  (((|fun n => Z_of_nat n|) (x))%Z).
unfold absA in *.
unfold w.
unfold x.
replace (p (Z.abs_nat px + a + b + c + 1)%nat)%Z with 
(p (a+b+c+1)%nat)%Z.
rewrite Z.abs_eq.
replace (Z.abs_nat px + a + b + c + 1)%nat with (Z.abs_nat (px + (Z_of_nat (a + b + c + 1))))%nat.
rewrite inj_Zabs_nat.
rewrite Z.abs_eq.
unfold px.
omega.
omega.
rewrite Zabs_nat_Zplus.
rewrite Zabs_nat_Z_of_nat.
ring.
unfold px; apply Hc.
omega.
solve [auto with zarith].
solve [auto with zarith].
apply Hb.
omega.
omega.
unfold w, absA.
rewrite Z.abs_eq.
rewrite Z.abs_eq.
assert (Z.of_nat x < power2 x)%Z.
apply n_power.
omega.
generalize (power2_pos x); intros; omega.
apply Zle_0_nat.
omega.
Qed.

Lemma power2_increases_step : forall m:nat, (power2 m <= power2 (S m))%Z.
Proof.  
induction m.
simpl; omega.
replace (power2 (S (S m))) with (2*((power2 (S m))))%Z by trivial.
replace (power2 (S m)) with (2*power2 m)%Z by trivial.
apply Z.mul_le_mono_nonneg_l.
omega.
assumption.
Qed.

Lemma w_increases : forall n m:nat, (n <= m)%nat -> (w n <= w m)%Z. 
Proof.
  induction 1.
apply Z.le_refl.
unfold w. 
apply Z.le_trans with (power2 m).
assumption.
apply power2_increases_step.
Qed.

End LS2n.



(* axiom A2.3 does not hold : Lemma R2_3 : forall x y, ~HRwdiff x y -> HRwequal x y. *)
Module Export KK := mHRwspec(LS2n).

Definition u (n:nat) : Z :=  
if (Nat.even n) then 0 else LS2n.w (Nat.div2 n).

Lemma u_positive : forall n:nat, (0 <= u n)%Z.
Proof.
  intros.
  unfold u; simpl.
  destruct (Nat.even n).
  omega.
  unfold LS2n.w.
  apply Z.lt_le_incl.
  apply LS2n.power2_pos.
Qed.

Lemma u_pos : LS2n.leA LS2n.a0 u.
Proof.
unfold LS2n.leA, LS2n.a0.
exists 0; intros.
apply u_positive.
Qed.

(* belongs to HRw *)

Lemma Pu : P u.
Proof.
  unfold P.
  exists (fun x => 1%Z).
  unfold LS2n.lim; split.
exists (fun x => 2%Z).
split.
unfold LS2n.std; intros; exists 0%nat; reflexivity.
split.
unfold LS2n.leA, LS2n.a0.
exists 0%nat.
intros;omega.

unfold LS2n.ltA, LS2n.absA.
exists 0%nat; intros.
rewrite Z.abs_eq; omega.
split.
unfold LS2n.ltA, LS2n.a0.
exists 0; intros; omega.
unfold LS2n.leA, LS2n.absA, LS2n.multA.
exists 0; intros; rewrite Z.abs_eq.
ring_simplify.
unfold u; destruct (Nat.even n).
apply Z.lt_le_incl.
apply LS2n.power2_pos.
unfold LS2n.w.
Search LS2n.power2.
apply LS2n.w_increases.
Search Nat.div2.
apply Nat.div2_decr.
solve [auto].
apply u_positive.
Qed.

Definition HRw_u : HRw.
  exists u.
  apply Pu.
Defined.

(* not equal to 0 *)
Lemma HRwequal_u_0 : ~ HRwequal HRw_u HRw0.
Proof.
  unfold HRwequal, HRw_u, HRw0; (*unfold LS2n.lim, LS2n.leA, LS2n.multA, LS2n.absA, LS2n.plusA, LS2n.oppA, LS2n.a0, LS2n.w; *) intros; intro.
  pose (p k:=(Z.abs (Z.div (LS2n.w (2*k+1)%nat) (LS2n.w k))+1)%Z).
  
(*assert (LS2n.ltA LS2n.w (LS2n.multA p u) ).
unfold LS2n.ltA, LS2n.multA.
exists 1.
intros.
unfold u.
unfold p.
*)

assert (Hlim:LS2n.lim p).
admit.
assert (Hlt:LS2n.ltA LS2n.a0 p).
admit.
assert (HA:LS2n.leA (LS2n.multA p (LS2n.absA (LS2n.plusA u (LS2n.oppA LS2n.a0)))) LS2n.w).
apply (H p Hlim Hlt).

apply (LS2n.le_lt_False (LS2n.multA p u) LS2n.w).

assert (L1:LS2n.equalA (LS2n.plusA u (LS2n.oppA LS2n.a0)) u).
assert (L2:LS2n.equalA (LS2n.oppA LS2n.a0) LS2n.a0).
rewrite <- LS2n.plus_neutral.
apply LS2n.plus_opp.
rewrite L2.
rewrite LS2n.plus_comm.
rewrite LS2n.plus_neutral.
reflexivity.
rewrite LS2n.abs_pos_val in HA.
rewrite L1 in HA.
assumption.
rewrite L1.
apply u_pos.

Admitted.
(*Lemma x : LS2n.oppA LS2n.a0 = LS2n.a0.
Proof.
unfold LS2n.oppA, LS2n.a0.
Admitted.
*)
(* not distinct from 0 *)
Lemma HRwdiff_u_0 : ~ HRwdiff HRw_u HRw0.
Proof.
  unfold HRwdiff, HRw_u, HRw0; intros; intro Hex.
  destruct Hex.
Admitted.    

Lemma contradiction : (forall x y, ~HRwdiff x y -> HRwequal x y) -> False.
Proof.
intros.
generalize (H HRw_u HRw0); intros Hsp.
apply HRwequal_u_0.
apply Hsp.
apply HRwdiff_u_0.
Qed.



