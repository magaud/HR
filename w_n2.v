Require Export LaugwitzSchmieden.

Module LSn2 <: Num_w.

Include LS. 
(* Definitions in LS are available here thanks to the module type declaration for LS - see above - *)

Definition w :A := fun (n:nat) => Z_of_nat (n*n).

Lemma n_n2 : beta <A w.
unfold beta,w; unfold_intros.
exists 2%nat.
intros.
apply inj_lt.
setoid_replace n with (n*1)%nat at 1 by ring.
apply mult_lt_compat_l; omega.
Qed.

Lemma n_n2bis : forall n, (Z_of_nat n <= Z_of_nat (n*n))%Z.
Proof.
induction n.
simpl; omega.
rewrite Nat2Z.inj_mul.
setoid_replace (Z.of_nat (S n)) with (Z.of_nat (S n)* 1)%Z at 1 by ring.
apply Zmult_le_compat_l.
rewrite Nat2Z.inj_succ.
omega.
omega.
Qed.

Lemma lim_lt_w : forall a:A, lim a/\ leA 0 a -> ltA a w.
Proof.
intros.
apply lt_le_trans with beta.
apply lim_lt_beta.
assumption.
apply lt_le; apply n_n2.
Qed.

Lemma ANS3 : ~lim w.
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
apply n_n2bis.
apply Zle_0_nat.
apply Zle_0_nat.
omega.
Qed.

Lemma Aw : 0 <A w.
Proof.
unfold ltA.
exists 0%nat.
intros;unfold a0, w.
rewrite Nat2Z.inj_mul.
setoid_replace 0%Z with (Z.of_nat n * 0)%Z by ring.
assert (0<Z.of_nat n)%Z by omega.
apply Zmult_lt_compat_l; assumption.
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

End LSn2.
