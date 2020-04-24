Require Export Bridges_order2_LS.

Import mBridges2_LS.
Import LSw.

(** congruent is an equivalence relation *)

Lemma congr_refl : forall a, congruent a a.
Proof.
destruct Aw as [nw Hnw]; unfold a0 in Hnw.
red;intros. 
exists (nw+1)%nat.
intros.
setoid_replace ((a k - a k) * w l - (a l - a l) * w k)%Z with 0%Z by ring.
simpl.
replace (r * 0)%Z with (w k * 0)%Z by ring.
apply Zmult_le_compat_l.
assert (0< w l)%Z by (apply Hnw; omega).
omega.
assert (0< w k)%Z by (apply Hnw; omega).
omega.
Qed.

Lemma congr_sym : forall a b, congruent a b -> congruent b a.
Proof.
unfold congruent; intros a b Hab r Hr.
destruct (Hab r Hr) as [p Hp]. 
exists p.
intros.
setoid_replace ((b k - a k) * w l - (b l - a l) * w k)%Z with 
(- ((a k - b k) * w l - (a l - b l) * w k))%Z by ring.
rewrite Z.abs_opp.
apply Hp; assumption.
Qed.

Lemma congr_trans : forall a b c, congruent a b -> congruent b c -> congruent a c.
Proof.
unfold congruent; intros a b c Hab Hbc r Hr.
assert (H2r:(0 < 2 * r)%Z) by omega.
destruct (Hab (2*r)%Z H2r) as [p Hp]; clear Hab.
destruct (Hbc (2*r)%Z H2r) as [q Hq]; clear Hbc.
exists (p+q+1)%nat.
intros k Hk l Hl.
rewrite <- (Z.abs_eq r) by omega.
rewrite <- Z.abs_mul.
replace (r * ((a k - c k) * w l - (a l - c l) * w k))%Z with 
(r* ((a k - b k) * w l - (a l - b l) * w k) + r*((b k - c k) * w l - (b l - c l) * w k))%Z by ring.
eapply Zle_trans.
apply Z.abs_triangle.
rewrite (Z.abs_mul r).
rewrite (Z.abs_eq r) by omega.
rewrite Z.abs_mul.
rewrite (Z.abs_eq r)by omega.
apply Zle_mult_inv with 2%Z.
omega.
rewrite Z.mul_add_distr_l.
replace (2 * (w k * w l))%Z with ((w k * w l) + (w k * w l))%Z by ring.
assert (Hkq:(k>=q)) by omega.
assert (Hkp:(k>=p)) by omega.
assert (Hlq:(l>=q)) by omega.
assert (Hlp:(l>=p)) by omega.
generalize (Hp k Hkp l Hlp); clear Hp.
generalize (Hq k Hkq l Hlq); clear Hq.
repeat rewrite Zmult_assoc.
intros; omega.
Qed.

Instance HRwcongr_equiv : Equivalence HRw_congruent.
Proof.
constructor; unfold HRw_congruent.
unfold Reflexive; intros; apply congr_refl.
unfold Symmetric; intros; apply congr_sym; assumption.
unfold Transitive; intros; eapply congr_trans; eassumption.
Qed.

Lemma congruent0_bounded : forall x, congruent x 0 -> exists M:Z, forall k, (Z.abs (x k) < M * (w k))%Z.
Proof.
Admitted.
 
(*

Lemma lemma1 : forall a b c, (Z.abs (a-b) <=c -> Z.abs a <= c + Z.abs b)%Z.
Proof.
intros.
Search ({_<_}+{_})%Z.
destruct (Z_lt_ge_dec (a-b) 0)%Z.
rewrite Z.abs_neq in H.
destruct (Z_lt_ge_dec a 0)%Z.
rewrite Z.abs_neq.
destruct (Z_lt_ge_dec b 0)%Z.
rewrite Z.abs_neq.
omega.
omega.
rewrite Z.abs_eq.
omega.
omega.
omega.
rewrite Z.abs_eq.
destruct (Z_lt_ge_dec b 0)%Z.
rewrite Z.abs_neq.
omega.
omega.
rewrite Z.abs_eq.
omega.
omega.
omega.
omega.
rewrite Z.abs_eq in H.

destruct (Z_lt_ge_dec a 0)%Z.
rewrite Z.abs_neq.
destruct (Z_lt_ge_dec b 0)%Z.
rewrite Z.abs_neq.
omega.
omega.
rewrite Z.abs_eq.
omega.
omega.
omega.
rewrite Z.abs_eq.
destruct (Z_lt_ge_dec b 0)%Z.
rewrite Z.abs_neq.
omega.
omega.
rewrite Z.abs_eq.
omega.
omega.
omega.
omega.
Qed.
*)

(*
Lemma HRw_congruent_0_HRwgt_w : forall x, congruent x 0 -> |x| <A w. 
Proof.
unfold congruent, leA, ltA, absA.
destruct Aw as [nw Hnw].
intros.
assert (Hlt:(0<1)%Z).
omega.
destruct (H 1%Z Hlt) as [n Hn]; clear Hlt.
exists (n+nw+1)%nat.
intros p Hlt.
assert (Hpn:(p>n+nw+1)) by omega.
assert (Hpn':p>=n) by omega.
generalize (Hn p Hpn' (n+nw+1)%nat); clear Hn; intros Hp.
setoid_replace (x p - a0 p)%Z with (x p)%Z in Hp by (unfold a0; ring).
apply Zmult_lt_reg_l with (w p).
apply Hnw; omega.


setoid_replace (x p + (- a0 p))%Z with (x p)%Z in Hp by ring.

*)
