Require Export sequences_AX.

Module lub_proof(N:Num_w).

Import N.
Module Export UU := seq(N).

Axiom lim_not_lim : forall n v, lim n/\0<=n -> ~lim v/\0<=v -> n <v.

Lemma foo :
forall S : subset,
forall Hdec : forall alpha beta : HRw,
       beta [>] alpha -> {s : HRw | S s /\ s [>] alpha} + {upper_bound S beta},
forall s0 : HRw,
forall Hs0 : S s0,
forall b0' : HRw,
forall b0,
forall Hb0 : b0 = b0' [+] [1],
forall Hup : upper_bound S b0,
forall s_b_alpha_beta : forall (k : A) (Hk : std k /\ 0 <= k),
                 {sn : HRw & {bn : HRw & Psb S s0 b0 k Hk sn bn}},
forall Hs_b_alpha_beta : s_b_alpha_beta = def_s_b_alpha_beta S Hdec s0 b0 Hs0 Hup,               
forall ss : forall k0 : A, std k0 /\ 0 <= k0 -> HRw,
forall Hss : ss = fun (k0 : A) (Hk0 : std k0 /\ 0 <= k0) =>
      projT1 (s_b_alpha_beta k0 Hk0),
forall bb : forall k0 : A, std k0 /\ 0 <= k0 -> HRw,
forall Hbb : bb = fun (k0 : A) (Hk0 : std k0 /\ 0 <= k0) =>
      projT1 (projT2 (s_b_alpha_beta k0 Hk0)), 
forall ssA : forall k0 : A, std k0 /\ 0 <= k0 -> A,
forall HssA : ssA = fun (k0 : A) (Hk0 : std k0 /\ 0 <= k0) => proj1_sig (ss k0 Hk0),
forall bbA : forall k0 : A, std k0 /\ 0 <= k0 -> A,
forall HbbA : bbA = fun (k0 : A) (Hk0 : std k0 /\ 0 <= k0) => proj1_sig (bb k0 Hk0),
forall v1 : A,
forall Hv1 : ~ lim v1 /\
      0 < v1 /\
      (forall k : A,
       0 <= k /\ k <= v1 -> extends ssA k <= min k (extends bbA)),
forall v2 : A,
forall Hv2 : ~ lim v2 /\
      0 < v2 /\
      (forall n : A,
       0 <= n /\ n <= v2 ->
       forall m : A, 0 <= m -> m < n -> extends ssA m <= extends ssA n),
forall n : A,
forall Hlim : std n,
forall Hlt : 0 <= n,
extends ssA n <= min (minA v1 v2) (extends bbA).
Proof.
intros.
elim (A0_dec (v1 + - v2)). (* Meaning ? *)
intros Hv1v2. 
apply le_trans with (min v1 (extends bbA)).
apply le_trans with (extends ssA  v1).
decompose [and] Hv2.
apply H3.
split.
apply lt_le; solve[intuition].
setoid_replace v2 with (0+v2) by ring.
setoid_replace v1 with ((v1 + -v2)+v2) by ring.
apply le_plus.
elim Hv1v2; intros Hv1v2'.
apply lt_le; assumption.
rewrite Hv1v2'; apply le_refl.
apply le_refl.
assumption.
assert (nlim:lim n).
apply std_lim; assumption. 
apply lim_not_lim; solve [intuition | intuition; apply lt_le; intuition].
decompose [and] Hv1.
apply H3; split;  solve[intuition | intuition; apply lt_le; intuition | apply le_refl ]. 
apply min_def2.
unfold minA; destruct (A0_dec (v1 +- v2)).
apply le_refl.
elim Hv1v2.
intros.
assert (Hf:False) 
  by (apply contradict_lt_le with (s:=v1+ - v2) (x:=0); [ assumption | apply lt_le; assumption]).
destruct Hf.
intros Hrew; rewrite Hrew in l.
assert (Hf:False) by (apply not_lt_0_0; assumption).
destruct Hf.
intros Hv1v2.
apply le_trans with (min v2 (extends bbA)).
apply le_trans with (extends ssA  v2).
decompose [and] Hv2.
apply H3.
split.
apply lt_le; assumption.
apply le_refl.
assumption.
assert (nlim : lim n).
apply std_lim; assumption.
apply lim_not_lim;  solve [intuition | intuition; apply lt_le; intuition].
decompose [and] Hv1.
apply H3.
split.
apply lt_le; solve [intuition]. 
setoid_replace v2 with (0+v2) by ring.
setoid_replace v1 with ((v1 + -v2)+v2) by ring.
apply le_plus.
apply lt_le; assumption.
apply le_refl.
apply min_def2.
unfold minA.
destruct (A0_dec (v1 + - v2)).
destruct s.
assert (Hf:False) 
  by (apply contradict_lt_le with (s:=v1+ - v2) (x:=0); [ assumption | apply lt_le; assumption]).
destruct Hf.
rewrite e in Hv1v2.
assert (Hf:False) by (apply not_lt_0_0; assumption).
destruct Hf.
apply le_refl.
Qed.


Lemma least_upper_bound_principle : 
  forall S:subset, non_empty S -> bound_above S -> 
    (forall alpha beta:HRw,  beta [>] alpha -> 
      {s:HRw| S s /\ s [>] alpha}+{upper_bound S beta}) -> 
   has_least_upper_bound S.
Proof.
intros S Hnon_empty Hbound Hdec.
elim Hnon_empty; intros s0 Hs0.
elim Hbound; intros b0' Hb0'.

pose (b0 := b0' [+] [1]).
assert (Hup:(upper_bound S b0)) by (unfold b0; apply HRwgt_upper_bound; assumption).
assert (b0 [>] s0) by (unfold b0; apply Hup; assumption).
pose (s_b_alpha_beta := (def_s_b_alpha_beta S Hdec s0 b0 Hs0 Hup)).
(* avec valeurs dans HRw *)
pose (ss := fun k0 Hk0 =>  (projT1  (s_b_alpha_beta k0 Hk0))).
pose (bb := fun k0 Hk0 => (projT1 (projT2  (s_b_alpha_beta k0 Hk0)))).
(* avec valeurs dans A *)
pose (ssA := (fun k0 Hk0 => proj1_sig (ss k0 Hk0))).
pose (bbA := (fun k0 Hk0 => proj1_sig (bb k0 Hk0))).

assert (Hbn_sup_sn : (forall n, std n /\ 0<=n ->  (forall k, forall Hk:(std k/\ 0 <=k), k<=n ->  
  (ssA k Hk) <= (min_lim n bbA)))).
intros n (Hlimn, Hlen) k (Hlimk,Hlek) Hkn.
replace (ssA k (conj Hlimk Hlek)) with (proj1_sig (ss k (conj Hlimk Hlek))) by solve[trivial].
assert (HS:(S (ss k (conj Hlimk Hlek)))).
unfold ss.
elim (s_b_alpha_beta k (conj Hlimk Hlek)).
intros sk (bk, (Hsk,(Hbk,H'))).
simpl; solve [intuition].
apply min_lim_prop.
intros p (Hlimp,Hlep) Hpn.
apply lt_le.
assert (bb p (conj Hlimp Hlep) [>] ss k (conj Hlimk Hlek)).
unfold ss.
elim (s_b_alpha_beta k (conj Hlimk Hlek)).
intros sk (bk,(Hsk,(Hbk,H'))).
simpl; unfold bb.
elim (s_b_alpha_beta p (conj Hlimp Hlep)).
intros sp (bp,(Hsp,(Hbp,Hp'))).
simpl; unfold upper_bound in Hbp.
apply Hbp.
solve [intuition].
apply HRwgt_Zgt.
assumption.

assert (Hsn_increasing : forall n, forall Hn:std n/\0<= n, forall m, forall (Hm:std m/\0<= m), 
  n <= m -> ssA n Hn <= ssA m Hm).
intros.
apply thm_Hsn_increasing with (S:=S) (Hdec:=Hdec) (s0:=s0) (b0:=b0) (Hs0:=Hs0) (Hb0S := Hup) (n:=m) (m:=n) (bbA:=bbA).
unfold ssA,ss, s_b_alpha_beta; trivial.
unfold bbA,bb, s_b_alpha_beta; trivial.
assumption.

assert (Hequal : forall n:A, forall Hn: std n /\ 0<= n, 
  (HRwequal (HRwminus (bb n Hn) (ss n Hn)) 
                     (HRwmult (power two_third n Hn) (HRwminus b0 s0)))).
intros n Hn.
unfold bb,ss; elim (s_b_alpha_beta n Hn).
intros sn (bn, (Hsn,(Hbn,Hequaln))).
simpl.
unfold HRwminus in *.
subst.
assumption.

(* we overspill the min_bn_sup_sn using the magic function "extends" *)
assert (Hbn_sup_sn' : exists v:A, ~lim v /\ 0<v /\
  (forall k, 0 <=k /\ k<=v ->  (extends ssA) k <= (min k (extends bbA)))).
apply (overspill_principle' (fun m => extends ssA m <= min m (extends bbA))).
intros.
apply min_prop.
intros.
solve [intuition].
rewrite <- extends_id with (H:=H1).
intros.
assert (H2': std k /\ 0<=k).
solve [intuition].
rewrite <- extends_id with (H:=H2').
apply le_trans with (min_lim n bbA).
apply Hbn_sup_sn with (n:=n).
assumption.
apply le_refl.
apply min_lim_def.
assumption.
assumption.

assert (Hsn_increasing' : exists v:A,~lim v /\ 0<v /\ forall (n : A), 0 <= n /\ n<= v -> 
forall (m : A), 0<=m -> m < n -> (extends ssA) m  <= (extends ssA) n).

assert (Hsn_increasing'' : exists v : A,
         ~ lim v /\
         0 < v /\
         (forall n : A,
          0 <= n /\ n <= v ->
          forall m : A, 0 <= m /\ m <= v -> m < n -> (extends ssA) m  <= (extends ssA) n)).
apply (overspill_principle2 (fun n m => m < n -> extends ssA m <= extends ssA n)).

intros.
rewrite <- (extends_id ssA n H1).
rewrite <- (extends_id ssA m H2).

apply Hsn_increasing.
apply lt_le; assumption.

destruct Hsn_increasing'' as [nv Hnv].
exists nv.
repeat split; try solve [intuition].
intros; apply Hnv; try solve [intuition].
split.
assumption.
apply le_trans with n.
apply lt_le.
assumption.
solve [intuition].

elim Hbn_sup_sn'.
intros v1 Hv1.
elim Hsn_increasing' .
intros v2 Hv2.
pose (bA:=min (minA v1 v2) (extends bbA)).
unfold has_least_upper_bound.
assert (Hb:(P bA)).
assert (Hl0:std 0/\0<=0) by (apply H0std). (*split; [apply lim0 | apply le_refl]).*)

elim (A0_dec bA). (* Meaning ? *)
intros HA0; elim HA0.
intros Hneg.
assert (ssA 0 Hl0 <= bA).
unfold bA.
decompose [and] Hv1.
rewrite (extends_id ssA).
eapply foo with (v1:=v1) (b0:=b0) (b0':=b0') (ss:=ss) (bb:=bb) (ssA:=ssA) (bbA:=bbA)(s_b_alpha_beta:=s_b_alpha_beta); try solve [intuition].
generalize (H0std).
assert (|bA|<=|ssA 0 Hl0|).
rewrite abs_neg_val.
rewrite abs_neg_val.
setoid_replace (-bA) with ((-a1)*bA) by ring.
setoid_replace (- ssA 0 Hl0) with ((-a1)*(ssA 0 Hl0)) by ring.
apply le_mult_neg.
apply lt_m1_0.
assumption.
apply le_trans with bA.
assumption.
apply lt_le; assumption.
apply lt_le; assumption.

assert (P (ssA 0 Hl0)).
replace (ssA 0 Hl0) with (proj1_sig (ss 0 Hl0)) by solve [auto].
apply HRw_P.
elim H3; intros n (Hlimn,(H0n, Hex)).
exists n.
split.
assumption.
split.
assumption.
apply le_trans with (|ssA 0 Hl0 |) ; assumption.
intros Hr; unfold P.
elim P0; intros nP0 HP0; exists nP0; rewrite Hr; solve [intuition].
intros Hpos.
unfold bA.
assert ((min (minA v1 v2) (extends bbA)) <= (extends bbA) 0).
apply min_def.
split.
apply le_refl.
apply minA_le; solve [apply lt_le; intuition].
assert (P (extends bbA 0)).

rewrite <- extends_id with (H:=Hl0) in *.
replace (bbA 0 Hl0) with (proj1_sig (bb 0 Hl0)) by solve [auto].
apply HRw_P.
elim H2; intros n (Hlimn,(H0n, Hex)).
exists n.
split.
assumption.
split.
assumption.
apply le_trans with (| extends bbA 0|).
rewrite abs_pos_val.
rewrite abs_pos_val.
assumption.
apply le_trans with (min (minA v1 v2) (extends bbA)).
apply lt_le; assumption. 
assumption.
apply lt_le; assumption. 
assumption.
(* ici, on a construit b et on va montrer que c'est bien la plus petite borne supérieure pour S *)
pose (b :=(exist
       (fun x0 : A => exists n1 : A, lim n1 /\ 0 < n1 /\ (|x0 |) <= n1 * w)
       bA Hb)).
exists b.

unfold least_upper_bound.
split.

intros s Hs.
assert (~ (s [>] b)).
intro Hsb.
assert (H1:exists n:A, std n /\ 0 <= n /\ forall (Hyp:std n/\0 <= n), 
  (s [+] -w b) [>] ((bb n Hyp) [+] -w (ss n Hyp))). (* (1) *)
apply has_limit with (x:=(b0 [+] (-w s0))) (eps:=s [+] (-w b)).
apply HRwgt_HRwplus_inv_l with s0.
ring_simplify.
unfold upper_bound in Hup; apply Hup; assumption.
apply HRwgt_HRwplus_inv_l with b.
ring_simplify.
assumption.
assumption.

elim H1; clear H1.
intros n (Hlim,(Hlt,H1)).
generalize (H1 (conj Hlim Hlt)); clear H1; intros H1.
assert (H2:(bb n (conj Hlim Hlt) [+] -w (ss n (conj Hlim Hlt))) [>=] 
        (bb n (conj Hlim Hlt) [+] -w b)). (* (2) *)
assert (b [>=] (ss n (conj Hlim Hlt))).
apply Zge_HRwge.
simpl.
replace (proj1_sig (ss n (conj Hlim Hlt))) with (ssA n (conj Hlim Hlt)) by solve [auto].
unfold bA.
rewrite extends_id with (H:=conj Hlim Hlt).
(* HHH *)
eapply foo with (v1:=v1) (b0:=b0) (b0':=b0') (ss:=ss) (bb:=bb) (ssA:=ssA) (bbA:=bbA)(s_b_alpha_beta:=s_b_alpha_beta); try solve [intuition].

assert (-w (ss n (conj Hlim Hlt)) [>=] -w b).
apply HRwge_HRwopp; assumption.

rewrite (HRwplus_comm _ (-w b)).
rewrite HRwplus_comm.
apply R2_4'; assumption.

generalize (HRwgt_HRwge_trans _ _ _ H1 H2); intros H3.
generalize (HRwgt_HRwplus_inv_r _ _ (-w b) H3); intros H4.
assert (bb n (conj Hlim Hlt) [>=] s).
unfold bb; elim (s_b_alpha_beta n (conj Hlim Hlt)).
intros sn (bn, (alphan, (betan, Hn))); simpl.
apply HRwgt_HRwge.
unfold upper_bound in *; intuition.
eapply contradict_HRwgt_HRwge ; eassumption.

apply not_HRwgt_HRwge; assumption.

intros b' Hbb'.
assert (H1:exists n:A, std n /\ 0 <= n /\ forall (Hyp:std n/\0 <= n), 
  (b [+] -w b') [>] ((bb n Hyp) [+] -w (ss n Hyp))).
apply has_limit with (x:=b0 [+] (-w s0)) (eps:=b [+] (-w b')).
apply HRwgt_HRwplus_inv_l with s0.
ring_simplify.
unfold upper_bound in Hup; apply Hup; assumption.
apply HRwgt_HRwplus_inv_l with b'.
ring_simplify; assumption.
assumption.
elim H1; clear H1.
intros n (Hlim,(Hlt,H1)).
generalize (H1 (conj Hlim Hlt)); clear H1; intros H1.
assert ( (bb n (conj Hlim Hlt)) [>=] b).
apply Zge_HRwge.
change (proj1_sig b <= (bbA n (conj Hlim Hlt))).
unfold b; simpl.
assert (Hnn: (0 <=n /\ n <= minA v1 v2)).
split.
assumption.
assert (~lim (minA v1 v2)) by (apply minA_lim; solve [intuition]).
assert (nlim:lim n).
apply std_lim; assumption.
apply lt_le; apply lim_not_lim.
split; assumption.
split.
assumption.
apply minA_le; solve[apply lt_le; intuition].
rewrite extends_id. 
apply (min_def (minA v1 v2) (extends bbA) n Hnn).
assert ((bb n (conj Hlim Hlt) [+] (-w (ss n (conj Hlim Hlt)))) [>=] 
            (b [+] (-w (ss n (conj Hlim Hlt))))).
apply R2_4'; assumption.

assert (b [+] (-w b') [>] b [+] (-w ss n (conj Hlim Hlt))).
apply HRwgt_HRwge_trans with (bb n (conj Hlim Hlt) [+] (-w ss n (conj Hlim Hlt))); assumption.
assert ((b [+] (-w (ss n (conj Hlim Hlt)))) [+] ((ss n (conj Hlim Hlt) 
           [+] (-w b'))) [>] 
b [+] (-w (ss n (conj Hlim Hlt)))).
ring_simplify; unfold HRwminus.
assumption.
assert (H' : (ss n (conj Hlim Hlt) [+] (-w b')) [>] [0]).

apply HRwgt_HRwplus_inv_l with ((b [+] (-w ss n (conj Hlim Hlt)))).
rewrite (HRwplus_comm _ [0]); rewrite HRwplus_zero.
assumption.
revert H'.
unfold ss.
elim (s_b_alpha_beta n (conj Hlim Hlt)).
intros sn (bn, (Hsn,(Hbn,Hn'))).
simpl; intros H'.
exists sn.
split.
solve [intuition]. 
apply HRwgt_HRwplus_inv_l with (-w b').
rewrite (HRwplus_comm _ b').
rewrite HRwplus_opp.
rewrite HRwplus_comm.
assumption.
Qed.

End lub_proof.