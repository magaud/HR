Require Export LUB_spec_LS.

Module seq_LS.

Module Export UU := lub_spec_LS.

Import LSw.

Section section_sequences.

Variable S : subset.
Variable Hdec :
 forall alpha beta a b:HRw, upper_bound S beta /\ S alpha /\ (beta [>=] b /\ b [>=] a /\ a [>=] alpha) -> 
   {s:HRw| S s /\ s [>] a}+{upper_bound S b}.

Variables s0 b0 : HRw.
Variable Hs0 : S s0.
Variable Hb0S : upper_bound S b0. (* a strict upper bound *)

(* implicit assumption : b^0 >w s^0 *)

Definition epsilon (n:A) (H:std (n+1) /\ 0 <=A (n+1)) := (power two_third (n+1) H) [*] (b0 [+] (-w s0)).

Definition fs := fun (alpha beta a b : HRw) (Ha:S a) (Hb : upper_bound S b) (Hab : (b [>=] beta /\ beta [>=] alpha /\ alpha [>=] a)) =>
 (* a actually is sn_1 *)
     match (Hdec a b alpha beta (conj Hb (conj Ha Hab))) with
      | inleft Hs => proj1_sig Hs
      | inright _ => a
      end.

Definition fb := fun (alpha beta a b : HRw) (Ha:S a) (Hb : upper_bound S b) 
                     (Hab : (b [>=] beta /\ beta [>=] alpha /\ alpha [>=] a)) (n:A) (H:std (n+1) /\ (0<=A (n+1))) =>
      match (Hdec a b alpha beta (conj Hb (conj Ha Hab))) with
 (* b actually is bn_1 *)
      | inleft Hs => (b [+] proj1_sig Hs) [+] (-w alpha) [+] (epsilon n H)
      | inright _ => beta [+] (epsilon n H)
      end.

Lemma HRw_n : forall (n : A), std n /\ 0 <=A n -> P (n * w).
Proof.
intros n (Hle, Hlim).
unfold P.
exists (n+1).
split.
apply ANS2a.
apply std_lim.
solve[assumption].
apply ANS1.
split.
setoid_replace 0 with (0+0) by ring.
apply le_lt_plus.
solve[assumption].
apply lt_0_1.
rewrite abs_pos_val.
setoid_replace (n * w) with (n * w + 0) by ring.
rewrite mult_distr_l.
apply le_plus.
apply le_refl.
ring_simplify; apply lt_le; apply Aw.
setoid_replace 0 with (n*0) by ring.
apply le_mult.
assumption.
apply lt_le; apply Aw.
Qed.

Definition mk_HRw : forall n:A, std n/\0<=A n -> HRw.
intros n Hn.
exists (n * w).
apply HRw_n; assumption.
Defined.

Lemma mk_HRw_HRw0 : forall H:std 0/\0<=A 0, mk_HRw 0 H [=] [0].
Proof.
intros.
unfold mk_HRw.
simpl.
intros.
rewrite abs_pos_val.
ring_simplify.
apply lt_le; apply Aw.
setoid_replace (0 + -0) with 0 by ring.
apply le_refl.
Qed.

Definition Psb n HlimH0 sn bn := 
S sn /\ upper_bound S bn /\ (bn [+] (-w sn)) [=] ((mk_HRw n HlimH0)[+] [1])[*](power two_third n HlimH0 [*] (b0 [+] (-w s0))).

Lemma lemma0 : forall Hx, Psb 0 Hx s0 b0.
Proof.
intros; unfold Psb.
split.
assumption.
split.
assumption.
rewrite mk_HRw_HRw0.
unfold power; rewrite nat_like_induction_r1.
setoid_replace (([0] [+] [1]) [*] ([1] [*] (b0 [+] (-w s0)))) with (b0 [+] (-w s0)) by ring.
reflexivity.
Qed.

Lemma mk_HRw_step : 
  forall (n:A) (H:std n /\ 0 <=A n) (Hx:std (n+1) /\ 0 <=A (n+1)), mk_HRw n H [+] [1] [=] mk_HRw (n+1) Hx.
Proof.
intros.
unfold mk_HRw; simpl; intros.
setoid_replace (n * w + w + - ((n + 1) * w)) with 0 by ring.
rewrite abs_pos_val.
ring_simplify; apply lt_le; apply Aw.
apply le_refl.
Qed.

Lemma lemma_step : forall
(n : A)
(H : std n /\ 0<=A n)
(X : forall Hx : std n /\ 0 <=A n, {sn : HRw & {bn : HRw & Psb n Hx sn bn}})
(Hx : std (n + 1) /\ 0 <=A (n + 1))
(sn_1 : HRw)
(bn_1 : HRw)
(HHsn : S sn_1)
(HHbn : upper_bound S bn_1)
(HHequal : bn_1 [+] (-w sn_1) [=]
          (mk_HRw n H [+] [1]) [*] (power two_third n H [*] (b0 [+] (-w s0))))
(alphan_1 := (two_third [*] sn_1) [+] (one_third [*] bn_1) : HRw)
(betan_1 := (one_third [*] sn_1) [+] (two_third [*] bn_1) : HRw)
(Hyp : bn_1 [>=] betan_1 /\ betan_1 [>=] alphan_1 /\ alphan_1 [>=] sn_1)
(sn := fs alphan_1 betan_1 sn_1 bn_1 HHsn HHbn Hyp : HRw)
(bn := fb alphan_1 betan_1 sn_1 bn_1 HHsn HHbn Hyp n Hx : HRw),
Psb (n + 1) Hx sn bn.
Proof.
intros; unfold sn, bn, fs, fb; simpl.
assert (Heps:(epsilon n Hx) [>] [0]).
unfold epsilon; apply R2_5.
split.
apply power_HRwgt.
apply two_third_prop.
apply HRwgt_HRwplus_inv_r with s0; ring_simplify.
apply Hb0S; apply Hs0. 

destruct (Hdec sn_1 bn_1 alphan_1 betan_1 (conj HHbn (conj HHsn Hyp))).
(* case 1 *)
split.
destruct s;simpl; solve[intuition].
split.
unfold upper_bound; intros.
eapply HRwgt_trans with (bn_1 [+]  epsilon n Hx).

repeat rewrite <- HRwplus_assoc.
apply R2_4.
repeat rewrite HRwplus_assoc.
rewrite HRwplus_comm.
setoid_replace bn_1 with ([0][+] bn_1) at 2 by ring.
apply R2_4.
eapply HRwgt_HRwplus_inv_r with (alphan_1).
ring_simplify.
destruct s; simpl; solve[intuition].
apply HRwgt_trans with bn_1.
setoid_replace bn_1 with (bn_1 [+] [0]) at 2 by ring.
rewrite HRwplus_comm.
rewrite (HRwplus_comm bn_1).
apply R2_4.
assumption.
apply HHbn; assumption.
setoid_replace ((((bn_1 [+] proj1_sig s) [+] (-w alphan_1)) [+] epsilon n Hx) [+] (-w proj1_sig s)) with
(((bn_1 [+] (-w alphan_1)) [+] epsilon n Hx)) by ring.
unfold alphan_1, epsilon.
rewrite (two_thirds_one_third bn_1) at 1.
setoid_replace (((two_third [*] bn_1) [+] (one_third [*] bn_1)) [+]
 (-w ((two_third [*] sn_1) [+] (one_third [*] bn_1)))) with (two_third [*] (bn_1 [+] -w sn_1)) by ring.
setoid_rewrite HHequal.
setoid_replace (two_third [*] ((mk_HRw n H [+] [1]) [*] (power two_third n H [*] (b0 [+] (-w s0))))) 
with ((mk_HRw n H [+] [1])[*] two_third [*] (power two_third n H [*] (b0 [+] (-w s0)))) by ring.
rewrite HRwmult_assoc.
rewrite (HRwmult_comm two_third).
setoid_replace ((power two_third n H [*] (b0 [+] (-w s0))) [*] two_third) 
  with ((power two_third (n+1) Hx) [*] (b0 [+] -w s0))
  by (unfold power; setoid_rewrite nat_like_induction_r2 with (H:=H); simpl; ring).
setoid_replace (power two_third (n + 1) Hx [*] (b0 [+] (-w s0))) 
  with ([1] [*] (power two_third (n + 1) Hx [*] (b0 [+] (-w s0)))) at 2 by ring.
rewrite (HRwmult_comm (mk_HRw n H [+] [1])).
rewrite (HRwmult_comm [1]).
rewrite <- HRw_distr.
rewrite (HRwmult_comm _ ((mk_HRw n H [+] [1]) [+] [1])).
rewrite mk_HRw_step with (Hx:=Hx).
reflexivity.

(* case 2 *)
split.
assumption.
split.
unfold upper_bound.
intros.
apply HRwgt_trans with betan_1.
setoid_replace betan_1 with (betan_1 [+] [0]) at 2 by ring.
rewrite (HRwplus_comm betan_1).
rewrite (HRwplus_comm betan_1).
apply R2_4.
apply Heps.
apply u; assumption.
unfold betan_1, alphan_1.
rewrite (two_thirds_one_third sn_1) at 2.
setoid_replace ((((one_third [*] sn_1) [+] (two_third [*] bn_1)) [+] epsilon n Hx) [+]
(-w ((two_third [*] sn_1) [+] (one_third [*] sn_1)))) 
  with ((two_third [*] (bn_1 [+] -w sn_1)) [+] epsilon n Hx) 
  by ring.
rewrite HHequal.
unfold epsilon.
rewrite (HRwmult_comm two_third).
repeat rewrite HRwmult_assoc.
rewrite (HRwmult_comm (b0 [+] -w s0)).
rewrite <- (HRwmult_assoc (power two_third n H)).
setoid_replace (power two_third n H [*] two_third) with (power two_third (n+1) Hx)
  by (unfold power; setoid_rewrite nat_like_induction_r2 with (H:=H); reflexivity).
rewrite mk_HRw_step with (Hx:=Hx).
ring.
Qed.

Lemma mk_Hyp : forall
(sn_1 : HRw)
(bn_1 : HRw)
(HHsn : S sn_1)
(HHbn : upper_bound S bn_1)
(alphan_1 := (two_third [*] sn_1) [+] (one_third [*] bn_1) : HRw)
(betan_1 := (one_third [*] sn_1) [+] (two_third [*] bn_1) : HRw),
 bn_1 [>=] betan_1 /\ betan_1 [>=] alphan_1 /\ alphan_1 [>=] sn_1.
Proof.
intros.
unfold betan_1, alphan_1.
split.
apply HRwgt_HRwge.
rewrite (two_thirds_one_third bn_1) at 1.
rewrite HRwplus_comm.
apply R2_4.
apply HRwgt_HRwplus_inv_r with (one_third [*] (-w sn_1)).
rewrite <- HRw_distr.
setoid_replace  ((one_third [*] sn_1) [+] (one_third [*] (-w sn_1))) with [0] by ring.
apply R2_5.
split.
apply HRwgt_one_third.
apply HRwgt_HRwplus_inv_l with sn_1.
ring_simplify.
apply HHbn; apply HHsn.

split.
apply HRwgt_HRwge; apply step_thirds; apply HHbn; apply HHsn.

rewrite (two_thirds_one_third sn_1) at 2.
rewrite (HRwplus_comm (two_third [*] sn_1)).
rewrite (HRwplus_comm (two_third [*] sn_1)).
apply HRwgt_HRwge.
apply R2_4.
apply HRwgt_HRwplus_inv_r with (one_third [*] (-w sn_1)).
rewrite <- HRw_distr.
setoid_replace  ((one_third [*] sn_1) [+] (one_third [*] (-w sn_1))) with [0] by ring.
apply R2_5.
split.
apply HRwgt_one_third.
apply HRwgt_HRwplus_inv_l with sn_1.
ring_simplify.
apply HHbn; apply HHsn.
Qed.

Definition def_s_b : 
    forall k:A, forall Hk:(std k /\ 0 <=A k), 
{sn:HRw & {bn:HRw & Psb k Hk sn bn}}.
Proof.
intros k HlimkH0k.
apply (nat_like_induction
 (fun (x:A) => (forall Hx:std x /\ 0<=A x, {sn:HRw & {bn:HRw & Psb x Hx sn bn}}))).
clear HlimkH0k k.
intros.
exists s0.
exists b0.
apply lemma0.
intros n H X Hx.
generalize (X H); intros (sn_1, (bn_1, (HHsn, (HHbn, HHequal)))). 
pose (alphan_1:=((two_third [*] sn_1)) [+] (one_third [*] bn_1)).
pose (betan_1:=((one_third [*] sn_1) [+] (two_third [*] bn_1))).
assert (Hyp:bn_1 [>=] betan_1 /\ betan_1 [>=] alphan_1 /\ alphan_1 [>=] sn_1) by (apply mk_Hyp; assumption).
(*
pose (sn:=fs alphan_1 betan_1 sn_1 bn_1 HHsn HHbn Hyp).
pose (bn:=fb alphan_1 betan_1 sn_1 bn_1 HHsn HHbn Hyp n Hx).
*)
exists (fs alphan_1 betan_1 sn_1 bn_1 HHsn HHbn Hyp).
exists (fb alphan_1 betan_1 sn_1 bn_1 HHsn HHbn Hyp n Hx).
(*clear Hs0 Hb0S HlimkH0k k;*) abstract (apply lemma_step with (n:=n) (H:=H); assumption). 
apply HlimkH0k.
Defined.

Lemma auxiliary_lemma : forall P, forall x:HRw , forall Hx, projT1 (existT P x Hx) = x.
Proof.
intros; simpl;reflexivity.
Qed.

Lemma s_increases_step : 
forall ssA, forall HssA : ssA = (fun k0 Hk0 => proj1_sig (projT1 (def_s_b k0 Hk0))),
forall bbA, forall HbbA : bbA = (fun k0 Hk0 => proj1_sig (projT1 (projT2 (def_s_b k0 Hk0)))),
forall n, forall Hn:std n/\0<=A n,  forall (Hn1:std (n+1)/\0<=A (n+1)), forall m,
   (ssA n Hn m  <= ssA (plusA n a1) Hn1 m)%Z.
Proof.
intros ssA HssA bbA HbbA n Hn.
rewrite HssA.
unfold def_s_b at 2.
intros.
rewrite nat_like_induction_r2 with (H:=Hn).
unfold def_s_b.

pose (NLI:= (nat_like_induction
         (fun x : A => forall Hx : std x /\ 0 <=A x, {sn : HRw & {bn : HRw & Psb x Hx sn bn}})
         (fun Hx : std 0 /\ 0 <=A 0 =>
          existT (fun sn : HRw => {bn : HRw & Psb 0 Hx sn bn}) s0
            (existT (fun bn : HRw => Psb 0 Hx s0 bn) b0 (lemma0 Hx)))
         (fun (n0 : A) (H : std n0 /\ 0 <=A n0)
            (X : forall Hx : std n0 /\ 0 <=A n0, {sn : HRw & {bn : HRw & Psb n0 Hx sn bn}})
            (Hx : std (plusA n0 1) /\ 0 <=A plusA n0 1) =>
          let (sn_1, s) := X H in
          let (bn_1, p) := s in
          match p with
          | conj HHsn (conj HHbn HHequal) =>
              existT (fun sn : HRw => {bn : HRw & Psb (plusA n0 1) Hx sn bn})
                (fs ((two_third [*] sn_1) [+] (one_third [*] bn_1))
                   ((one_third [*] sn_1) [+] (two_third [*] bn_1)) sn_1 bn_1 HHsn HHbn
                   (mk_Hyp sn_1 bn_1 HHsn HHbn))
                (existT
                   (fun bn : HRw =>
                    Psb (plusA n0 1) Hx
                      (fs ((two_third [*] sn_1) [+] (one_third [*] bn_1))
                         ((one_third [*] sn_1) [+] (two_third [*] bn_1)) sn_1 bn_1 HHsn HHbn
                         (mk_Hyp sn_1 bn_1 HHsn HHbn)) bn)
                   (fb ((two_third [*] sn_1) [+] (one_third [*] bn_1))
                      ((one_third [*] sn_1) [+] (two_third [*] bn_1)) sn_1 bn_1 HHsn HHbn
                      (mk_Hyp sn_1 bn_1 HHsn HHbn) n0 Hx)
                   (def_s_b_subproof n0 H X Hx sn_1 bn_1 HHsn HHbn HHequal
                      (mk_Hyp sn_1 bn_1 HHsn HHbn)))
          end) n Hn Hn)).

change (((proj1_sig
   (projT1 NLI)) m <= proj1_sig
   (projT1
      (let (sn_1, s) :=
           NLI in
      let (bn_1, p) := s in
       match p with
       | conj HHsn (conj HHbn HHequal) =>
           existT (fun sn : HRw => {bn : HRw & Psb (plusA n a1) Hn1 sn bn})
             (fs ((two_third [*] sn_1) [+] (one_third [*] bn_1))
                ((one_third [*] sn_1) [+] (two_third [*] bn_1)) sn_1 bn_1 HHsn HHbn
                (mk_Hyp sn_1 bn_1 HHsn HHbn))
             (existT
                (fun bn : HRw =>
                 Psb (plusA n a1) Hn1
                   (fs ((two_third [*] sn_1) [+] (one_third [*] bn_1))
                      ((one_third [*] sn_1) [+] (two_third [*] bn_1)) sn_1 bn_1 HHsn HHbn
                      (mk_Hyp sn_1 bn_1 HHsn HHbn)) bn)
                (fb ((two_third [*] sn_1) [+] (one_third [*] bn_1))
                   ((one_third [*] sn_1) [+] (two_third [*] bn_1)) sn_1 bn_1 HHsn HHbn
                   (mk_Hyp sn_1 bn_1 HHsn HHbn) n Hn1)
                (def_s_b_subproof n Hn
                   (nat_like_induction
                      (fun x : A =>
                       forall Hx : std x /\ a0 <=A x, {sn : HRw & {bn : HRw & Psb x Hx sn bn}})
                      (fun Hx : std a0 /\ a0 <=A a0 =>
                       existT 
                         (fun sn : HRw => {bn : HRw & Psb a0 Hx sn bn}) s0
                         (existT (fun bn : HRw => Psb a0 Hx s0 bn) b0 (lemma0 Hx)))
                      (fun (n0 : A) 
                         (H : std n0 /\ a0 <=A n0)
                         (X : 
                          forall Hx : std n0 /\ a0 <=A n0, 
                          {sn : HRw & {bn : HRw & Psb n0 Hx sn bn}})
                         (Hx : std (plusA n0 a1) /\ a0 <=A plusA n0 a1) =>
                       let (sn_0, s1) := X H in
                       let (bn_0, p0) := s1 in
                       match p0 with
                       | conj HHsn0 (conj HHbn0 HHequal0) =>
                           existT 
                           (fun sn : HRw => {bn : HRw & Psb (plusA n0 a1) Hx sn bn})
                           (fs 
                           ((two_third [*] sn_0) [+] (one_third [*] bn_0))
                           ((one_third [*] sn_0) [+] (two_third [*] bn_0)) sn_0 bn_0 HHsn0 HHbn0
                           (mk_Hyp sn_0 bn_0 HHsn0 HHbn0))
                           (existT
                           (fun bn : HRw =>
                           Psb 
                           (plusA n0 a1) Hx
                           (fs 
                           ((two_third [*] sn_0) [+] (one_third [*] bn_0))
                           ((one_third [*] sn_0) [+] (two_third [*] bn_0)) sn_0 bn_0 HHsn0 HHbn0
                           (mk_Hyp sn_0 bn_0 HHsn0 HHbn0)) bn)
                           (fb 
                           ((two_third [*] sn_0) [+] (one_third [*] bn_0))
                           ((one_third [*] sn_0) [+] (two_third [*] bn_0)) sn_0 bn_0 HHsn0 HHbn0
                           (mk_Hyp sn_0 bn_0 HHsn0 HHbn0) n0 Hx)
                           (def_s_b_subproof n0 H X Hx sn_0 bn_0 HHsn0 HHbn0 HHequal0
                            (mk_Hyp sn_0 bn_0 HHsn0 HHbn0)))
                       end) n Hn) Hn1 sn_1 bn_1 HHsn HHbn HHequal 
                   (mk_Hyp sn_1 bn_1 HHsn HHbn)))
       end)) m)%Z).

destruct NLI.
destruct s.
destruct p as[Hp1 [Hp2 Hp3]].
simpl (projT1 (existT (fun sn : HRw => {bn : HRw & Psb n Hn sn bn}) x (existT (fun bn : HRw => Psb n Hn x bn) x0 (conj Hp1 (conj Hp2 Hp3))))).
rewrite auxiliary_lemma.

unfold fs.
destruct (Hdec x x0 ((two_third [*] x) [+] (one_third [*] x0)) 
       ((one_third [*] x) [+] (two_third [*] x0)) 
       (conj Hp2 (conj Hp1 (mk_Hyp x x0 Hp1 Hp2)))).
destruct s as [s Hs].
simpl.
assert (Hsw : (s [>] x)).
assert (t:=two_thirds_one_third x).
setoid_rewrite t.
apply HRwgt_trans with ((two_third [*] x) [+] (one_third [*] x0)).
solve [intuition].
apply HRwgt_HRwplus_l.
apply HRw1_3.
apply Hp2; apply Hp1.
destruct s as [ss Hss].
destruct x as [xx Hxx].
unfold HRwgt in Hsw.
destruct Hsw as [v [Hv1 [Hv2 Hv3]]].
simpl.
assert (xx <=A ss).
apply le_plus_inv with (-xx).
apply le_mult_inv with v.
assumption.
apply le_trans with w.
ring_simplify.
apply lt_le; apply Aw.
assumption.
admit. (** to investigate, strange, is probably related to the construction of s... *)
apply Z.le_refl.
Admitted.


Lemma s_increases : 
forall ssA, forall HssA : ssA = (fun k0 Hk0 => proj1_sig (projT1 (def_s_b k0 Hk0))),
forall bbA, forall HbbA : bbA = (fun k0 Hk0 => proj1_sig (projT1 (projT2 (def_s_b k0 Hk0)))),
forall n, forall Hn:std n/\0<=A n, forall p, forall (Hp:std p/\0<=A p), forall m,
  n <=A p -> (ssA n Hn m  <= ssA p Hp m)%Z.
Proof.
intros ssA HssA bbA HbbA n Hn m Hm.
apply (nat_like_induction
  (fun x:A => forall Hx:std x/\ 0<=A x,forall p, 
  n <=A x -> (ssA n Hn p <= ssA x Hx p)%Z)).
intros.
assert (n=A 0) by (apply le_id; solve [intuition]).
Admitted. (* ok when shifting from lim to std : to check quickly, still requires dependent rewriting *)


End section_sequences.


End seq_LS.


