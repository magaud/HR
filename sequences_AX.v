Require Export LUB_spec_AX.

Module seq(N:Num_w).

Import N.
Module Export XX:=lub_spec_AX(N).

Section section_sequences.
Variable S : subset.
Variable Hdec : forall alpha beta : HRw,
       beta [>] alpha -> {s : HRw | S s /\ s [>] alpha} + {upper_bound S beta}.
Variables s0 b0 : HRw.
Variable Hs0 : S s0.
Variable Hb0S : upper_bound S b0.

Definition fs := fun (alpha beta : HRw) (Hab : beta [>] alpha) (sn_1 : HRw) =>
      match Hdec alpha beta Hab with
      | inleft Hs => proj1_sig Hs
      | inright _ => sn_1
      end.

Definition fb := fun (alpha beta : HRw) (Hab : beta [>] alpha) (bn_1 : HRw) =>
      match Hdec alpha beta Hab with
      | inleft Hs => (bn_1 [+] proj1_sig Hs) [+] (-w alpha)
      | inright _ => beta
      end.

Lemma s_b_alpha_beta_lemma : forall
(n : A)
(HlimH0 : std n /\ 0 <= n)
(sn : HRw)
(bn : HRw)
(Hbs : S sn /\ upper_bound S bn)
(alphan : HRw)
(betan : HRw)
(Habn : betan [>] alphan),
S (fs alphan betan Habn sn) /\ upper_bound S (fb alphan betan Habn bn).
Proof.
intros.
unfold fs,fb; simpl.
elim (Hdec alphan betan Habn).
intros a; case a; simpl.
intros x (HSx, Hxa).
split.
assumption. 
apply HRwgt_upper_bound_2 with bn.
abstract (solve [intuition]).
assert (Hr:(bn [+] (x [+] (-w alphan))) [=] ((bn [+] x) [+] (-w alphan))) by ring.
setoid_rewrite <- Hr.
setoid_replace bn with (bn[+] [0]) at 2 by ring.
apply HRwgt_HRwplus_l.
apply HRwgt_HRwplus_inv_r with alphan.
ring_simplify; assumption.
abstract (intros;solve [intuition]).
Qed.

Definition Psb n HlimH0 sn bn := 
S sn /\ upper_bound S bn /\ (bn [+] (-w sn)) [=] (power two_third n HlimH0 [*] (b0 [+] (-w s0))).

Lemma lemma : forall
(n : A)
(HlimH0 : std n /\ 0 <= n)
(alphan : HRw)
(betan : HRw)
(sn : HRw)
(bn : HRw)
(Hs : S sn)
(Hb : upper_bound S bn)
(Hpower : (bn [+] (-w sn)) [=] (power two_third n HlimH0 [*] (b0 [+] (-w s0))))
(Habn : betan [>] alphan)
(Halphan : alphan = ((two_third [*] sn) [+] (one_third [*] bn)))
(Hbetan : betan = ((one_third [*] sn) [+] (two_third [*] bn)))
(Hx0 : std (n + 1) /\ 0 <= (n + 1)),

S (fs alphan betan Habn sn) /\
upper_bound S (fb alphan betan Habn bn) /\
(fb alphan betan Habn bn [+] (-w fs alphan betan Habn sn)) [=]
(power two_third (n + 1) Hx0 [*] (b0 [+] (-w s0))). 
Proof.
intros.
assert (S (fs alphan betan Habn sn) /\
upper_bound S (fb alphan betan Habn bn)).

solve [eapply s_b_alpha_beta_lemma; eauto; intuition].
split. 
intuition.
split.
intuition.

unfold fs, fb; elim (Hdec alphan betan Habn).
intros a; elim a; intros sa Hsa; simpl.

setoid_rewrite Halphan.
ring_simplify.
unfold HRwminus; setoid_replace (((-w bn) [*] one_third) [+] bn) with (two_third [*] bn)
by (setoid_rewrite HRwplus_comm;setoid_rewrite (HRwmult_comm (-w bn)); setoid_rewrite <- HRwminus_one_third; ring_simplify; solve [trivial | apply HRwequal_refl]).
assert (Hr: ((two_third [*] bn) [+] (-w (two_third [*] sn)))[=](two_third [*] (bn [+] -w sn))) by ring.
setoid_rewrite Hr.
setoid_rewrite Hpower.
unfold power; rewrite nat_like_induction_r2 with (H:=HlimH0).
ring_simplify; unfold HRwminus.
apply HRwequal_refl.

intros Hup.
setoid_rewrite Hbetan. 
ring_simplify; unfold HRwminus.
assert (Hr:((one_third [*] sn) [+] (-w sn))[=] (-w two_third [*] sn)).
assert (Hr2:((-w two_third) [*] sn)[=](-w (two_third [*] sn))) by ring.
setoid_rewrite Hr2.
setoid_rewrite <- HRwminus_one_third; ring_simplify; solve [trivial | apply HRwequal_refl]. 
setoid_rewrite Hr.
assert (Hr2:(((-w two_third) [*] sn) [+] (two_third [*] bn))[=](two_third [*] (bn [+] -w sn))) by ring.
setoid_rewrite Hr2.
setoid_rewrite Hpower.
unfold power; rewrite nat_like_induction_r2 with (H:=HlimH0).
ring_simplify; unfold HRwminus.
apply HRwequal_refl.
Qed.

Definition def_s_b_alpha_beta : 
    forall k:A, forall Hk:(std k /\ 0 <= k), 
{sn:HRw & {bn:HRw & Psb k Hk sn bn}}.
Proof.
intros k HlimkH0k.
apply (nat_like_induction
 (fun (x:A) => (forall Hx:std x /\ 0<=x, {sn:HRw & {bn:HRw & Psb x Hx sn bn}}))).
clear HlimkH0k k.
intros.
exists s0.
exists b0.

abstract ( 
split; [assumption |idtac];
split; [assumption |idtac];
unfold power; rewrite nat_like_induction_r1; ring
) using aproof1.

clear HlimkH0k k.
intros n HlimH0 Hx.

generalize (Hx HlimH0) ; clear Hx.
intros 
 (sn,(bn, (Hs, (Hb,Hpower)))).

pose (alphan:=((two_third [*] sn)) [+] (one_third [*] bn)).
pose (betan:=((one_third [*] sn) [+] (two_third [*] bn))).

assert (Habn: betan [>] alphan) by (clear HlimH0 Hpower; abstract (apply step_thirds; intuition) using aproof2).

exists (* sn+1 *) (fs alphan betan Habn sn).
exists (* bn+1 *) (fb alphan betan Habn bn).
abstract (eapply lemma; eapply Hpower || intuition) using aproof3.

apply HlimkH0k.
Defined.

Lemma Hsn_increasing_aux : 
forall ssA, forall HssA : ssA = (fun k0 Hk0 =>  proj1_sig(projT1 (def_s_b_alpha_beta k0 Hk0))),
forall bbA, forall HbbA : bbA = (fun k0 Hk0 => proj1_sig (projT1 (projT2 (def_s_b_alpha_beta k0 Hk0)))),
forall n, forall Hn, forall Hn1,  ssA n Hn <= ssA (n+1) Hn1.
Proof.
intros ssA HssA bbA HbbA n Hn.
rewrite HssA.
unfold def_s_b_alpha_beta at 2.
intros.
rewrite nat_like_induction_r2 with (H:=Hn).
unfold def_s_b_alpha_beta.

pose (NLI :=
(nat_like_induction
        (fun x : A =>
         forall Hx : std x /\ 0 <= x, {sn : HRw & {bn : HRw & Psb x Hx sn bn}})
        (fun Hx : std 0 /\ 0 <= 0 =>
         existT (fun sn : HRw => {bn : HRw & Psb 0 Hx sn bn}) s0
           (existT (fun bn : HRw => Psb 0 Hx s0 bn) b0 (aproof1 Hx)))
        (fun (n0 : A) (HlimH0 : std n0 /\ 0 <= n0)
           (Hx : forall Hx : std n0 /\ 0 <= n0,
                 {sn : HRw & {bn : HRw & Psb n0 Hx sn bn}}) =>
         let (sn, s) := Hx HlimH0 in
         let (bn, p) := s in
         match p with
         | conj Hs (conj Hb Hpower) =>
             fun Hx0 : std (n0 + 1) /\ 0 <= n0 + 1 =>
             existT (fun sn0 : HRw => {bn0 : HRw & Psb (n0 + 1) Hx0 sn0 bn0})
               (fs ((two_third [*] sn) [+] (one_third [*] bn))
                  ((one_third [*] sn) [+] (two_third [*] bn))
                  (aproof2 sn bn Hs Hb) sn)
               (existT
                  (fun bn0 : HRw =>
                   Psb (n0 + 1) Hx0
                     (fs ((two_third [*] sn) [+] (one_third [*] bn))
                        ((one_third [*] sn) [+] (two_third [*] bn))
                        (aproof2 sn bn Hs Hb) sn) bn0)
                  (fb ((two_third [*] sn) [+] (one_third [*] bn))
                     ((one_third [*] sn) [+] (two_third [*] bn))
                     (aproof2 sn bn Hs Hb) bn)
                  (aproof3 n0 HlimH0 sn bn Hs Hb Hpower
                     (aproof2 sn bn Hs Hb) Hx0))
         end) n Hn Hn)).

change (
(proj1_sig
  (projT1
     NLI) <=
proj1_sig
  (projT1
     ((let (sn, s) := NLI in
       let (bn, p) := s in
       match p with
       | conj Hs (conj Hb Hpower) =>
           fun Hx : std (n + 1) /\ 0 <= n + 1 =>
           existT (fun sn0 : HRw => {bn0 : HRw & Psb (n + 1) Hx sn0 bn0})
             (fs ((two_third [*] sn) [+] (one_third [*] bn))
                ((one_third [*] sn) [+] (two_third [*] bn))
                (aproof2 sn bn Hs Hb) sn)
             (existT
                (fun bn0 : HRw =>
                 Psb (n + 1) Hx
                   (fs ((two_third [*] sn) [+] (one_third [*] bn))
                      ((one_third [*] sn) [+] (two_third [*] bn))
                      (aproof2 sn bn Hs Hb) sn) bn0)
                (fb ((two_third [*] sn) [+] (one_third [*] bn))
                   ((one_third [*] sn) [+] (two_third [*] bn))
                   (aproof2 sn bn Hs Hb) bn)
                (aproof3 n Hn sn bn Hs Hb Hpower (aproof2 sn bn Hs Hb) Hx))
       end) Hn1))
)).
destruct NLI.
destruct s.
destruct p.
destruct a.

replace 
  (projT1
     (existT (fun sn : HRw => {bn : HRw & Psb n Hn sn bn}) x
        (existT (fun bn : HRw => Psb n Hn x bn) x0 (conj s (conj u h))))) with x by auto.

replace
(projT1
     (existT (fun sn0 : HRw => {bn0 : HRw & Psb (n + 1) Hn1 sn0 bn0})
        (fs ((two_third [*] x) [+] (one_third [*] x0))
           ((one_third [*] x) [+] (two_third [*] x0)) (aproof2 x x0 s u) x)
        (existT
           (fun bn0 : HRw =>
            Psb (n + 1) Hn1
              (fs ((two_third [*] x) [+] (one_third [*] x0))
                 ((one_third [*] x) [+] (two_third [*] x0)) (aproof2 x x0 s u)
                 x) bn0)
           (fb ((two_third [*] x) [+] (one_third [*] x0))
              ((one_third [*] x) [+] (two_third [*] x0)) (aproof2 x x0 s u) x0)
           (aproof3 n Hn x x0 s u h (aproof2 x x0 s u) Hn1))))
with
(fs ((two_third [*] x) [+] (one_third [*] x0))
           ((one_third [*] x) [+] (two_third [*] x0)) (aproof2 x x0 s u) x)
by auto.

unfold fs.
destruct (Hdec ((two_third [*] x) [+] (one_third [*] x0))
      ((one_third [*] x) [+] (two_third [*] x0)) (aproof2 x x0 s u)).
generalize s1; intros (sn1, (hsn1a,hsn1b)).
simpl.
assert (sn1 [>] x).
assert (t:=two_thirds_one_third x).
setoid_rewrite t.
eapply HRwgt_trans.
apply hsn1b.
setoid_rewrite (HRwplus_comm (two_third [*] x)).
apply R2_4.
apply HRw1_3.
apply u; apply s.
apply lt_le; apply HRwgt_Zgt; assumption.
apply le_refl.
Qed.

Definition Q:A-> Prop := fun (a:A) => std a /\ leA a0 a.

Instance Q_morph : Proper (equalA ==> Basics.impl) Q.
Proof.
repeat red.
unfold Q.
intros x y Heq H'.
destruct H'.
split; rewrite <- Heq; assumption.
Qed.

Definition R: forall ssA:forall a, Q a->A, forall x, forall a, Q a->Prop :=
fun (ssA:forall a, Q a->A) (x:A) (a:A) (h:Q a) => leA (ssA a h) x.

Definition allDep (Q: A -> Prop) (R:forall x, forall a, Q a->Prop) (x:A) (a:A):=
 forall p:(Q a), (R x a p).

Parameter ssA_args_id :
  forall ssA:forall a, Q a->A, (forall x y, equalA x y -> forall p:Q x, forall q:Q y, equalA (ssA x p) (ssA y q)).
Check ssA_args_id.
(* proving this would require dependent rewriting : *)
(* Error: build_signature: no constraint can apply on a dependent argument *)

(*
Lemma ssA_args_id' :
  forall ssA:forall a, Q a->A, forall HssA : ssA = (fun k0 Hk0 => proj1_sig (projT1 (def_s_b_alpha_beta k0 Hk0))),(forall x y, equalA x y -> forall p:Q x, forall q:Q y, equalA (ssA x p) (ssA y q)).
Proof.
intros.
rewrite HssA.
destruct (def_s_b_alpha_beta x p) as [s_x [b_x Hx]].
destruct (def_s_b_alpha_beta y q) as [s_y [b_y Hy]].
destruct s_x.
destruct s_y.

simpl.
unfold Psb in Hx,Hy.
assert  (S (exist (fun x1 : A => P x1) x0 p0) /\
     upper_bound S b_x /\ forall p:(std x /\ 0<=x), b_x [+] (-w exist (fun x1 : A => P x1) x0 p0) =w power two_third x p [*] (b0 [+] (-w s0))).
admit. (* in a comment *)
assert  (S (exist (fun x1 : A => P x1) x1 p1) /\
     upper_bound S b_x /\ forall q:(std y /\ 0<=y), b_x [+] (-w exist (fun x1 : A => P x1) x0 p0) =w power two_third y q [*] (b0 [+] (-w s0))).
admit. (* in a comment *)
decompose [and] H1.
decompose [and] H2.
rewrite H in H6.
unfold def_s_b_alpha_beta.
simpl.
*)

Instance allDep_morph (ssA:forall a, Q a->A)(* (Q: A -> Prop) (R:forall x, forall a, Q a->Prop)*)(v:A) : Proper (equalA ==> iff) (@allDep Q (R ssA) v).
Proof.
repeat red; unfold allDep, R.
intros x y H.
split.
intros.
assert (Q x) by (rewrite H; assumption).
rewrite <- (ssA_args_id ssA x y H).
eapply H1.

unfold allDep ,R; intros.
assert (Q y) by (rewrite <- H; assumption).
rewrite (ssA_args_id ssA).
eapply H1.
assumption.
Existential 1:= H2.
Existential 1 := H2.
Qed.

Lemma thm_Hsn_increasing : 
forall ssA, forall HssA : ssA = (fun k0 Hk0 => proj1_sig (projT1 (def_s_b_alpha_beta k0 Hk0))),
forall bbA, forall HbbA : bbA = (fun k0 Hk0 => proj1_sig (projT1 (projT2 (def_s_b_alpha_beta k0 Hk0)))),
forall n, forall Hn:std n/\0<= n, forall m, forall (Hm:std m/\0<= m), 
  m <= n -> ssA m Hm <= ssA n Hn.
Proof.
intros ssA HssA bbA HbbA n Hn m Hm.
apply (nat_like_induction
  (fun x:A => forall Hx:std x/\ 0<=x,
  m <= x -> ssA m Hm <= ssA x Hx)).
intros.
assert (m==0) by (apply le_id; solve [intuition]).
generalize Hm.
assert (HallDep: (allDep Q (R ssA) (ssA 0 Hx) m)).
rewrite H1.
unfold allDep, Q, R; intros.
rewrite (proof_irr _ Hx p).
apply le_refl.
apply HallDep.
intros n0 Hn0 IH Hx Hmn0.
(* here we actually know that  m <= n0+1, *)
assert (Hstd:std (m + - (n0+1))).
apply ANS2a'.
apply Hm.
apply ANS2a_minus.
apply ANS2a'.
apply Hn0.
apply ANS1'.

elim (std_A0_dec (m + - (n0+1)) Hstd). (* occurs in thm_Hsn_increasing, because we need m <= n0 \/ m=n0+1 from  m <= n0+1 *)
intros Hdec'; elim Hdec'.
intros.
apply le_trans with (ssA n0 Hn0).
assert (m<= n0).
apply le_plus_inv with (- (n0+1) +1).
rewrite plus_assoc.
setoid_replace (n0 + (-(n0+1) +1)) with 0 by ring.
apply lt_le_2.
assumption.
apply IH.
assumption.
apply Hsn_increasing_aux with (bbA:=bbA); solve [assumption].

intros.
assert (m==n0+1).
setoid_replace (n0+1) with (0+(n0+1)) by ring.
setoid_replace m with ((m + - (n0 + 1)) + (n0 +1 )) by ring.
rewrite b.
reflexivity.

generalize Hm.
assert (HallDep: (allDep Q (R ssA) (ssA (n0+1) Hx) m)).
rewrite H.
unfold allDep, Q, R; intros.
rewrite (proof_irr _ Hx p).
apply le_refl.
apply HallDep.

intros.
assert (Hf:False).
apply contradict_lt_le with (s:=0) (x:=m + - (n0+1)).
assumption.
apply le_plus_inv with (n0+1).
ring_simplify.
assumption.
solve [intuition]. 
assumption.
Qed.

End section_sequences.

End seq.
