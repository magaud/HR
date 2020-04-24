Require Export sequences_LS.
Require Export ZArith_dec.
Require Export Recdef.

Module lub_proof_LS.

Module Export UU := seq_LS.

Import LSw.

Definition max_natlist (l:list nat) := fold_right Max.max 0%nat l.

Lemma max_natlist_biggest : forall u l , In u l -> u<= max_natlist l.
Proof.
induction l.
intros HH; inversion HH.
intros HH; destruct HH. 
intros; subst.
simpl.
apply Max.le_max_l.
simpl.
apply Coq.Arith.Le.le_trans with (max_natlist l).
apply IHl; assumption.
apply Max.le_max_r. 
Qed.

(*
Definition mk_list (a:A) : lim a /\ (0<=A a) -> list A.
intros.
apply (nat_like_induction (fun (_:A) => list A)) with (n:=a).
exact (cons a0 nil).
intros n Hn rec.
exact (cons (n+1) rec).
assumption.
Defined.

Lemma mk_r1 : forall (H:lim a0/\0<=A a0), mk_list (a0) H = cons a0 nil.
intros.
unfold mk_list.
rewrite (nat_like_induction_r1).  
reflexivity.
Qed.

Lemma mk_r2 : forall n, forall (H:lim n/\0<=A n), forall (H':lim (n+1)/\0<=A (n+1)), 
mk_list (n+1) H' = (n+1)::mk_list n H.
Proof.
intros.
unfold mk_list.
rewrite nat_like_induction_r2 with (H:=H).
reflexivity.
Qed.
*)

Definition steps : forall X Y:A->Prop, (forall k:A,  X k -> Y k) ->  list {k:A| X k} ->  list {k:A| Y k}.
intros X Y HXY l.
eapply (@map ( {k : A | X k})).
intros p(*; destruct p as [x Hx]*).
exists (proj1_sig p).
apply HXY.
clear l HXY Y; abstract (destruct p; assumption).
exact l.
Defined.

(*
Definition mk_list2 (a:A) : lim a /\ (0<=A a) -> list {k : A | (lim k /\ 0 <=A k) /\ k <=A (a + 1)}.
intros.
apply (nat_like_induction (fun (a:A) => list {k : A | (lim k /\ 0 <=A k) /\ k <=A (a + 1)})) with (n:=a).
refine (cons _ nil).
exists a0.
split.
split.
apply lim0.
apply le_refl.
setoid_replace 0 with (0+0) at 1 by ring.
apply le_plus.
apply le_refl.
apply lt_le; apply lt_0_1.

intros n Hn rec.
assert (rec':list {k : A | (lim k /\ 0 <=A k) /\ k <=A (n + 1+1)}).
apply steps with (X:=(fun k => (lim k /\ 0 <=A k) /\ k <=A (n + 1)))
(Y:= fun k => (lim k /\ 0 <=A k) /\ k <=A (n + 1 + 1)).
intros k (Ha1,Ha2). 
split.
assumption.
setoid_replace k with (k+0) by ring.
apply le_plus.
assumption.
apply lt_le; apply lt_0_1.
exact rec.

refine (cons _ rec').
exists (n+1).
split.
split.
apply ANS2a.
intuition.
apply ANS1.
setoid_replace 0 with (0+0) by ring.
apply le_plus.
intuition.
apply lt_le; apply lt_0_1.
setoid_replace (n+1) with ((n+1)+0) at 1 by ring.
apply le_plus.
apply le_refl.
apply lt_le; apply lt_0_1.
assumption.
Qed.
*)

Lemma mk_list2_aux1 : forall n k : A, (std k /\ 0 <=A k) /\ k <=A n -> (std k /\ 0 <=A k) /\ k <=A (n + 1).
Proof.
intros n k (Ha1,Ha2).
split ; [ assumption |
setoid_replace k with (k+0) by ring; 
apply le_plus; [
assumption |
apply lt_le; apply lt_0_1]].
Qed.

Lemma mk_list2_aux2 : forall n, (std n /\ 0<=A n) -> (std (n + 1) /\ 0 <=A (n + 1)) /\ (n + 1) <=A (n + 1).
Proof.
intros n Hn.
abstract (repeat split;
[apply ANS2a'; try apply ANS1'; solve[intuition]
| setoid_replace 0 with (0+0) by ring; apply le_plus; (solve [intuition] || apply lt_le; apply lt_0_1)
|apply le_refl
]).
Qed.

Definition mk_list2' (a:A) : std a /\ (0<=A a) -> list {k : A | (std k /\ 0 <=A k) /\ k <=A (a)}.
(* builds the list [0 ..i .. a ] with each time a proof of lim i /\ 0<=A i /\ i <=A a *)
intros.
apply (nat_like_induction (fun (a:A) => list {k : A | (std k /\ 0 <=A k) /\ k <=A a })) with (n:=a).
refine (cons _ nil).
exists a0.
 (repeat split; apply std0 || apply le_refl).

intros n Hn rec.
apply cons.
 
exists (n+1).
apply (mk_list2_aux2 n Hn).

apply steps with (X:=(fun k => (std k /\ 0 <=A k) /\ k <=A n ))
(Y:= fun k => (std k /\ 0 <=A k) /\ k <=A (n + 1)).
apply mk_list2_aux1. 
exact rec.

assumption.
Defined.

(*
Lemma mk_list2_prop : 
  forall n, forall Hn:  lim n/\0<=A n, forall p,  In p  (mk_list2' n Hn) -> 0 <=A (proj1_sig p) /\ (proj1_sig p) <=A n.
Proof.
intros n Hn p.
assert (Hn': lim n /\ 0 <=A n).
assumption.
revert p Hn.
apply (nat_like_induction (fun (n:A) => forall (p: {k : A | (lim k /\ 0 <=A k) /\ k <=A n}), forall (Hn:lim n/\0<=A n), In p (mk_list2' n Hn) -> 0 <=A proj1_sig p /\ proj1_sig p <=A n)).
intros p Hn.
unfold mk_list2'.
rewrite nat_like_induction_r1.
simpl; intros Hp.
destruct Hp as [Hp | Hf].
subst; simpl.
split; apply le_refl.
destruct Hf.
intros p Hp HRp X Hp1.
unfold mk_list2'; rewrite nat_like_induction_r2  with (H:=Hp).
simpl; intros.
destruct H as [HA | HB].
subst; simpl.
split; [solve [intuition] | apply le_refl].
apply HRp.
des
simpl.
simpl.

*)


(** seq_of_Ms ssA bbA (n+1) produces the sequences M_{n+1}^0 to M_{n+1}^{n+1} *)

Definition seq_of_Ms : forall
(ssA:forall k0 : A, std k0 /\ 0 <=A k0 -> A)
(bbA:forall k0 : A, std k0 /\ 0 <=A k0 -> A)
(n : A)
(Hn : std n  /\ 0 <=A n)
(*(Hn1: lim (n+1) /\ 0<=A (n+1))*)
(Mn1 
    : forall (k : A) (Hk : std k /\ 0 <=A k),
      k <=A (n) -> {N : nat | forall m : nat, m >= N -> (ssA n Hn m < bbA k Hk m)%Z}),
list nat.
Proof.
intros ssA bbA n Hn (*Hn1*) Mn1.
apply (@map {k : A | (std k /\ 0 <=A k) /\ k <=A (n)} nat).
intros K.
case K; intros k Hk.
case Hk; intros Hk1 Hk2.
Check (Mn1 k Hk1 Hk2) .
exact (proj1_sig (Mn1 k Hk1 Hk2)).
apply mk_list2'.
assumption.
Defined.

Definition nat2A : nat -> {n:A | std n /\ 0<=A n}.
Proof.
fix nat2A 1.
intros n; case n.
exists a0.
clear nat2A n; abstract (split; [apply std0 | apply le_refl]).
intros p. 
case (nat2A p).
intros xp Hxp.
exists (xp+a1).
clear nat2A n p;
abstract (split; [apply ANS2a'; [intuition | apply ANS1']| setoid_replace 0 with (0+0) by ring; apply le_plus; [intuition| apply lt_le;apply lt_0_1]]).
Defined.

(* adapting power_lim to take into account (k+1) when computing b^n - s^n *)

Axiom power_lim2
     : forall x : HRw,
       x [>] [0] ->
       [1] [>] x ->
       forall a : HRw,
       a [>] [0] ->
       forall eps : HRw,
       eps [>] [0] -> exists n : A, std n /\ 0 <=A n /\ (forall H : std n /\ 0 <=A n, eps [>] (a [*] ((mk_HRw n H)[+] [1]) [*] power x n H)).

Lemma std_n_n1
     : forall n : A,
       std n /\ 0 <=A n ->
       std (n + 1) /\ 0 <=A (n + 1).
Proof.
intros n Hn.
split.
apply ANS2a'.
apply Hn.
apply ANS1'.
setoid_replace 0 with (0+0) by ring.
apply le_plus.
apply Hn.
apply lt_le; apply lt_0_1.
Qed.

Definition def_bigM : forall
(ssA : forall k0 : A, std k0 /\ 0 <=A k0 -> A)
(bbA : forall k0 : A, std k0 /\ 0 <=A k0 -> A)
(M : forall (n : A) (Hn : std n /\ 0 <=A n) (k : A) (Hk : std k /\ 0 <=A k),
    k <=A n -> {N : nat | forall m : nat, m >= N -> (ssA n Hn m < bbA k Hk m)%Z}),
{n:A| std n /\ 0<=A n} ->  nat.
intros ssA bbA M.
intros (n, Hn).
apply (nat_like_induction (fun (_:A) =>  nat)) with (n:=n).
pose (H:= (M 0 (conj std0 (le_refl 0)) 0 (conj std0 (le_refl 0)) (le_refl 0))).
exact (proj1_sig H).
intros p Hp bigM_p.

(* seq_of_Ms builds the list [ M_{p+1}^{0} .. M_{p+1}^{p+1} *)
(* bigM_p, to which we add + 1 *) 
exact (Max.max (bigM_p+1)%nat (max_natlist ( seq_of_Ms ssA bbA (p+1) (std_n_n1 p Hp) (M (p+1) (std_n_n1 p Hp))))).
assumption.
Defined.

Definition pack : forall n, forall Hn : std n /\ 0<=A n, {n| std n /\ 0<=A n}.
intros n Hn. 
exists n.
assumption.
Defined.

Lemma bigM_fst_is_OK :
forall 
(ssA : forall k0 : A, std k0 /\ 0 <=A k0 -> A)
(bbA : forall k0 : A, std k0 /\ 0 <=A k0 -> A)
(M : forall (n : A) (Hn : std n /\ 0 <=A n) (k : A) (Hk : std k /\ 0 <=A k),
    k <=A n -> {N : nat | forall m : nat, m >= N -> (ssA n Hn m < bbA k Hk m)%Z})
(n : A)
(Hn:std n /\ 0<=A n)
(Hn':std n/\0<=A n)
(p: A)
(Hp : std p/\0<=A p)
(p':A)
(Hp':std p'/\0<=A p')
(Hle: p<=A n)
(Hle':p'<=A n)
(Heq:p=A p'),
proj1_sig (M n Hn p Hp Hle) = proj1_sig (M n Hn' p' Hp' Hle').
Proof.
Admitted. (* proof irrelevance and dependent rewriting *)

(*
Lemma In_transp : 
forall 
(ssA : forall k0 : A, lim k0 /\ 0 <=A k0 -> A)
(bbA : forall k0 : A, lim k0 /\ 0 <=A k0 -> A)
(M : forall (n : A) (Hn : lim n /\ 0 <=A n) (k : A) (Hk : lim k /\ 0 <=A k),
    k <=A n -> {N : nat | forall m : nat, m >= N -> (ssA n Hn m < bbA k Hk m)%Z})
(n : A)
(Hn:lim n /\ 0<=A n)
(p :  {k : A | (lim k /\ 0 <=A k) /\ k <=A n}),
In p (mk_list2' n Hn) -> {k:A | In (M n Hn k Hk) (seq_of_Ms ssA bbA n Hn (M n Hn))}.
*)

Lemma bigM_bigger : forall 
(ssA : forall k0 : A, std k0 /\ 0 <=A k0 -> A)
(bbA : forall k0 : A, std k0 /\ 0 <=A k0 -> A)
(M : forall (n : A) (Hn : std n /\ 0 <=A n) (k : A) (Hk : std k /\ 0 <=A k),
    k <=A n -> {N : nat | forall m : nat, m >= N -> (ssA n Hn m < bbA k Hk m)%Z})
(n : A)
(Hn:std n /\ 0<=A n)
(p: A)
(Hp : std p/\0<=A p)
(Hle: p<=A n),
  proj1_sig (M n Hn p Hp Hle) <= def_bigM ssA bbA M (pack n Hn).
Proof.
Admitted.

(*
intros ssA bbA M n Hn p Hp Hle.
revert Hn Hle.
unfold def_bigM.
intros Hn Hle.
assert (Hn2: lim n /\ 0 <=A n).
assumption.
revert Hn Hle.
apply (nat_like_induction (fun (n:A) => forall (Hn : lim n /\ 0 <=A n) (Hle : p <=A n),def_bigM ssA bbA M (pack n Hn) >= proj1_sig (M n Hn p Hp Hle))).
intros.
unfold pack, def_bigM.
rewrite nat_like_induction_r1.
assert (Heq:0=Ap).
apply le_id; solve[intuition].
rewrite <- (bigM_fst_is_OK ssA bbA M 0 (conj lim0 (le_refl 0)) Hn 0 (conj lim0 (le_refl 0)) p Hp (le_refl 0) Hle Heq).
omega.

intros m Hm Hn' Hle' Hle''.
unfold pack, def_bigM.
rewrite nat_like_induction_r2 with (H:=Hm).
assert (Hab:forall a b, a<=b -> b>=a) by (intros;omega).
apply Hab.

apply Le.le_trans with (max_natlist (seq_of_Ms ssA bbA (plusA m a1) (lim_n_n1 m Hm) (M (plusA m a1) (lim_n_n1 m Hm))))%nat.
apply max_natlist_biggest.
unfold seq_of_Ms.
unfold mk_list2'.
apply Max.le_max_r.
assumption.
Qed.
Show 2.
2:symmetry;eassumption.
revert Hle Hn.

Check (bigM_fst_is_OK ssA bbA M 0 (conj lim0 (le_refl 0))). Hn 0 (conj lim0 (le_refl 0)) Hp). with (Hn':=Hn) (Hp':= Hp) (Hle':=Hle).
assert (Heq:p=A 0).
apply le_id; solve[intuition].
setoid_rewrite Heq.

se
rewrite <- (proof_irr _ Hn (conj lim0 (le_refl 0))).
rewrite 
destruct (M 0 (conj lim0 (le_refl 0)) 0 (conj lim0 (le_refl 0)) (le_refl 0)).
destruct (M 0 Hn p Hp Hle).
simpl.
destruct (M 0 (conj lim0 (le_refl 0)) 0 
         (conj lim0 (le_refl 0)) 
         (le_refl 0)).
simpl.
rewrite nat_like_induction_r1.
unfold def_bigM.
*)

Lemma bigM_increases_step : forall 
(ssA : forall k0 : A, std k0 /\ 0 <=A k0 -> A)
(bbA : forall k0 : A, std k0 /\ 0 <=A k0 -> A)
(M : forall (n : A) (Hn : std n /\ 0 <=A n) (k : A) (Hk : std k /\ 0 <=A k),
    k <=A n -> {N : nat | forall m : nat, m >= N -> (ssA n Hn m < bbA k Hk m)%Z})
(n : A)
(Hn:std n /\ 0<=A n)
(Hn1 : std (n+1)/\0<=A (n+1)), 
  def_bigM ssA bbA M (pack n Hn) < def_bigM ssA bbA M (pack (n+1) Hn1).
Proof.
intros.
simpl.
rewrite (nat_like_induction_r2) with(H:=Hn).

change ( 
def_bigM ssA bbA M (pack n Hn) <
Max.max
  (nat_like_induction (fun _ : A => nat)
     (let (M0, _) := M 0 (conj std0 (le_refl 0)) 0 (conj std0 (le_refl 0)) (le_refl 0) in M0)
     (fun (p : A) (Hp : std p /\ 0 <=A p) (bigM_p : nat) =>
      Max.max (bigM_p + 1) (max_natlist (seq_of_Ms ssA bbA (p + 1) (std_n_n1 p Hp) (M (p + 1) (std_n_n1 p Hp))))) n
     Hn + 1) (max_natlist (seq_of_Ms ssA bbA (n + 1) (std_n_n1 n Hn) (M (n + 1) (std_n_n1 n Hn))))).
change (
def_bigM ssA bbA M (pack n Hn) <
Max.max (def_bigM ssA bbA M (pack n Hn)+1) (max_natlist (seq_of_Ms ssA bbA (n + 1) (std_n_n1 n Hn) (M (n + 1) (std_n_n1 n Hn))))).
apply Coq.Arith.Lt.lt_le_trans with (def_bigM ssA bbA M (pack n Hn) + 1)%nat.
omega.
apply Max.le_max_l.
Qed.

Lemma bigM_increases : forall 
(ssA : forall k0 : A, std k0 /\ 0 <=A k0 -> A)
(bbA : forall k0 : A, std k0 /\ 0 <=A k0 -> A)
(M : forall (n : A) (Hn : std n /\ 0 <=A n) (k : A) (Hk : std k /\ 0 <=A k),
    k <=A n -> {N : nat | forall m : nat, m >= N -> (ssA n Hn m < bbA k Hk m)%Z}),
(forall x y : {n : A | std n /\ 0 <=A n},
  proj1_sig x <A proj1_sig y -> def_bigM ssA bbA M x < def_bigM ssA bbA M y).
Proof.
Admitted. (* bigM_increases *)

Lemma bigM_increases2 : forall 
(ssA : forall k0 : A, std k0 /\ 0 <=A k0 -> A)
(bbA : forall k0 : A, std k0 /\ 0 <=A k0 -> A)
(M : forall (n : A) (Hn : std n /\ 0 <=A n) (k : A) (Hk : std k /\ 0 <=A k),
    k <=A n -> {N : nat | forall m : nat, m >= N -> (ssA n Hn m < bbA k Hk m)%Z}),
(forall x y : {n : A | std n /\ 0 <=A n},
  proj1_sig x <=A proj1_sig y -> def_bigM ssA bbA M x <= def_bigM ssA bbA M y).
Proof.
Admitted. (* bigM_increases2 *)

Lemma lt_le_dec : forall n m : nat, {n < m} + {m <= n}.
Proof.
intros.
destruct (lt_dec n m).
left; omega.
right; omega.
Qed.

Lemma nat2A_1 : forall i, (proj1_sig (nat2A i) <A proj1_sig (nat2A (i + 1))).
Proof.
intros.
setoid_replace (i+1)%nat with (S i)%nat by ring.
induction i.
simpl.
setoid_replace 0 with (0+0) at 1 by ring.
apply le_lt_plus.
apply le_refl.
apply lt_0_1.
simpl.
destruct (nat2A i).
simpl.
setoid_replace (x+1) with (x+1+0) at 1 by ring.
apply le_lt_plus.
apply le_refl.
apply lt_0_1.
Qed.



Section def_rec.
Variable u: {n : A | std n /\ 0 <=A n} -> nat.
Variable u_increases : (forall (x y : {n : A | std n /\ 0 <=A n}), (proj1_sig x) <A (proj1_sig y) -> u x < u y).

Definition my_measure (mi:nat*nat) : nat := (fst mi)-(u (nat2A (snd mi))). 

(*
Function computation (mi:nat*nat) {measure my_measure} : nat :=
match mi with (m,i) => 
if (lt_dec m (u (nat2A (i+1)))) then i else computation (m,(i+1)%nat) end.
intros.
unfold my_measure, my_measure'.
assert (u (nat2A (i + 1)) > u (nat2A i)) by (apply u_increases;apply nat2A_1).
abstract omega.
Defined.
*)
Function computation2 (mi:nat*nat) (carryH:u (nat2A (snd mi)) <=(fst mi)) {measure my_measure mi} : 
  {n : nat | u (nat2A n) <= (fst mi) < u (nat2A (n + 1)%nat)} :=
match  (lt_le_dec (fst mi) (u (nat2A ((snd mi)+1)))) with 
 | left Hl =>  exist (fun (n:nat) => u (nat2A n) <=fst mi< u (nat2A (n+1)%nat)) (snd mi) (conj carryH Hl) 
 | right Hr => computation2 ((fst mi),((snd mi)+1)%nat) Hr 
end.
intros.
unfold my_measure; simpl in *.

assert (u (nat2A ((snd mi) + 1)) > u (nat2A (snd mi))) by (apply u_increases;apply nat2A_1).
abstract omega.
Defined.

End def_rec.

Definition hyp2: (* how to decompose the natural numbers to build the function tau *)
       forall (m : nat) (u : {n : A | std n /\ 0 <=A n} -> nat),
       (forall (x y : {n : A | std n /\ 0 <=A n}), (proj1_sig x) <A (proj1_sig y) -> u x < u y) ->
       {n : nat | u (nat2A n) <= m < u (nat2A (n + 1)%nat)} + {m < u (nat2A 0)%nat}.
Proof.
intros m u Hu.
case (lt_le_dec m (u (nat2A 0)%nat)).
right.
exact l.
left.
change (u (nat2A 0) <= fst (m, 1)) in l.
exact (computation2 u Hu (m,0%nat) l).
Defined.

Definition def_tau : forall 
(ssA : forall k0 : A, std k0 /\ 0 <=A k0 -> A)
(bbA : forall k0 : A, std k0 /\ 0 <=A k0 -> A)
(M : forall (n : A) (Hn : std n /\ 0 <=A n) (k : A) (Hk : std k /\ 0 <=A k),
    k <=A n -> {N : nat | forall m : nat, m >= N -> (ssA n Hn m < bbA k Hk m)%Z}),
nat -> Z.
Proof.
intros ssA bbA M m.
(*assert (Hprop:(forall x y : {n : A | lim n /\ 0 <=A n},
  proj1_sig x <=A proj1_sig y -> def_bigM ssA bbA M x < def_bigM ssA bbA M y)) 
  by apply bigM_increases. (* bigM strictly increasing ... *) *)
case (hyp2 m (def_bigM ssA bbA M) (bigM_increases ssA bbA M)).
intros (x, Hx).
exact (ssA (proj1_sig (nat2A x)) (proj2_sig (nat2A x)) m).
intros; exact 0%Z.
Defined.

Lemma sub_lemma1 : (forall x y z:Z, x<=z -> z<= y -> (Z.abs z)<=(Z.abs y) \/ (Z.abs z) <= (Z.abs x))%Z.
Proof.
intros x y z Hxz Hyz.
destruct (Z_le_gt_dec z 0).
destruct (Z_le_gt_dec x 0).
rewrite (Z.abs_neq z).
rewrite (Z.abs_neq x).
right; omega.
omega.
omega.
destruct (Z_le_gt_dec y 0).
rewrite (Z.abs_neq z).
rewrite (Z.abs_neq y).
left; omega.
omega.
omega.
assert False by omega.
omega.

destruct (Z_le_gt_dec x 0).
destruct (Z_le_gt_dec y 0).


assert False by omega.
omega.
rewrite (Z.abs_eq z).
rewrite (Z.abs_eq y).
left; omega.
omega.
omega.
destruct (Z_le_gt_dec y 0).
assert False by omega.
omega.
rewrite (Z.abs_eq z).
rewrite (Z.abs_eq y).
left; omega.
omega.
omega.
Qed.

Lemma sub_lemma2 : (forall x y z:Z, x<=z -> z<= y -> Z.abs z <= (Z.abs y)+(Z.abs x))%Z.
Proof.
intros.
destruct (sub_lemma1 x y z H H0).
generalize (Z.abs_nonneg x); intros Hnew.
omega.
generalize (Z.abs_nonneg y); intros Hnew.
omega.
Qed.

Lemma lemma1 : forall x y z, x<=A z -> z<=A y -> |z|<=A |y|+|x|.
Proof.
unfold_intros.
destruct_exists.
exists (H+H0+1)%nat.
intros.
apply sub_lemma2.
apply H2; omega.
apply H1; omega.
Qed.

Lemma between_is_P :
forall x y :A, P x -> P y -> forall z, x<=A z -> z<=A y -> P z.
Proof.
intros x y Hx Hy z Hxz Hzy; unfold P in *.
assert (|z|<=A |x|+|y|). 
rewrite plus_comm.
(apply lemma1; assumption).
destruct Hx as [nx [Hnx1 [Hnx2 Hnx]]].
destruct Hy as [ny [Hny1 [Hny2 Hny]]].
exists (nx+ny).
split.
apply ANS2a; assumption.
split.
setoid_replace 0 with (0+0) by ring.
apply lt_plus; assumption.
eapply le_trans.
apply H.
ring_simplify.
apply le_plus; assumption.
Qed.

Lemma A_is_nat : 
forall a:A, std a /\ 0<=A a -> exists n:nat, a=proj1_sig (nat2A n).
Proof.
intros.
apply (nat_like_induction (fun (a:A) => exists n : nat, a = proj1_sig (nat2A n))).
exists 0%nat.
simpl; reflexivity.
intros n Hn Hex.
destruct Hex as [p Hp].
exists (S p)%nat.
simpl.
destruct (nat2A p) as [x Hx].
simpl in *.
now apply f_equal2.
assumption.
Qed.

Lemma proj_nat2A : forall p q, proj1_sig (nat2A p) <=A proj1_sig (nat2A (p+q)).
Proof.
induction q.
replace (p+0)%nat with p by ring.
apply le_refl.
rewrite <- plus_n_Sm.
replace (S (p+q))%nat with ((p+q)+1)%nat by ring.
eapply le_trans.
eassumption.
apply lt_le; apply nat2A_1.
Qed.

Lemma proj_nat2A' : forall p q, p<= q -> proj1_sig (nat2A p) <=A proj1_sig (nat2A q).
Proof.
intros p q Hpq.
destruct (PeanoNat.Nat.le_exists_sub p q Hpq) as [v [Hv1 Hv2]]. 
subst.
rewrite Plus.plus_comm.
apply proj_nat2A.
Qed.

(*Lemma P_dec : forall P:nat -> Prop, (exists N : nat,P N) -> {N:nat | P N}.
Proof.
intros.
Search nat.
destruct H.
*)

Lemma least_upper_bound_principle : 
  forall S:subset, non_empty S -> bound_above S -> 
    (forall alpha beta a b:HRw, upper_bound S beta /\ S alpha /\ (beta [>=] b /\ b [>=] a /\ a [>=] alpha) -> 
       {s:HRw| S s /\ s [>] a}+{upper_bound S b}) -> 
 has_least_upper_bound_weak S.
Proof.
intros S Hnon_empty Hbound Hdec.
elim Hnon_empty; intros s0 Hs0.
elim Hbound; intros b0 Hb0.

pose (s_b := (def_s_b S Hdec s0 b0 Hs0 Hb0)).
(* avec valeurs dans HRw *)
pose (ss := fun k0 Hk0 =>  (projT1  (s_b k0 Hk0))).
pose (bb := fun k0 Hk0 => (projT1 (projT2  (s_b k0 Hk0)))).
(* avec valeurs dans A *)
pose (ssA := (fun k0 Hk0 => proj1_sig (ss k0 Hk0))).
pose (bbA := (fun k0 Hk0 => proj1_sig (bb k0 Hk0))).

assert (HbsA : forall (n:A) (k:A) (Hn:std n /\ 0 <=A n) (Hk: std k /\ 0 <=A k), k <=A n -> ssA n Hn <A bbA k Hk).

assert (Hbs : forall (n:A) (k:A) (Hn:std n /\ 0 <=A n) (Hk: std k /\ 0 <=A k), k <=A n -> bb k Hk [>] ss n Hn).
intros.
assert (HS:(S (ss n Hn))).
unfold ss.
elim (s_b n Hn).
intros sn (bn, (Hsn,(Hbn,H'))).
simpl; solve [intuition].
assert (HB: upper_bound S (bb k Hk)).
unfold bb.
elim (s_b k Hk).
intros sk (bk, (Hsk,(Hbk,H'))).
simpl; solve [intuition].
apply HB; assumption.

intros.
apply HRwgt_Zgt; apply Hbs; assumption.
assert (Hb0s0:  (b0[+] (-w s0)) [>] [0]).
apply HRwgt_HRwplus_inv_r with (s0).
ring_simplify.
apply Hb0; apply Hs0.

(* end asserts *)
unfold ltA in HbsA.
assert (Maux : forall (n : A) (Hn : std n /\ 0 <=A n) (k:A) (Hk : std k /\ 0 <=A k),
       k <=A n -> exists N : nat, forall n0 : nat, n0 > N -> (ssA n Hn n0 < bbA k Hk n0)%Z).
intros; apply HbsA; assumption.
assert (Maux' : forall (n : A) (Hn : std n /\ 0 <=A n) (k:A) (Hk : std k /\ 0 <=A k),
       k <=A n -> exists N : nat, forall n0 : nat, n0 >= N -> (ssA n Hn n0 < bbA k Hk n0)%Z).
intros n Hn k Hk Hnk; destruct (Maux n Hn k Hk Hnk) as [N HN]; exists (N+1)%nat; intros; apply HN; omega.

assert (M:(forall (n : A) (Hn : std n /\ 0 <=A n) (k : A) (Hk : std k /\ 0 <=A k),
       k <=A n -> { N : nat | forall m : nat, m >= N -> (ssA n Hn m < bbA k Hk m)%Z})).
admit. (* to be fixed (easy), we shifted to Set-existential types *)

pose (tau:=def_tau ssA bbA M).

assert (tau_prop: forall n:A, forall Hn:(std n/\0<=A n), (ssA n Hn) <=A tau /\  tau <=A (bbA n Hn)).
intros p Hp.
split.

exists (def_bigM ssA bbA M (exist _ p Hp)). (* we choose M_p *)
intros m Hm. 
unfold tau,def_tau.
destruct (hyp2 m (def_bigM ssA bbA M) (bigM_increases ssA bbA M)) as[[nx Hnx ]|].
assert (Hp1:std (p+1)/\0<=A (p+1)) by (apply std_n_n1; assumption).

destruct (A_is_nat p Hp) as [px Hpx].
subst.

destruct (le_lt_dec px nx)%nat.

apply (s_increases S Hdec s0 b0 Hs0 Hb0) with (bbA:=bbA).
reflexivity.
reflexivity.
apply proj_nat2A'; assumption.

assert ( def_bigM ssA bbA M (nat2A (nx + 1))<m).
assert (nx+1<=px) by omega.
eapply Lt.le_lt_trans.
2:apply Hm.
apply bigM_increases2.
simpl.

apply proj_nat2A'.
assumption.
omega.

assert (m<= def_bigM ssA bbA M  (exist (fun n : A => std n /\ 0 <=A n) p Hp)).
eapply Le.le_trans.
apply lt_le_weak; apply l.
apply bigM_increases2.
simpl.
destruct Hp; assumption.
omega.
(* concludes : ss n <=w Tau *)

exists (def_bigM ssA bbA M (exist _ p Hp)). (* we choose M_p *)
intros m Hm. 
unfold tau,def_tau.
destruct (hyp2 m (def_bigM ssA bbA M) (bigM_increases ssA bbA M)) as[[nx Hnx ]|].
assert (Hp1:std (p+1)/\0<=A (p+1)) by (apply std_n_n1; assumption).

destruct (A_is_nat p Hp) as [px Hpx].
subst.

destruct (le_lt_dec px nx)%nat.
assert (Hle : proj1_sig (nat2A px) <=A proj1_sig (nat2A nx)).
apply proj_nat2A'; assumption.

pose (localM := (M (proj1_sig (nat2A nx)) (proj2_sig (nat2A nx)) (proj1_sig (nat2A px)) Hp Hle)).

apply Z.lt_le_incl. 
apply (proj2_sig localM).

assert (proj1_sig localM <=def_bigM ssA bbA M (nat2A (nx))).
destruct (nat2A nx) as [v Hv].
unfold localM; apply bigM_bigger.

omega.

assert ( def_bigM ssA bbA M (nat2A (nx + 1))<m).
assert (nx+1<=px) by omega.
eapply Lt.le_lt_trans.
2:apply Hm.
apply bigM_increases2.
simpl.

apply proj_nat2A'.
assumption.
omega.

assert (m<= def_bigM ssA bbA M  (exist (fun n : A => std n /\ 0 <=A n) p Hp)).
eapply Le.le_trans.
apply lt_le_weak; apply l.
apply bigM_increases2.
simpl.
destruct Hp; assumption.
omega.
(* concludes : bb n >=w Tau *)

assert (Ptau:(P tau)).
assert (H0:std 0 /\ 0<=A 0) by (split; [apply std0 | apply le_refl]).
eapply between_is_P with (x:=proj1_sig (ss 0 H0)) (y:=proj1_sig (bb 0 H0)).
destruct (ss 0 H0); assumption.
destruct (bb 0 H0); assumption.
apply tau_prop.
apply tau_prop.
 
pose(Tau := (exist (fun x : A => P x) tau Ptau)).
exists Tau.
split.
intros.
assert (HTauv: (v [+] (-w Tau)) [>] [0]).
apply HRwgt_HRwplus_inv_r with (Tau).
ring_simplify; assumption.
(* Check (power_lim2 two_third (proj1 two_third_prop) (proj2 two_third_prop) (b0 [+] (-w s0)) Hb0s0 (v [+] (-w Tau)) HTauv). *)
destruct (power_lim2 two_third (proj1 two_third_prop) (proj2 two_third_prop) (b0 [+] (-w s0)) Hb0s0 (v [+] (-w Tau)) HTauv) 
  as [n [Hn1 [Hn2 Hn3]]].

assert  (HPsb:(Psb S s0 b0 n (conj Hn1 Hn2) (ss n (conj Hn1 Hn2)) (bb n (conj Hn1 Hn2)))).
unfold ss, bb ; destruct (s_b n (conj Hn1 Hn2)) as [x s].
destruct s as [y [r1 [r2 r3]]].
unfold Psb; simpl.
repeat split; assumption.

destruct HPsb as [HH1 [HH2 HH3]].

assert ((((b0 [+] (-w s0)) [*] (mk_HRw n (conj Hn1 Hn2) [+] [1])) [*] power two_third n (conj Hn1 Hn2)) [=] 
  bb n (conj Hn1 Hn2) [+] -w (ss n (conj Hn1 Hn2))).
symmetry.
assert (HRew: exist P (n * w + w) (Padd (n * w) w (HRw_n n (conj Hn1 Hn2)) Pw) [=] (mk_HRw n (conj Hn1 Hn2) [+] [1])).
simpl;intros.
setoid_replace (n * w + w + - (n * w + w)) with a0 by ring.
rewrite abs_pos_val.
ring_simplify.
apply lt_le; apply Aw.
apply le_refl.

rewrite HH3; ring.
assert ((v [+] -w (bb n (conj Hn1 Hn2))) [>] (Tau [+] (-w (ss n (conj Hn1 Hn2))))).
generalize (Hn3 (conj Hn1 Hn2)); intros Hn3'.
rewrite H0 in Hn3'.
apply HRwgt_HRwplus_inv_r with (bb n (conj Hn1 Hn2) [+] (-w Tau)).
ring_simplify; unfold HRwminus; assumption.
assert ( (Tau [+] (-w ss n (conj Hn1 Hn2))) [>=] [0]).
apply HRwge_HRwplus_inv_r with (ss n (conj Hn1 Hn2)).
ring_simplify.
apply Zge_HRwge; apply tau_prop.
assert ( (v [+] (-w bb n (conj Hn1 Hn2))) [>] [0]).
apply HRwgt_HRwge_trans with (Tau [+] (-w ss n (conj Hn1 Hn2))).
assumption.
assumption.
exists (bb n (conj Hn1 Hn2)).
split.
unfold upper_bound; intros.
apply HH2; assumption.
split.
apply HRwgt_HRwplus_inv_r with (-w bb n (conj Hn1 Hn2)).
setoid_replace (bb n (conj Hn1 Hn2) [+] (-w bb n (conj Hn1 Hn2))) with [0] by ring.
assumption.
apply Zge_HRwge; apply tau_prop.
intros mu HmuTau.
assert (HmuTau': (Tau [+] (-w mu)) [>] [0]).
apply HRwgt_HRwplus_inv_r with (mu).
ring_simplify; assumption.
destruct (power_lim2 two_third (proj1 two_third_prop) (proj2 two_third_prop) (b0 [+] (-w s0)) Hb0s0 (Tau [+] (-w mu)) HmuTau') 
  as [k [Hk1 [Hk2 Hk3]]].

assert  (HPsb:(Psb S s0 b0 k (conj Hk1 Hk2) (ss k (conj Hk1 Hk2)) (bb k (conj Hk1 Hk2)))).
unfold ss, bb ; destruct (s_b k (conj Hk1 Hk2)) as [x s].
destruct s as [y [r1 [r2 r3]]].
unfold Psb; simpl.
repeat split; assumption.

destruct HPsb as [HH1 [HH2 HH3]].

assert (((ss k (conj Hk1 Hk2)) [+] (-w mu)) [>] (bb k (conj Hk1 Hk2) [+] (-w Tau))).
generalize (Hk3 (conj Hk1 Hk2)); intros Hk3'.
setoid_replace (((b0 [+] (-w s0)) [*] (mk_HRw k (conj Hk1 Hk2) [+] [1])) [*] power two_third k (conj Hk1 Hk2)) with
((mk_HRw k (conj Hk1 Hk2) [+] [1]) [*] (power two_third k (conj Hk1 Hk2) [*] (b0 [+] (-w s0)))) in Hk3' by ring.
rewrite <- HH3 in Hk3'.
apply HRwgt_HRwplus_inv_l with ( (-w (ss k (conj Hk1 Hk2)) [+] Tau)).
ring_simplify.
rewrite HRwplus_comm.
unfold HRwminus; assumption.
assert (((bb k (conj Hk1 Hk2)) [+] (-w Tau)) [>=] [0]).
apply HRwge_HRwplus_inv_r with (Tau).
ring_simplify.
apply Zge_HRwge; apply tau_prop.
assert ((((ss k (conj Hk1 Hk2))) [+] (-w mu)) [>] [0]).
apply HRwgt_HRwge_trans with (bb k (conj Hk1 Hk2) [+] (-w Tau)). 
assumption.
assumption.
exists (ss k (conj Hk1 Hk2)).
split.
apply HH1.
apply HRwgt_HRwplus_inv_r with (-w mu).
setoid_replace (mu [+] (-w mu)) with [0] by ring.
assumption.
Admitted.

End lub_proof_LS.



(* Local Variables: *)
(* coq-prog-name: "/Users/magaud/.opam/4.09.0/bin/coqtop" *)
(* coq-load-path: ( ("." "HR") ) *)
(* suffixes: .v *)
(* End: *)