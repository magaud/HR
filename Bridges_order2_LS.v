Require Export LUB_spec.
Require Export LaugwitzSchmieden.
Require Export w.

Module mBridges2_LS.

Import LSw.

Module Export HH := lub_spec(LSw).

(** R2_2' *)
Definition weakly_holds1 (P : Z -> Prop) (a:A) := 
exists M, forall m, (m >M)%nat -> (P (a m)). 

Definition weakly_holds2 (P :Z -> Z -> Prop) (a:A) (b:A) := 
exists M, forall m, (m >M)%nat -> P (a m) (b m). 

Definition weakly_holds3 (P :Z -> Z -> Z -> Prop) (a:A) (b:A) (c:A) := 
exists M, forall m, (m >M)%nat -> P (a m) (b m) (c m). 

Definition weakly_holds4 (P :Z -> Z -> Z -> Z -> Prop) (a:A) (b:A) (c:A) (d:A) := 
exists M, forall m, (m >M)%nat -> P (a m) (b m) (c m) (d m). 


Lemma Z_prop : forall a b c:Z, (a+b>=c -> a+a>=c \/ b+b>=c)%Z.
Proof.
intros; omega.
Qed.

(* ecrire la basic definition pour l'appliquer ici *)
Lemma R2_2' : forall x y,  y [>]x -> forall z:HRw, 
let xx := proj1_sig x in 
let yy := proj1_sig y in 
let zz := proj1_sig z in 
weakly_holds4 (fun x y z w => exists q, (q*(y-z)>= w)%Z \/ (q *(z-x)>= w))%Z xx yy zz w.
Proof.
intros x y; destruct x as [xx Hxx]; destruct y as [yy Hyy]; simpl; intros Hxy.

intros z; destruct z as [zz Hzz]; simpl.

destruct Hxy as [p [Hp1 [Hp2 Hp3]]].
assert (w <=A (p*(yy+ -zz) + p*(zz+ -xx))).
setoid_replace (p * (yy + - zz) + p * (zz + - xx)) with (p * (yy + - xx)) by ring.
assumption.

destruct H as [N HN].
unfold weakly_holds4, plusA, oppA, multA in *.
exists N%nat.
intros.
exists ((p m)+(p m))%Z.
rewrite Z.mul_add_distr_r.
rewrite Z.mul_add_distr_r.
apply Z_prop.
apply Z.le_ge.
apply HN.
assumption.
Qed.

(** R2_3' *)

(* congruent *)

(*Definition congruent (x y:A) : Prop := 
forall r:positive, exists N:nat, forall k l:nat, (k>=N)%nat -> (l>=N)%nat -> 
(Qabs (((x k) - (y k)) # (wp k)) - (((x l) - (y l)) # (wp l))) <= 1 # r.
*)

Definition congruent (x y : A) : Prop := 
forall r:Z, (0<r)%Z ->  exists N:nat, forall k :nat, (k>=N)%nat -> forall l:nat, (l>=N)%nat -> 
(r * (Z.abs (((x k) - (y k)) * (w l) - (((x l) - (y l)) * (w k)))) <= (w k) * (w l))%Z.


Definition HRw_congruent (x y : HRw) :=
congruent (proj1_sig x) (proj1_sig y).

(* regular *)
Definition regular (x:A) : Prop := congruent x a0.
Definition HRw_regular (x : HRw) :=
regular (proj1_sig x).

Lemma prop : forall P1 P2, ~((exists n:A, P1 n) \/ (exists n:A, P2 n)) -> ~exists n:A, P1 n\/P2 n.
Proof.
intros.
intuition.
destruct H0 as [n Hn]; destruct Hn.
apply H1; exists n; assumption.
apply H2; exists n; assumption.
Qed.

(* lim means there is a majorant *)
(* defining majorant and proving the property requires changing the definition of lim into a computational one : exists -> sig *)
Parameter majorant : forall n:A, 0<A n -> lim  n -> Z.
Axiom majorant_prop : forall x H0 Hlim, (0< majorant x H0 Hlim)%Z.
Axiom majorant_prop2 : forall x H0 Hlim n, (x n<= majorant x H0 Hlim)%Z.

Lemma lim_Z : forall x:Z, lim (fun _ => x).
Proof.
unfold lim,std,a1,a0,plusA,leA,ltA; intros.
exists (|(fun _ => x)|+a1); unfold a1,absA,plusA.
assert (Hdec:(x<0\/x>=0)%Z) by omega.
split.
exists 0%nat; intros; trivial.
split.
exists 0%nat; intros.
destruct Hdec.
rewrite Z.abs_neq; omega.
rewrite Z.abs_eq; omega.
exists 0%nat; intros.
destruct Hdec.
rewrite Z.abs_neq; omega.
rewrite Z.abs_eq; omega.
Qed.

Lemma Z_prop2 : forall x y:Z, (x>=y\/x<y)%Z.
Proof.
intros; omega.
Qed.

Lemma between_abs : forall a b c d :Z , (0<d -> d* Z.abs (a - b) <= c -> d*b-c<=d*a/\d*a<=d*b+c)%Z.
Proof.
intros.
rewrite <- (Z.abs_eq d) in H0 by omega.
rewrite <-Z.abs_mul in H0.
replace (d * (a-b))%Z with (d*a - d*b)%Z in H0 by ring.
assert (Hdec:((d*a-d*b<0)\/(d*a-d*b>=0))%Z) by omega.
destruct Hdec.
rewrite Z.abs_neq in *; omega.
rewrite Z.abs_eq in *; omega.
Qed.

Lemma between_abs2 : forall a b, (0<=b -> - b <= a <= b -> (Z.abs a) <= b)%Z.
Proof.
intros.
assert (Hdec:(a<0\/a>=0)%Z) by omega.
destruct Hdec.
rewrite Z.abs_neq in *.
omega.
omega.
rewrite Z.abs_eq in *.
omega.
omega.
Qed.

Lemma R2_3' : forall x y, HRw_congruent x y -> ~HRwdiff x y -> HRwequal x y.  
Proof.
intros x y; destruct x as [xx Hxx]; destruct y as [yy Hyy].
unfold HRw_congruent, HRwdiff; simpl; clear Hxx Hyy.
intros Hc Hdiff.
generalize (prop _ _ Hdiff); intros; revert n H1 H0; clear H.
assert (~(exists q:A, lim q /\ 0 <A q /\ (w <=A q * (xx + - yy) \/ w<=A q * (yy + - xx)))).
intro;apply Hdiff.
destruct H as [n [H1 [H2 H3]]].
destruct H3.
left; exists n; intuition.
right; exists n; intuition.
clear Hdiff.

unfold congruent in Hc.
intros ar Har1 Har2.
pose (r:= majorant ar Har1 Har2).
pose (p:= (3 * r)%Z). 
assert (Hp:(0<p)%Z).
unfold p.
assert (0 < r)%Z by apply majorant_prop.
omega.
assert (H2p:(0<2*p)%Z) by omega.

destruct (Hc (2*p)%Z H2p) as [preK HK]; clear Hc.
destruct Aw as [nw Hnw]; unfold a0 in Hnw.
pose (K:=(preK+nw+1)%nat).
assert (HpreKK:(K>=preK)%nat) by (unfold K; omega).
generalize (HK K HpreKK); clear HK; intros HK.
assert (HK':(forall l:nat, (l>=K)%nat -> 
((2 * p) * ((xx l - yy l) * w K)) - (w K * w l) <= (2*p)* ((xx K - yy K) * w l)
<= ((2 * p) * ((xx l - yy l) * w K)) + (w K * w l))%Z).
intros.
apply between_abs; solve[intuition].

destruct (Z_prop2 (p * (xx K - yy K)) (w K)).
assert (forall l, (l>= K)%nat -> 2*p*(xx l - yy l) >= w l)%Z.
intros.
apply Zmult_ge_reg_r with (p:=w K).
apply Z.lt_gt; apply Hnw; unfold K; omega.
rewrite (Zmult_comm ( w l) (w K)).
apply Zge_trans with (m:=((2*p) *((xx K - yy K) * (w l)) - (w K)*(w l))%Z).
destruct (HK' l H1) as [HH1 HH2]; intros.
apply Z.le_ge.
apply Zplus_le_reg_r with ((w K * (w l))%Z).
replace (2 * p * ((xx K - yy K) * w l) - w K * w l + w K * w l)%Z
with (2 * p * ((xx K - yy K) * w l))%Z by ring.
replace (2 * p * (xx l - yy l) * w K)%Z with (2 * p * ((xx l - yy l) * w K))%Z by ring.
assumption.
replace ((w K)*(w l))%Z with (2* (w K)*(w l) - (w K)*(w l))%Z by ring.
apply Z.le_ge.
ring_simplify.
replace ( 2 * p * ((xx K - yy K) * w l) - w K * w l)%Z with ((2 * p * (xx K - yy K) - (w K)) * (w l))%Z by ring.
apply Zmult_le_compat.
apply Zplus_le_reg_r with (w K).
replace ( 2 * p * (xx K - yy K) - w K + w K)%Z with (2 *( p * (xx K - yy K)))%Z by ring. 
replace ((w K) + (w K))%Z with (2 * (w K))%Z by ring.
omega.
apply Z.le_refl.
assert (0< w K)%Z by (apply Hnw; unfold K; omega).
omega.
assert (0< w l)%Z by (apply Hnw; unfold K in *; omega).
omega.

assert False.
apply H.
exists (fun (_:nat)=> 2*p)%Z.
split.
apply lim_Z.
split.
unfold ltA,a0; exists K; intros; assumption.

left.
unfold leA, multA, plusA, oppA.
exists K.
intros.
apply Z.ge_le.
apply H1.
omega.
solve[intuition].
destruct Har1 as [nr Hnr].
exists (nr+K+1)%nat.
intros l Hl.
assert (0 < ar l)%Z by (apply Hnr; omega).
unfold multA, plusA, oppA, absA.
rewrite <- (Z.abs_eq (ar l)).
rewrite <- Z.abs_mul.
apply between_abs2.
assert (0< w l)%Z by (apply Hnw; unfold K in *; omega).
omega.
split.
destruct (Z_prop2 (xx l + - yy l) 0).
apply Z.le_trans with 0%Z.
assert (0 < w l)%Z by (apply Hnw; unfold K in *; omega).
omega.
assert (0< ar l)%Z by (apply Hnr;omega).
replace 0%Z with ((ar l)*0)%Z by ring.
apply Zmult_le_compat_l.
omega.
omega.
apply Z.le_trans with (r * (xx l + - yy l))%Z.

destruct (Z_prop2 (p * (xx K - yy K)) (- (w K)))%Z.
apply Zmult_le_reg_r with (3*(w K))%Z.
assert (0< w K)%Z by (apply Hnw; unfold K in *; omega).
omega.
replace (- w l * (3 * w K))%Z with (- (2 * w l * w K) - w l * w K)%Z by ring.
replace (r* (xx l + - yy l) * (3 * w K))%Z with ((p * (xx l + - yy l)* w K))%Z by (unfold p; ring). 
apply Z.le_trans with (2*p*(xx l + - yy l) * (w K))%Z.
assert (Hl':(l>=K)) by omega.
destruct (HK' l Hl') as [HH1' HH2'].
apply Z.le_trans with ((2 * p * ((xx K - yy K) * w l)) - (w K)*(w l))%Z.
replace (w l * w K)%Z with (w K * w l)%Z by ring.
apply Zplus_le_compat_r.
replace (- (2 * w l * w K))%Z with ((2 * (- w K)) * w l)%Z by ring.
repeat rewrite Zmult_assoc.
apply Zmult_le_compat_r.
repeat rewrite <- Zmult_assoc.
apply Zmult_le_compat_l.
omega.
omega.
assert (0< w l)%Z by (apply Hnw; unfold K in *; omega).
omega.

replace (2 * p * (xx l + - yy l) * w K)%Z with (2 * p * ((xx l - yy l) * w K))%Z by ring.
unfold Zminus in *;omega.
apply Zmult_le_compat_r.
apply Z.mul_le_mono_neg_r.
assumption.
omega.
assert (0< w K)%Z by (apply Hnw; unfold K in *; omega).
omega.

assert (forall l, (l>= K)%nat -> 2*p*(xx l - yy l) <= - w l)%Z.
intros.
apply Zmult_le_reg_r with (p:=w K).
apply Z.lt_gt; apply Hnw; unfold K; omega.
apply Z.le_trans with (m:=((2*p) *((xx K - yy K) * (w l0)) + (w K)*(w l0))%Z).
destruct (HK' l0 H4) as [HH1 HH2]; intros.
apply Zplus_le_reg_r with (- (w K * (w l0)))%Z.
replace (2 * p * ((xx K - yy K) * w l0) + w K * w l0 + - (w K * w l0))%Z
with (2 * p * ((xx K - yy K) * w l0))%Z by ring.
replace (2 * p * (xx l0 - yy l0) * w K)%Z with (2 * p * ((xx l0 - yy l0) * w K))%Z by ring.
assumption.
replace (- (w l0)*(w K))%Z with ((2 * (- (w K)) + (w K))*(w l0))%Z by ring.
replace ( 2 * p * ((xx K - yy K) * w l0) + w K * w l0)%Z with ((2 * p * (xx K - yy K) + (w K)) * (w l0))%Z by ring.
apply Zmult_le_compat_r.
apply Zplus_le_compat_r.
repeat rewrite <- Zmult_assoc.
apply Zmult_le_compat_l.
omega.
omega.
assert (0 < w l0)%Z by (apply Hnw; unfold K in *; omega).
omega.

assert False.
apply H.
exists (fun (_:nat)=> 2*p)%Z.
split.
apply lim_Z.
split.
unfold ltA,a0; exists K; intros; assumption.

right.
unfold leA, multA, plusA, oppA.
exists K.
intros.
apply Z.ge_le.
assert (2 * p * (xx n + - yy n) <= - w n)%Z.
apply H4.
omega.
replace (2* p* (yy n + - xx n))%Z with  (- (2 * p * (xx n + -yy n)))%Z by ring.
apply Z.le_ge.
apply Zplus_le_reg_l with (2 * p * (xx n + - yy n) - w n)%Z.
ring_simplify.
ring_simplify in H6; omega.
destruct H5.

apply Z.mul_le_mono_neg_r.
omega.
apply majorant_prop2.

destruct (Z_prop2 (xx l + - yy l) 0).
apply Z.le_trans with (2* ((ar l) * (xx l + - yy l)))%Z.
pattern (ar l  * (xx l + - yy l))%Z at 1.
replace (ar l * (xx l + - yy l))%Z with (1*((ar l)*(xx l + - yy l)))%Z by ring.
apply Zmult_le_compat_r.
omega.
replace 0%Z with ((ar l)*0)%Z by ring.
apply Zmult_le_compat_l.
omega.
assert (0 < ar l)%Z.
apply Hnr; omega.
omega.
apply Zmult_le_reg_r with (w K).
apply Z.lt_gt; apply Hnw; unfold K; omega.
apply Z.le_trans with (2 * r * (xx l + - yy l) * (w K))%Z. 
repeat rewrite Zmult_assoc.
apply Zmult_le_compat_r.
apply Zmult_le_compat_r.
apply Zmult_le_compat_l.
apply majorant_prop2.
omega.
omega.
assert (0< w K)%Z by (apply Hnw; unfold K in *; omega).
omega.

apply Zmult_le_reg_r with 3%Z.
omega.
replace ( (w l)*(w K)*3)%Z with (2* (w K) * (w l) + (w K) * (w l))%Z by ring.
replace (2 * r * (xx l + - yy l) * w K * 3)%Z with (2 * p * ((xx l + - yy l) * w K))%Z by (unfold p;ring).
assert (Hl': l>=K) by omega.
destruct (HK' l Hl').

assert (2 * p * ((xx K - yy K)* (w l)) <= 2 * w K * w l)%Z.
repeat rewrite <- Zmult_assoc.
apply Zmult_le_compat_l.
repeat rewrite Zmult_assoc.
apply Zmult_le_compat_r.
omega.
assert (0< w l)%Z by (apply Hnw; unfold K in *; omega).
omega.
omega.

unfold Zminus in *; omega.

apply Z.le_trans with 0%Z.
replace 0%Z with (ar l * 0)%Z by ring.
apply Zmult_le_compat_l.
omega. 
omega.

assert (0< w l)%Z by (apply Hnw; unfold K in *; omega).
omega.
omega.
Qed.


End mBridges2_LS.