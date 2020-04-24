(* use ./coqidescript to load *)
Require Export HRw0_basic_facts.
(* follows the structure of coq_reals : Rreals.*)
Require Import CSetoids.
Require Import CSemiGroups.
Require Import CMonoids.
Require Import CGroups.
Require Import CornTac.
Require Import CAbGroups.
Require Import CRings.
Require Import CFields.
Require Import COrdFields.
Require Import CReals.

Import mBridges2_LS.
Import LSw.

Definition HRwC := {x:HRw | HRw_congruent x HRw0}.

Definition HRwCequal (x y: HRwC) := HRwequal (proj1_sig x) (proj1_sig y).
Definition HRwCdiff (x y:HRwC) :=  HRwdiff (proj1_sig x) (proj1_sig y).

Lemma irr_HRwC : irreflexive (A:=HRwC) HRwCdiff.
Proof.
red; intros x; destruct x as [x HxC];  simpl.
destruct x as [x HxP]; intro Hor.
destruct Hor as [Hor | Hor]; unfold HRwgt in *;
destruct Hor as [n [ Hn1 [Hn2 Hn3]]];
setoid_replace (n * (x + - x)) with a0 in Hn3 by ring;
apply w_not_neg; assumption.
Qed.

Lemma sym_HRwCdiff : Csymmetric HRwCdiff.
Proof.
red; intros x y; destruct x as [x HxC]; destruct y as [y HyC]. 
unfold HRwCdiff, HRwdiff; simpl;
 intros; solve [intuition].
Qed.

Lemma R2_2 : forall x y, HRw_congruent x HRw0 -> HRw_congruent y HRw0 -> HRwgt x y -> forall z, HRw_congruent z HRw0 ->  (HRwgt x z) or (HRwgt z y).
Proof.
unfold HRw_congruent, congruent.
intros (x,Hx) (y,Hy) HCx HCy Hxy (z,Hz) HCz; simpl in *.
assert (Hxy':{n:A| lim  n /\ 0 <A n /\ w <=A n * (x + - y)}).
admit.
destruct Hxy' as [n [Hn1 [Hn2 Hn3]]].
setoid_replace (n* (x + - y)) with (n*(x + - z) + n*(z + - y)) in Hn3 by ring.
assert (forall k l m:A, m<=A (plusA k l) -> {m<=A (plusA k k)}+{m<=A (plusA l l)}).
unfold leA, plusA.
intros.
assert (H': { N : nat | forall n0 : nat, n0 > N -> (m n0 <= k n0 + l n0)%Z}).
admit.
destruct H'.
 
admit.
destruct (H _ _ _ Hn3) as [Hl | Hr].
left.
exists (n+n).
split.
admit.
split.
admit.
rewrite mult_distr_l.
assumption.
right.
exists (n+n).
split.
admit.
split.
admit.
rewrite mult_distr_l.
assumption.
Qed.

Lemma cotrans_HRwCdiff : cotransitive (A:=HRwC) HRwCdiff.
Proof.
red.
intros (x, HxC) (y, HyC); simpl.
intros Hxy.
assert (Hdec:{x>w y} + {y >w x}).
admit. (* requires changing the definition of HRwdiff (+) *)
intros (Z,HzC).
simpl.
destruct Hdec.
destruct (R2_2 x y HxC HyC h Z).
assumption.
left.
left.
assumption.
right.
left.
assumption.
destruct (R2_2 y x HyC HxC h Z).
unfold HRwdiff.
assumption.
right.
right.
assumption.
left.
right.
assumption.
Qed.

Lemma tight_HRwCequal_HRwCdiff : tight_apart (A:=HRwC) HRwCequal HRwCdiff.
Proof.
red.
intros (x, HxC) (y, HyC).
split.
Check R2_3'.
apply R2_3'. (* that's why we choose to focus on HRw numbers which are congruent to 0 *)
transitivity HRw0.
assumption.
symmetry; assumption.

intros Heq; intros [Hgt | Hgt].
eapply HRwequal_HRwgt_False; [apply Heq | apply Hgt].
eapply HRwequal_HRwgt_False; [symmetry; apply Heq | apply Hgt].
Qed.

Lemma HRwC_is_CSetoid: is_CSetoid HRwC HRwCequal HRwCdiff.
Proof.
constructor.
apply irr_HRwC.
apply sym_HRwCdiff.
apply cotrans_HRwCdiff.
apply tight_HRwCequal_HRwCdiff.
Qed.

Definition HRwCSetoid : CSetoid := Build_CSetoid HRwC HRwCequal HRwCdiff HRwC_is_CSetoid.
Canonical Structure HRwCSetoid.
Canonical Structure HRwCCSetoid := cs_crr HRwCSetoid.

Lemma HRwplus_stable : forall x y, HRw_congruent x HRw0 -> HRw_congruent y HRw0 -> HRw_congruent (x+w y) HRw0.
Proof.
intros (x, Hx) (y, Hy); unfold HRw_congruent, HRw0, congruent; simpl; clear Hx Hy.
intros.
assert (H1': (0 < 2 * r)%Z) by omega.
destruct (H (2*r)%Z H1') as [nx Hx]; clear H.
destruct (H0 (2*r)%Z H1') as [ny Hy]; clear H0.
exists (nx+ny+1)%nat.
intros.
unfold plusA, a0.
rewrite <- (Z.abs_eq r) by omega.
rewrite <- (Z.abs_mul r).
setoid_replace  (r * ((x k + y k - 0) * w l - (x l + y l - 0) * w k))%Z 
with (r * ((x k)* (w l) - (x l) * (w k)) + r* ((y k) * (w l) - (y l) * (w k)))%Z by ring.
apply Zmult_le_reg_r with 2%Z.
omega.
setoid_replace (w k * w l * 2)%Z with ((w k * w l) + (w k * w l))%Z by ring.
rewrite <- (Zmult_comm 2%Z).
rewrite <- (Z.abs_mul 2%Z).
rewrite Z.mul_add_distr_l.
eapply Zle_trans.
apply Zabs_triangle.
do 2 rewrite (Z.abs_mul 2).
do 2 rewrite (Z.abs_mul r).
rewrite (Z.abs_eq 2%Z) by omega.
rewrite (Z.abs_eq r) by omega.
rewrite Z.mul_assoc.
rewrite Z.mul_assoc.
apply Z.add_le_mono.
setoid_replace (x k) with (x k - a0 k)%Z by (unfold a0; ring).
setoid_replace (x l) with (x l - a0 l)%Z by (unfold a0; ring).
apply Hx; omega.
setoid_replace (y k) with (y k - a0 k)%Z by (unfold a0; ring).
setoid_replace (y l) with (y l - a0 l)%Z by (unfold a0; ring).
apply Hy; omega.
Qed.

Definition HRwCplus (x y:HRwC) : HRwC.
destruct x as [x Hx]; destruct y as [y Hy].
exists (x +w y).
apply HRwplus_stable; assumption.
Defined.

Lemma HRwCdiff_reg : forall x1 y1 x2 y2, HRwCdiff (HRwCplus x1 y1) (HRwCplus x2 y2) -> (HRwCdiff x1 x2) or (HRwCdiff y1 y2).
Proof.
intros (x1, Hx1C) (y1, Hy1C) (x2, Hx2C) (y2, Hy2C) Hx1y1x2y2; simpl in *.
unfold HRwdiff in Hx1y1x2y2; simpl.
assert (Hdec:{(x1 +w y1) >w (x2 +w y2)} + {(x2 +w y2) >w (x1 +w y1)}).
admit. (* requires changing HRwdiff def (+) *)
clear Hx1y1x2y2.
destruct Hdec as [Hdec | Hdec].
destruct x1 as [x1 Hx1P];
destruct y1 as [y1 Hy1P];
destruct x2 as [x2 Hx2P];
destruct y2 as [y2 Hy2P]; unfold HRwdiff in *;simpl in *.
left.
destruct Hdec as [n [Hn1 Hn2]]. 
right.
unfold HRw_congruent, congruent in *; simpl in *.

(* destruct Hx1y1x2y2. impossible *)
Admitted. (* should be fixable *)

Lemma HRwCplus_is_setoid_bin_fun: bin_fun_strext HRwCSetoid HRwCSetoid HRwCSetoid HRwCplus.
Proof.
 unfold bin_fun_strext.
 intros x1 x2 y1 y2 H.
apply HRwCdiff_reg; assumption.
Qed.
(*
 elim (total_order_T x1 x2); intro H1.
  elim H1; clear H1; intro H2.
   left.
red;simpl; unfold HRwdiff; right; assumption.
  right.
red; simpl.
assert (HRwdiff (x1+w y1) (x2+w y2)) by (repeat red in H; assumption).
admit. (* comments *)
  left.
red; simpl; unfold HRwdiff; left; assumption.*)


Definition HRwCplus_sbinfun : CSetoid_bin_op HRwCSetoid := Build_CSetoid_bin_op HRwCSetoid HRwCplus HRwCplus_is_setoid_bin_fun.

Lemma HRw_is_CSemiGroup : is_CSemiGroup HRwCSetoid HRwCplus_sbinfun.
Proof.
 unfold is_CSemiGroup, associative.
 intros x y z.
 apply eq_symmetric.
destruct x; destruct y; destruct z; simpl.
apply HRwplus_assoc.
Qed.

Definition HRwCSemiGroup : CSemiGroup := Build_CSemiGroup HRwCSetoid HRwCplus_sbinfun HRw_is_CSemiGroup.
Canonical Structure HRwCSemiGroup.

Definition HRwC0 : HRwC.
exists HRw0.
reflexivity.
Defined.

Lemma HRwC_is_CMonoid : is_CMonoid HRwCSemiGroup (HRwC0).
Proof.
 constructor.
  unfold is_rht_unit.
  intro x; destruct x; simpl.
unfold HRwCequal; simpl.
  rewrite HRwplus_comm.
  apply HRwplus_zero.
 unfold is_lft_unit.
  intro x; destruct x.
 apply HRwplus_zero. 
Qed.

Definition HRwCMonoid : CMonoid := Build_CMonoid _ _ HRwC_is_CMonoid.
Canonical Structure HRwCMonoid.

(** ** HRw real numbers form a group *)

(** negation *)
Lemma HRwopp_stable : forall x, HRw_congruent x HRw0  -> HRw_congruent (-w x) HRw0.
Proof.
intros x Hx.
destruct x as [x HPx].
unfold HRw_congruent, HRwopp, oppA, congruent in *; simpl in *.
intros r Hr.
destruct (Hx r Hr) as [N HN].
exists N.
intros.
setoid_replace ((- x k - a0 k) * w l - (- x l - a0 l) * w k)%Z 
  with (-1 *  (( x k - a0 k)* w l - (x l - a0 l) * w k))%Z by (unfold a0; ring).
rewrite Z.abs_mul by omega.
rewrite Z.abs_neq by omega.
ring_simplify.
apply HN; omega.
Qed.

Definition HRwCopp : HRwC -> HRwC.
intros (x, Hx).
exists (-w x).
apply HRwopp_stable; assumption.
Defined.

Lemma HRwCdiff_Copp : forall x y, HRwCdiff (HRwCopp x) (HRwCopp y) -> HRwCdiff x y.
Proof.
intros (x,Hx) (y,Hy).
simpl.
intros Hdiff; destruct Hdiff as [Hdiff | Hdiff].
unfold HRwdiff; idtac.
right.
eapply HRwgt_HRwplus_inv_r with (-w x +w -w y).
simpl;ring_simplify; assumption.
left.
eapply HRwgt_HRwplus_inv_r with (-w x +w -w y).
simpl;ring_simplify; assumption.
Qed.

Lemma HRwCNeg_sunop : fun_strext (S1:=HRwCSetoid) (S2:=HRwCSetoid) HRwCopp.
Proof.
 unfold fun_strext.
 intros x y H.
 apply HRwCdiff_Copp; assumption.
Qed.

Definition HRwCNeg_op : CSetoid_un_op HRwCMonoid := Build_CSetoid_un_op HRwCSetoid HRwCopp HRwCNeg_sunop.

Lemma HRwC_is_Group : is_CGroup HRwCMonoid HRwCNeg_op.
Proof.
 unfold is_CGroup.
 intro x.
 unfold is_inverse.
 split.
destruct x.
  apply HRwplus_opp.
destruct x; simpl; unfold HRwCequal; simpl.
  rewrite HRwplus_comm.
 apply HRwplus_opp.
Qed.

Definition HRwCGroup := Build_CGroup _ _ HRwC_is_Group.
Canonical Structure HRwCGroup.
(** ** HRw real numbers form an abelian group *)

Lemma HRwC_is_AbGroup : is_CAbGroup HRwCGroup.
Proof.
 unfold is_CAbGroup.
 unfold commutes.
 intros x y.
destruct x; destruct y.
 apply HRwplus_comm.
Qed.

Definition HRwCAbGroup := Build_CAbGroup _ HRwC_is_AbGroup.
Canonical Structure HRwCAbGroup.

(** ** HRw real numbers form a ring *)
Lemma HRwmult_stable : forall x y, HRw_congruent x HRw0 -> HRw_congruent y HRw0 -> HRw_congruent (x *w y) HRw0.
Proof.
intros (x,Hx) (y,Hy); unfold HRw_congruent; simpl; intros Hx0 Hy0.
destruct (congruent0_bounded x Hx0) as [Mx HMx].
destruct (congruent0_bounded y Hy0) as [My HMy].
unfold congruent; simpl; unfold divA, multA; intros r Hr.
destruct (Hx0 r Hr) as [nx Hnx].
destruct (Hy0 r Hr) as [ny Hny].
destruct Aw as [nw Hnw].
exists (nx+ny+nw+1)%nat.

(*intros k Hk l Hl.
replace (x k * y k / w k - a0 k)%Z with (x k * y k / w k)%Z by (unfold a0;ring).
replace (x l * y l / w l - a0 l)%Z with (x l * y l / w l)%Z by (unfold a0;ring).
apply Zmult_lt_0_le_reg_r with (w k * w l)%Z.
setoid_replace 0%Z with (w k * 0)%Z by ring.
apply Zmult_lt_compat_l.
apply Hnw; omega.
apply Hnw; omega.
rewrite (Zmult_comm _ (w k * w l)).
rewrite Zmult_assoc.
rewrite <- (Z.abs_eq (w k * w l * r)).
rewrite <- Z.abs_mul.
replace (w k * w l * r * (x k * y k / w k * w l - x l * y l / w l * w k))%Z with 
(( (w l * w l * r) * ((x k * y k / w k) * w k )) - (w k * w k * r) * ((x l * y l / w l) * w l))%Z by ring.

eapply Zle_trans.
apply Z.abs_triangle.
Search Z.abs.
SearchPattern (Z.abs (_+_)<_)%Z.


Search (_ * (_ + _) = _)%Z.
repeat rewrite <- Z.mul_assoc.
rewrite <- (Z.abs_eq (w k * w l)%Z).
rewrite <- Z.abs_mul.
unfold Zminus.
Check Z.mul_add_distr_r.
rewrite Z.mul_add_distr_r.
unfold Zminus.

rewrite <- (Z.abs_eq r).
rewrite <- (Z.abs_mul).


.unfold a0; ring_simplify.
ring_simplify.

destruct (
exists 0%nat; intros.
pattern ((x k) * (y k))%Z.*)
Admitted. (* proof available on paper HRwmult_stable *)

Definition HRwCmult : HRwC -> HRwC -> HRwC.
intros (x,Hx) (y,Hy).
exists (x*w y).
apply HRwmult_stable; assumption.
Defined.

(** multiplication *)
Lemma HRwCdiff_mult : 
  forall x1 y1 x2 y2, HRwCdiff (HRwCmult x1 y1)  (HRwCmult x2 y2) ->  (HRwCdiff x1 x2) or (HRwCdiff y1 y2).
Proof.
Admitted. (* to investigate : HRwCdiff_mult *)

Lemma HRwCMul_is_csbinop : bin_fun_strext HRwCSetoid HRwCSetoid HRwCSetoid HRwCmult.
Proof.
 unfold bin_fun_strext.
 intros x1 x2 y1 y2 H.
  apply HRwCdiff_mult; assumption.
Qed.

Definition HRwCMul_op : CSetoid_bin_op HRwCMonoid := Build_CSetoid_bin_op HRwCSetoid HRwCmult HRwCMul_is_csbinop.

Lemma HRwMul_assoc : associative (S:=HRwCAbGroup) HRwCMul_op.
Proof.
 unfold associative.
 intros x y z.
 apply eq_symmetric.
destruct x; destruct y; destruct z.
 apply HRwmult_assoc.
Qed.

Lemma HRw_congr01 : HRw_congruent HRw0 HRw1.
Proof.
unfold HRw_congruent, HRw0, HRw1, congruent; simpl.
destruct Aw as [N HN].
intros.
exists (N+1)%nat.
intros.
setoid_replace (- w k * w l - - w l * w k)%Z with 0%Z by ring.
simpl.
setoid_replace (r * 0)%Z with (w k * 0)%Z by ring.
apply Z.lt_le_incl.
apply Zmult_lt_compat_l.
apply HN; omega.
apply HN; omega.
Qed.

Definition HRwC1 : HRwC.
exists HRw1.
symmetry; apply HRw_congr01.
Defined.

Lemma HRwC_is_Ring : is_CRing HRwCAbGroup (HRwC1) HRwCMul_op.
Proof.
 exists HRwMul_assoc.
    constructor.
     unfold is_rht_unit; intro x.
destruct x; simpl; unfold HRwCequal; simpl.
rewrite HRwmult_comm.
apply HRwmult_one.  
    unfold is_lft_unit; intro x.
destruct x; simpl.
apply HRwmult_one.
   unfold commutes.
destruct x; destruct y;
   apply HRwmult_comm.
  unfold distributive; intros x y z; destruct x; destruct y; destruct z;
  apply HRw_distr.
apply HRw1_HRw0.
Qed.

Definition HRwCRing := Build_CRing _ _ _ HRwC_is_Ring.
Canonical Structure HRwCRing.

(** ** The real numbers "built using the Harthong-Reeb line" form a field *)

(** reciprocal *)
Lemma HRwinv_stable : forall x, HRw_congruent x HRw0 -> forall h:HRwdiff x HRw0, HRw_congruent (HRwinv x h) HRw0.
Proof.
destruct Aw as [N HN].
intros; destruct x; unfold HRw0, HRw_congruent, congruent in *; simpl in *.
intros.
destruct (HRwdiff0_diff0_spec_or x p h) as [Ho | Ho].
destruct Ho as [Q HQ].
assert (Hprop :  forall k l, (0 < Z.abs ((w k * w l) / (x k * x l)))%Z).
intros.

(*exists (N+P+Q+1)%nat.
intros.
unfold divA, multA.
setoid_replace ((w k * w k / x k - a0 k) * w l - (w l * w l / x l - a0 l) * w k)%Z
with ((w k * w k / x k) * w l - (w l * w l / x l) * w k)%Z by (unfold a0;ring).
Search (_ <= _)%Z.
apply Zmult_le_reg_r with (Z.abs (x k))%Z.
Print HRwinv.
admit. (* easy *)

repeat rewrite <- Zmult_assoc.
rewrite  <- Z.abs_mul.
intros.
unfold HRwdiff in *; simpl in *.
destruct h as [h | h].

*)
Admitted. (* HRwCdiv_stable *)
Check HRwinv.

Definition HRwCinv : forall x: HRwC, HRwCdiff x HRwC0 -> HRwC.
intros (x,H) Hdiff.
exists (HRwinv x Hdiff).
apply HRwinv_stable; assumption.
Defined.

Definition HRwCrecip : forall x : HRwCRing, x [#] [0] -> HRwCRing := fun x h => HRwCinv x h.

Lemma HRwC_is_Field : is_CField HRwCRing HRwCrecip.
Proof.
 constructor.
destruct x; apply HRwmult_inv.
simpl.
destruct x.
unfold HRwCrecip, HRwCinv, HRwCequal.
change (HRwmult (HRwinv x Hx)  x =w HRw1). (* strange, but no easier way yet... *)
rewrite HRwmult_comm.
apply HRwmult_inv.
Qed. 

Lemma HRwCdiff_inv : 
forall x, forall Hx: HRwCdiff x HRwC0, forall y, forall Hy:HRwCdiff y HRwC0, HRwCdiff (HRwCinv x Hx) (HRwCinv y Hy) -> HRwCdiff x y.
Proof.
Admitted. (* HRwCdiff_inv : to be fixed later *)

Lemma HRwC_is_Field2: forall (x y : HRwCRing) (x_ : x[#][0]) (y_ : y[#][0]),
   HRwCrecip x x_[#]HRwCrecip y y_ -> x[#]y.
Proof.
 intros x y x1 y1 H.
destruct x; destruct y; simpl.
 apply HRwCdiff_inv with (Hx:=x1) (Hy:=y1); assumption.
Qed.
 
Definition HRwCField : CField := Build_CField _ _ HRwC_is_Field HRwC_is_Field2.
Canonical Structure HRwCField.

(** ** HRw real numbers form an ordered field *)
(** greater-than *)

Definition HRwCgt (x y : HRwC) := HRwgt (proj1_sig x) (proj1_sig y).

Lemma HRwCgt_strext : Crel_strext HRwCField HRwCgt.
Proof.
 intros x1 x2 y1 y2.
Admitted. (** HRwCgt_strext *)

Definition HRwCgt_rel : CCSetoid_relation HRwCField := Build_CCSetoid_relation HRwCField HRwCgt HRwCgt_strext.

(** less-than *)
Definition HRwClt (x y:HRwC) := HRwCgt y x.

Lemma HRwClt_strext : Crel_strext HRwCField HRwClt.
Proof.
 intros x1 x2 y1 y2.
 pose (G := HRwCgt_strext y1 y2 x1 x2).
 tauto.
Qed.

Definition HRwCless_rel : CCSetoid_relation HRwCField := Build_CCSetoid_relation HRwCField HRwClt HRwClt_strext.

Definition HRwCge (x y : HRwC) := HRwge (proj1_sig x) (proj1_sig y).
Definition HRwCle (x y : HRwC) := HRwCge y x.

Lemma HRwC_is_OrdField : is_COrdField HRwCField HRwCless_rel HRwCle HRwCgt_rel HRwCge.
Proof.
 constructor.
       constructor.
        unfold Ctransitive.
        (* apply HRwge_trans. *)
(*
       unfold CSetoids.antisymmetric.
       apply Rlt_asym.
      intros x y xy z.
      apply Rplus_lt_compat_r.
      assumption.
     intros x y x0 y0.
     apply Rmult_gt_0_compat; assumption.
    intros x y.
    constructor.
     intro xy.
     elim (total_order_T x y); intro H2.
      elim H2; clear H2; intro H3.
       left; assumption.
      elimtype False; apply xy; assumption.
     right; assumption.
    intro H; destruct H.
     apply: Rlt_not_eq; assumption.
    apply: Rgt_not_eq; assumption.
   intros x y.
   simpl in *.
   unfold Not; split.
    intros; fourier.
   intro.
   apply Rnot_lt_le.
   assumption.
  auto with *.
 auto with *.
Qed.*)
Admitted. (* HRwC_is_OrdField *)

Definition HRwCOrdField : COrdField := Build_COrdField _ _ _ _ _ HRwC_is_OrdField.
Canonical Structure HRwCOrdField.

(** ** Coq real numbers form a real number structure *)

Parameter HRwCCauchy_crit : (nat -> HRwC) -> Prop.
(* TODO to be defined in HRw... *)

Lemma cauchy_prop_cauchy_crit : (CauchySeq HRwCOrdField) ->
  forall s : (nat -> HRwCOrdField), (Cauchy_prop (R:=HRwCOrdField) s) -> (HRwCCauchy_crit s).
Proof.
Admitted. (* cauchy_prod_cauchy_crit *)
(*
 intros x seq cprop.
 unfold Cauchy_prop in cprop.
 unfold Rseries.Cauchy_crit.
 intros eps epsgt.
 elim (cprop ((eps / 2 / 2)%R) (eps2_Rgt_R0 _ (eps2_Rgt_R0 _ epsgt))).
 intros N NProp.
 exists N.
 intros n m ngt mgt.
 assert (AbsSmall (eps / 2) ((seq n) - (seq m)) )%R.
  stepr ((seq n - seq N) + (seq N - seq m))%R.
   stepl (eps / 2 / 2 + eps / 2 / 2)%R.
    apply AbsSmall_plus.
     apply NProp; assumption.
    apply (AbsSmall_minus).
    apply NProp; assumption.
   simpl; field.
  simpl; ring.
 destruct H.
 unfold Rfunctions.R_dist.
 apply Rabs_def1.
  clear - H0 epsgt.
  simpl in *.
  fourier.
 clear - H epsgt.
 simpl in *.
 fourier.
Qed.*)

(** limit *)

Definition HRwCLim : CauchySeq HRwCOrdField -> HRwCOrdField.
Admitted. (* HRwCLim *)

(*
Proof.
 intro x.
 elim x.
 intros seq cprop.
 cut (Rseries.Cauchy_crit seq).
  intro crit.
  elim (R_complete seq crit).
  intros lim uncv.
  exact lim.
 apply (cauchy_prop_cauchy_crit x).
 exact cprop.
Defined.
*)

(** INR is isomorphic to nring *)

Definition INA (n:nat) := (fun (_:nat) => Z.of_nat n).

Lemma Pn : forall n:nat, P (INA n).
Proof.
destruct Aw as [nw Hnw]; unfold a0 in Hnw.
intros; unfold P, INA.
exists (fun _ => (n+1)%nat).
split.
unfold lim, std, absA, leA, ltA, a0.
exists (fun _ => (n+2)%Z).
split.
unfold std.
exists 0%nat; intros; reflexivity.
split.
unfold leA.
exists 0%nat; unfold a0; intros; omega.
exists 0%nat; intros; rewrite Z.abs_eq by omega.
rewrite Nat2Z.inj_add.
apply Z.add_lt_mono_l.
simpl; omega.
split.
unfold ltA,a0.
exists 0%nat; intros.
replace Z0 with (Z.of_nat 0) by ring.
apply Nat2Z.inj_lt; omega.

unfold leA, multA, absA.
exists nw%nat.
intros.
replace (Z.abs n) with ((Z.abs n)*1)%Z by ring.
apply Z.mul_le_mono_nonneg.
apply Zabs_geq_zero. 
apply Zle_trans with n.
rewrite Z.abs_eq; omega.
apply Nat2Z.inj_le; omega.
omega.
assert (0< w n0)%Z by (apply Hnw;omega).
omega.
Qed.

Definition INHRw (n : nat) : HRw := 
exist P (INA n) (Pn n).

Definition INHRwC : nat -> HRwC.
intros n.
exists (INHRw n).
admit. (* INHRwC : n is congruent to 0 ? *)
Defined. 

Axiom proof_irr :forall A:Prop, forall x y:A, x=y.

Lemma HRwC_INHRwC_as_IHRwC : forall n : nat, INHRwC n = nring (R:=HRwCRing) n.
Proof.
(*induction n; simpl.
unfold INHRw, INA, HRw0, a0; simpl.
rewrite (proof_irr _ (Pn 0) P0).
reflexivity.
unfold INHRw, INA in *.
rewrite <- IHn.
simpl.
assert (H1:(P (INA (S n)))) by exact (Pn (S n)).
assert (H2:P ((fun _ : nat => n) + w)) by (exact (Padd ( fun _ : nat => n) w (Pn n) Pw)).
rewrite (proof_irr _ (Pn (S n))  H1).
rewrite (proof_irr _ (Padd ( fun _ : nat => n) w (Pn n) Pw) H2).
Check Pos.of_succ_nat.
assert ((fun _ : nat => Zpos (Pos.of_succ_nat n)) = (plusA (fun _ : nat => Z.of_nat n) w)).
unfold plusA.*)
Admitted. (* HRwC_INHRwC_as_IHRwC *)

Lemma HRwCisReals : is_CReals HRwCOrdField HRwCLim.
Proof.
Admitted. (* HRwCisReals *)
(*
 constructor.
  intros [s hs].
  unfold SeqLimit.
  unfold RLim.
  intros e e0.
  simpl.
  destruct (R_complete s ((cauchy_prop_cauchy_crit (Build_CauchySeq ROrdField s hs) s hs))).
  unfold Rseries.Un_cv in u.
  simpl in *.
  destruct (hs (e/4)) as [N HN].
   simpl.
   fourier.
  exists N.
  intros m Hm.
  destruct (u (e/2)).
   fourier.
  set (z:=max x0 m).
  rstepr (((s m[-]s N)[+](s N[-]s z))[+](s z[-]x)).
  apply AbsSmall_eps_div_two.
   apply AbsSmall_eps_div_two.
    stepl (e/4).
     apply HN; auto.
    change (e / 4 = e * / (0 + 1 + 1) * / (0 + 1 + 1)).
    field.
   apply AbsSmall_minus.
   stepl (e/4).
    unfold z.
    apply HN; eauto with *.
   change (e / 4 = e * / (0 + 1 + 1) * / (0 + 1 + 1)).
   field.
  assert (Hz:(z >= x0)%nat).
   unfold z; eauto with *.
  destruct (Rabs_def2 _ _ (H _ Hz)) as [A0 A1].
  stepl (e/2).
   split; unfold cg_minus; simpl; auto with *.
  change (e / 2 = e * / (0 + 1 + 1)).
  field.
 intro x.
 exists (Zabs_nat (up x)).
 unfold Zabs_nat.
 elim (archimed x).
 destruct (up x); simpl.
*)

Definition HRwCReals : CReals := Build_CReals HRwCOrdField HRwCLim HRwCisReals.
Canonical Structure HRwCReals.





