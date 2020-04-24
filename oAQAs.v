(* ssreflect stuff should be available *)

Require Export ssrint matrix.
Require Export HRw.

Lemma v : forall n:nat,n=n.
move =>a.
Abort.

(* coqc -q -R theories MathComp theories/tuple *)

Require Export ZArith.
Check Z.div. (* euclidian division : quotient *)
Check Z.quot. (* rounding toward zero *)
Check N2Z.inj_quot.
Eval compute in (Z_of_nat' 3).



(*Require Export mxalgebra.*)
(*Require Export ssralg.*)


(* should be in order to go *)

(* defining what an AQA is *)
(* reuse Etienne's work *) 
Parameter vector : nat -> Set -> Set.
Check 'rV_2. (* vector row of size 2 *)
Check 'cV_3. (* vector column of size 3 *)

Open Scope ring_scope.

Check mulmx.
Definition transp (d:nat) (X:'rV[Z]_d) := X^T.
Check transp.
Open Scope ring_scope.

Definition divn  (d:nat) (w:int) (v:'rV[int]_d) :  'rV[int]_d := map_mx (fun p => w *~ p) v.
Check divn.
Definition addn  (d:nat)  (v:'rV[int]_d) (w:'rV[int]_d) :  'rV[int]_d := map_mx (fun p => w +~ p) w.

(* to be defined component-wise using div *)


Definition g (d:nat) (M:'M[int]_d):= \tr M.

Definition f (d:nat) (M:'M[int]_d):= \det M.

Definition mult (d:nat) (M:'M[int]_d)(X:'cV[int]_d) := (M *m X).
Check mult.

Check mulmxDl.

Definition AQA (d:nat) (M:'M[int]_d) (V:'cV[int]_d) (w : Z) : 'cV[int]_d -> 'cV[int]_d  :=
fun X => (M *m X) V.

 fun (X:'rV[Z]_d) => let u:=  M *m M (*(X^T) *) in X.
mulmxDl
*)
Definition AQA2 d M V w : nat -> 'M_d -> 'rV_d -> nat -> 'rV_d -> 'rV_d :=
fun (d:nat) M V w X => X + V.
*)

(* defining what a \Omega-AQA is *)
(* HRw is inside a module *)
Parameter d: nat.

Check row.
Parameter oAQA (d:nat) : nat d, HRw -> HRw.
row col

Parameter affine : forall d, oAQA d -> Prop.

(* proving theorem 2 *)
Lemma thm2 : forall f:oAQA d, affine f <-> exists g:(nat ->AQA d), denom(g)=w /\ 
forall x:(* HRw^d *) f x = 


