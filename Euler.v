Require Export Extraction.
Require Export List.
Require Export w_n2.

Export LSn2.

(* computing the m^th first terms of the sequences (these terms are elements of A) *)
Fixpoint LS_Euler_stepA beta a b (f:A *  A -> A) m : list (A * A * A) :=
match m with
O => (a / beta, b / beta, b mod% beta)::nil
| (S k) => let r := (LS_Euler_stepA beta a b f k) in 
let '(ttk, xtk, xhk) := hd (a0, a0, a0)  r in 
let ftk := (f ((ttk * beta) + (a mod% beta) , (xtk * beta) + xhk)) / beta in
( ttk + a1, 
  xtk + (xhk + ftk) / beta,
  (xhk + ftk) mod% beta ) :: r
end.

Definition div_m (m:nat) (a:A) (b:A) := Z.div (a m) (b m).
Definition modulo_m (m:nat) (a:A) (b:A) := Zmod (a m) (b m).

Open Scope Z_scope.

(* computing the same terms as before, but looking only at rank k *)
Fixpoint LS_EulerA_m m beta a b f k : (list (Z * Z * Z)) :=
match k with 
  O => ((div_m m a beta), (div_m m b beta), (modulo_m m b beta))::nil
| S k => let r := (LS_EulerA_m m beta a b f k)
           in 
           let '(t_tild, x_tild, x_chap) := (hd (0%Z,0%Z,0%Z) r)
           in 
           let f_tild := Z.div (f m (t_tild * (beta m) + (modulo_m m a beta), x_tild * (beta m) + x_chap)) (beta m)
           in
           let s := x_chap + f_tild
           in
         (t_tild + 1, x_tild + s / (beta m), (Zmod s (beta m))) :: r
end.

Definition euler_m := LS_EulerA_m. 

Definition Euler_it_coq beta a b f k_om l_prof :=
      List.map (fun m => euler_m m beta a b f (k_om m)) l_prof.

Close Scope Z_scope.

Definition g2 (x:A * A) : A := (a1+a1)* w.
Definition g35 (x:A * A) : A := divA ((a1+a1+a1)* w) (a1+a1+a1+a1+a1).
Definition g_exp (v:A*A) : A := match v with (t,x) => x end.
Definition g_parabole (v:A*A) : A := match v with (t,x) => t end.
Definition g : A*A -> A := g_parabole.

Definition resultA0 := (LS_Euler_stepA beta a0 a0 g (0)).
Eval compute in resultA0.
Eval compute in (List.length resultA0).

Definition resultA1 := (LS_Euler_stepA beta a0 a0 g (50)).

Cd "code/extraction".

Extraction Language OCaml.

Extract Inductive prod => "(*)"  [ "(,)" ].
Extract Inductive bool => "bool" ["true" "false"].
Extract Inductive sumbool => "bool" ["true" "false"].

Extract Inductive positive => "int" ["(fun x -> 2*x+1)" "(fun x -> 2*x)" "1"]
"(fun fxI fxO fxH n -> if n=1 then fxH () else if (n mod 2)=0 then (fxO (n/2)) else (fxI (n/2)))".

Extract Inductive Z => "int" ["0" "(fun x -> x)" "(fun x -> -x)"]
"(fun fZ0 fZpos fZneg n -> if (n=0) then fZ0 () else if (n>0) then fZpos (n) else fZneg (-n))".

Extract Inductive list => "list" ["([])" "(::)"].

(* dummy extractions of useless functions *)
(* Extract Constant Z_of_nat => "(fun x -> let rec n2b x = match x with O -> 0 | S n -> (n2b n)+1 in n2b x)".*)
(*Extract Inductive nat => "int" ["0" "fun x -> x+1"].*)
(*Extract Constant P_of_succ_nat => "(fun x -> x+1)".*)
(*Extract Constant plus => "(fun x y -> x+y)".*)
(*Extract Constant mult => "(fun x y -> x*y)".*)
(*Extract Constant Pcompare => "(fun p1 p2 c -> c)".*)
(*Extract Constant Pdouble_plus_one_mask => "(fun x -> x)".*)
(*Extract Constant Pdouble_mask => "(fun x -> x)". *)

Extract Constant Z.compare => "(fun x y -> if (x=y) then Eq else if (x<y) then Lt else Gt)".
Extract Constant Pos.succ => "(fun x -> x+1)".
Extract Constant Pplus => "(fun x y -> x+y)".
Extract Constant Pplus_carry => "(fun x y -> x+y)".
Extract Constant Pmult => "(fun x y -> x*y)".
Extract Constant Pminus => "(fun x y -> x-y)".
Extract Constant Pdouble_minus_two => "(fun x -> IsNul)". 
Extract Constant Pminus_mask => "(fun x y -> IsNul)".
Extract Constant Pminus_mask_carry => "(fun x y -> IsNul)". 
Extract Constant Pdouble_minus_one => "(fun x -> 2*x+1)".
Extract Constant Zdiv_eucl_POS => "(fun x y -> (x/y, x mod y))".
Extract Constant Z.div_eucl => "(fun x y -> (x/y, x mod y))".

Extract Constant Zplus => "(fun x y -> x+y)".
Extract Constant Zmult => "(fun x y -> x*y)".
Extract Constant Z.opp => "(fun x -> -x)".

Extract Constant Zge_bool => "(fun x y -> x >= y)".
Extract Constant Zgt_bool => "(fun x y -> x > y)".

Extract Constant Z.abs => "(fun x -> if x < 0 then -x else x)".

(** Observing what we extracted **)

Fixpoint print_3 m r := @List.map (A*(A*A)) (Z*(Z*Z)) (fun u => match u with (a, (b, c)) => (a m, (b m,  c m)) end) r.
Fixpoint print_2 m r := @List.map (A*(A*A)) (Z*Z) (fun u => match u with (a, (b, c)) => (a m, b m) end) r.
Fixpoint print_1 m r := @List.map (A*(A*A)) Z (fun u => match u with (a, (b, c)) => (b m) end) r.


Extraction "euler.ml" resultA0 resultA1 Euler_it_coq print_3 print_2 print_1.

Cd "../..".

(*End euler.*)
