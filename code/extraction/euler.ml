
type nat =
| O
| S of nat

type comparison =
| Eq
| Lt
| Gt

(** val hd : 'a1 -> 'a1 list -> 'a1 **)

let hd default = function
| ([]) -> default
| x::_ -> x

(** val map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list **)

let rec map f = function
| ([]) -> ([])
| a::t -> (f a)::(map f t)

module Pos =
 struct
  (** val succ : int -> int **)

  let rec succ = (fun x -> x+1)

  (** val add : int -> int -> int **)

  let rec add = (fun x y -> x+y)

  (** val add_carry : int -> int -> int **)

  and add_carry = (fun x y -> x+y)

  (** val pred_double : int -> int **)

  let rec pred_double = (fun x -> 2*x+1)

  (** val mul : int -> int -> int **)

  let rec mul = (fun x y -> x*y)

  (** val compare_cont : comparison -> int -> int -> comparison **)

  let rec compare_cont r x y =
    (fun fxI fxO fxH n -> if n=1 then fxH () else if (n mod 2)=0 then (fxO (n/2)) else (fxI (n/2)))
      (fun p ->
      (fun fxI fxO fxH n -> if n=1 then fxH () else if (n mod 2)=0 then (fxO (n/2)) else (fxI (n/2)))
        (fun q -> compare_cont r p q)
        (fun q -> compare_cont Gt p q)
        (fun _ -> Gt)
        y)
      (fun p ->
      (fun fxI fxO fxH n -> if n=1 then fxH () else if (n mod 2)=0 then (fxO (n/2)) else (fxI (n/2)))
        (fun q -> compare_cont Lt p q)
        (fun q -> compare_cont r p q)
        (fun _ -> Gt)
        y)
      (fun _ ->
      (fun fxI fxO fxH n -> if n=1 then fxH () else if (n mod 2)=0 then (fxO (n/2)) else (fxI (n/2)))
        (fun _ -> Lt)
        (fun _ -> Lt)
        (fun _ -> r)
        y)
      x

  (** val compare : int -> int -> comparison **)

  let compare =
    compare_cont Eq

  (** val of_succ_nat : nat -> int **)

  let rec of_succ_nat = function
  | O -> 1
  | S x -> succ (of_succ_nat x)
 end

module Z =
 struct
  (** val double : int -> int **)

  let double x =
    (fun fZ0 fZpos fZneg n -> if (n=0) then fZ0 () else if (n>0) then fZpos (n) else fZneg (-n))
      (fun _ -> 0)
      (fun p -> (fun x -> x) ((fun x -> 2*x) p))
      (fun p -> (fun x -> -x) ((fun x -> 2*x) p))
      x

  (** val succ_double : int -> int **)

  let succ_double x =
    (fun fZ0 fZpos fZneg n -> if (n=0) then fZ0 () else if (n>0) then fZpos (n) else fZneg (-n))
      (fun _ -> (fun x -> x) 1)
      (fun p -> (fun x -> x) ((fun x -> 2*x+1) p))
      (fun p -> (fun x -> -x) (Pos.pred_double p))
      x

  (** val pred_double : int -> int **)

  let pred_double x =
    (fun fZ0 fZpos fZneg n -> if (n=0) then fZ0 () else if (n>0) then fZpos (n) else fZneg (-n))
      (fun _ -> (fun x -> -x) 1)
      (fun p -> (fun x -> x) (Pos.pred_double p))
      (fun p -> (fun x -> -x) ((fun x -> 2*x+1) p))
      x

  (** val pos_sub : int -> int -> int **)

  let rec pos_sub x y =
    (fun fxI fxO fxH n -> if n=1 then fxH () else if (n mod 2)=0 then (fxO (n/2)) else (fxI (n/2)))
      (fun p ->
      (fun fxI fxO fxH n -> if n=1 then fxH () else if (n mod 2)=0 then (fxO (n/2)) else (fxI (n/2)))
        (fun q -> double (pos_sub p q))
        (fun q -> succ_double (pos_sub p q))
        (fun _ -> (fun x -> x) ((fun x -> 2*x) p))
        y)
      (fun p ->
      (fun fxI fxO fxH n -> if n=1 then fxH () else if (n mod 2)=0 then (fxO (n/2)) else (fxI (n/2)))
        (fun q -> pred_double (pos_sub p q))
        (fun q -> double (pos_sub p q))
        (fun _ -> (fun x -> x) (Pos.pred_double p))
        y)
      (fun _ ->
      (fun fxI fxO fxH n -> if n=1 then fxH () else if (n mod 2)=0 then (fxO (n/2)) else (fxI (n/2)))
        (fun q -> (fun x -> -x) ((fun x -> 2*x) q))
        (fun q -> (fun x -> -x) (Pos.pred_double q))
        (fun _ -> 0)
        y)
      x

  (** val add : int -> int -> int **)

  let add = (fun x y -> x+y)

  (** val opp : int -> int **)

  let opp = (fun x -> -x)

  (** val sub : int -> int -> int **)

  let sub m n =
    add m (opp n)

  (** val mul : int -> int -> int **)

  let mul = (fun x y -> x*y)

  (** val compare : int -> int -> comparison **)

  let compare = (fun x y -> if (x=y) then Eq else if (x<y) then Lt else Gt)

  (** val leb : int -> int -> bool **)

  let leb x y =
    match compare x y with
    | Gt -> false
    | _ -> true

  (** val ltb : int -> int -> bool **)

  let ltb x y =
    match compare x y with
    | Lt -> true
    | _ -> false

  (** val of_nat : nat -> int **)

  let of_nat = function
  | O -> 0
  | S n0 -> (fun x -> x) (Pos.of_succ_nat n0)

  (** val pos_div_eucl : int -> int -> int*int **)

  let rec pos_div_eucl = (fun x y -> (x/y, x mod y))

  (** val div_eucl : int -> int -> int*int **)

  let div_eucl = (fun x y -> (x/y, x mod y))

  (** val div : int -> int -> int **)

  let div a b =
    let q,_ = div_eucl a b in q

  (** val modulo : int -> int -> int **)

  let modulo a b =
    let _,r = div_eucl a b in r
 end

module LSn2 =
 struct
  type coq_A = nat -> int

  (** val a0 : coq_A **)

  let a0 _ =
    0

  (** val a1 : coq_A **)

  let a1 _ =
    (fun x -> x) 1

  (** val plusA : coq_A -> coq_A -> coq_A **)

  let plusA u v n =
    Z.add (u n) (v n)

  (** val multA : coq_A -> coq_A -> coq_A **)

  let multA u v n =
    Z.mul (u n) (v n)

  (** val divA : coq_A -> coq_A -> coq_A **)

  let divA u v n =
    Z.div (u n) (v n)

  (** val modA : coq_A -> coq_A -> coq_A **)

  let modA u v n =
    Z.modulo (u n) (v n)

  (** val beta : coq_A **)

  let beta =
    Z.of_nat
 end

(** val lS_Euler_stepA :
    LSn2.coq_A -> LSn2.coq_A -> LSn2.coq_A -> ((LSn2.coq_A*LSn2.coq_A) ->
    LSn2.coq_A) -> nat -> ((LSn2.coq_A*LSn2.coq_A)*LSn2.coq_A) list **)

let rec lS_Euler_stepA beta0 a b f = function
| O -> (((LSn2.divA a beta0),(LSn2.divA b beta0)),(LSn2.modA b beta0))::([])
| S k ->
  let r = lS_Euler_stepA beta0 a b f k in
  let p,xhk = hd ((LSn2.a0,LSn2.a0),LSn2.a0) r in
  let ttk,xtk = p in
  let ftk =
    LSn2.divA
      (f
        ((LSn2.plusA (LSn2.multA ttk beta0) (LSn2.modA a beta0)),(LSn2.plusA
                                                                   (LSn2.multA
                                                                    xtk beta0)
                                                                   xhk)))
      beta0
  in
  (((LSn2.plusA ttk LSn2.a1),(LSn2.plusA xtk
                               (LSn2.divA (LSn2.plusA xhk ftk) beta0))),
  (LSn2.modA (LSn2.plusA xhk ftk) beta0))::r

(** val div_m : nat -> LSn2.coq_A -> LSn2.coq_A -> int **)

let div_m m a b =
  Z.div (a m) (b m)

(** val modulo_m : nat -> LSn2.coq_A -> LSn2.coq_A -> int **)

let modulo_m m a b =
  Z.modulo (a m) (b m)

(** val lS_EulerA_m :
    nat -> LSn2.coq_A -> LSn2.coq_A -> LSn2.coq_A -> (nat -> (int*int) ->
    int) -> nat -> ((int*int)*int) list **)

let rec lS_EulerA_m m beta0 a b f = function
| O -> (((div_m m a beta0),(div_m m b beta0)),(modulo_m m b beta0))::([])
| S k0 ->
  let r = lS_EulerA_m m beta0 a b f k0 in
  let p,x_chap = hd ((0,0),0) r in
  let t_tild,x_tild = p in
  let f_tild =
    Z.div
      (f m
        ((Z.add (Z.mul t_tild (beta0 m)) (modulo_m m a beta0)),(Z.add
                                                                 (Z.mul
                                                                   x_tild
                                                                   (beta0 m))
                                                                 x_chap)))
      (beta0 m)
  in
  let s = Z.add x_chap f_tild in
  (((Z.add t_tild ((fun x -> x) 1)),(Z.add x_tild (Z.div s (beta0 m)))),
  (Z.modulo s (beta0 m)))::r

(** val euler_m :
    nat -> LSn2.coq_A -> LSn2.coq_A -> LSn2.coq_A -> (nat -> (int*int) ->
    int) -> nat -> ((int*int)*int) list **)

let euler_m =
  lS_EulerA_m

(** val euler_it_coq :
    LSn2.coq_A -> LSn2.coq_A -> LSn2.coq_A -> (nat -> (int*int) -> int) ->
    (nat -> nat) -> nat list -> ((int*int)*int) list list **)

let euler_it_coq beta0 a b f k_om l_prof =
  map (fun m -> euler_m m beta0 a b f (k_om m)) l_prof

(** val g_parabole : (LSn2.coq_A*LSn2.coq_A) -> LSn2.coq_A **)

let g_parabole = function
| t,_ -> t

(** val g : (LSn2.coq_A*LSn2.coq_A) -> LSn2.coq_A **)

let g =
  g_parabole

(** val resultA0 : ((LSn2.coq_A*LSn2.coq_A)*LSn2.coq_A) list **)

let resultA0 =
  lS_Euler_stepA LSn2.beta LSn2.a0 LSn2.a0 g O

(** val resultA1 : ((LSn2.coq_A*LSn2.coq_A)*LSn2.coq_A) list **)

let resultA1 =
  lS_Euler_stepA LSn2.beta LSn2.a0 LSn2.a0 g (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    O))))))))))))))))))))))))))))))))))))))))))))))))))

(** val print_3 :
    nat -> (LSn2.coq_A*(LSn2.coq_A*LSn2.coq_A)) list -> (int*(int*int)) list **)

let rec print_3 m r =
  map (fun u -> let a,p = u in let b,c = p in (a m),((b m),(c m))) r

(** val print_2 :
    nat -> (LSn2.coq_A*(LSn2.coq_A*LSn2.coq_A)) list -> (int*int) list **)

let rec print_2 m r =
  map (fun u -> let a,p = u in let b,_ = p in (a m),(b m)) r

(** val print_1 :
    nat -> (LSn2.coq_A*(LSn2.coq_A*LSn2.coq_A)) list -> int list **)

let rec print_1 m r =
  map (fun u -> let _,p = u in let b,_ = p in b m) r
