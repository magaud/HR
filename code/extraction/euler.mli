
type nat =
| O
| S of nat

type comparison =
| Eq
| Lt
| Gt

val hd : 'a1 -> 'a1 list -> 'a1

val map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list

module Pos :
 sig
  val succ : int -> int

  val add : int -> int -> int

  val add_carry : int -> int -> int

  val pred_double : int -> int

  val mul : int -> int -> int

  val compare_cont : comparison -> int -> int -> comparison

  val compare : int -> int -> comparison

  val of_succ_nat : nat -> int
 end

module Z :
 sig
  val double : int -> int

  val succ_double : int -> int

  val pred_double : int -> int

  val pos_sub : int -> int -> int

  val add : int -> int -> int

  val opp : int -> int

  val sub : int -> int -> int

  val mul : int -> int -> int

  val compare : int -> int -> comparison

  val leb : int -> int -> bool

  val ltb : int -> int -> bool

  val of_nat : nat -> int

  val pos_div_eucl : int -> int -> int*int

  val div_eucl : int -> int -> int*int

  val div : int -> int -> int

  val modulo : int -> int -> int
 end

module LSn2 :
 sig
  type coq_A = nat -> int

  val a0 : coq_A

  val a1 : coq_A

  val plusA : coq_A -> coq_A -> coq_A

  val multA : coq_A -> coq_A -> coq_A

  val divA : coq_A -> coq_A -> coq_A

  val modA : coq_A -> coq_A -> coq_A

  val beta : coq_A
 end

val lS_Euler_stepA :
  LSn2.coq_A -> LSn2.coq_A -> LSn2.coq_A -> ((LSn2.coq_A*LSn2.coq_A) ->
  LSn2.coq_A) -> nat -> ((LSn2.coq_A*LSn2.coq_A)*LSn2.coq_A) list

val div_m : nat -> LSn2.coq_A -> LSn2.coq_A -> int

val modulo_m : nat -> LSn2.coq_A -> LSn2.coq_A -> int

val lS_EulerA_m :
  nat -> LSn2.coq_A -> LSn2.coq_A -> LSn2.coq_A -> (nat -> (int*int) -> int)
  -> nat -> ((int*int)*int) list

val euler_m :
  nat -> LSn2.coq_A -> LSn2.coq_A -> LSn2.coq_A -> (nat -> (int*int) -> int)
  -> nat -> ((int*int)*int) list

val euler_it_coq :
  LSn2.coq_A -> LSn2.coq_A -> LSn2.coq_A -> (nat -> (int*int) -> int) -> (nat
  -> nat) -> nat list -> ((int*int)*int) list list

val g_parabole : (LSn2.coq_A*LSn2.coq_A) -> LSn2.coq_A

val g : (LSn2.coq_A*LSn2.coq_A) -> LSn2.coq_A

val resultA0 : ((LSn2.coq_A*LSn2.coq_A)*LSn2.coq_A) list

val resultA1 : ((LSn2.coq_A*LSn2.coq_A)*LSn2.coq_A) list

val print_3 :
  nat -> (LSn2.coq_A*(LSn2.coq_A*LSn2.coq_A)) list -> (int*(int*int)) list

val print_2 :
  nat -> (LSn2.coq_A*(LSn2.coq_A*LSn2.coq_A)) list -> (int*int) list

val print_1 : nat -> (LSn2.coq_A*(LSn2.coq_A*LSn2.coq_A)) list -> int list
