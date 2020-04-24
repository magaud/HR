(*** to be load in toplevel mode ***)

open Euler.LSn2

open Euler
;;

open Colors
;;

open Graphics
;;

open Euler_drawing
;;

(*********** Utilities **************)

let rec list_n n = 
  match n with
      0 -> []
    | _ -> let l = list_n (n-1)
      in l @ [n]
;;

let rec expo x n = if n = 0 then 1 else x * (expo x (n-1))
;;

(******* End Utilities **********)

(********* Used omega numbers **********)
let zero_om = (function (m:nat) -> 0);;

let beta = (function (m:nat) -> (1 lsl (n2b m)))
(* this computes 2^m, where m is the unary representation of an integer *)
;;

let beta2 =(function (m:nat) -> ((1 lsl (n2b m))*(1 lsl (n2b m)))) (* = omega *)
;;
(* this is beta^2 *)

let grand_N = (function (m:int) -> 2*(expo 3 m))
;;
(* N = 2*(3^m) *)


(******* End omega numbers **********)

(******* Start drawing *************)

open_graph ":0 800x600" 
;;

(***********************************)

(******* The line x = 2*t ***********)

let f_deux_m =
  fun m (t, x) -> (beta2 m) * 2
;;

let grand_N = (function m -> (expo 2 m))
;;

draw_function beta zero_om zero_om f_deux_m grand_N 
  [3;6;8] [dark_cyan;light_green;black] 256 [grey2; white; white]
;;


(*draw_function beta zero_om zero_om f_deux_m grand_N 
  [3; 6; 7] [dark_cyan; light_green; black] 256 [grey2; white; white]
;;
*)

wait_next_event [Key_pressed]
;;

clear_graph ()
;;

(********* End The line x = 2*t ***********)

(******* The line x = 3/5*t ***********)

let f_trois_cinq_m =
  fun m (t, x) -> ((((beta2) m) * 3) / 5)
;;

let grand_N = (function m -> (expo 3 m))
;;

resize_window 1200 750
;;

draw_function beta zero_om zero_om f_trois_cinq_m grand_N 
  [1; 2; 3; 4; 8] [dark_green; light_green; pink; dark_cyan; black] 256 
  [grey3; white; grey2; grey1; white]
;;

wait_next_event [Key_pressed]
;;

clear_graph ()
;;

(******* End The line x = 3/5*t ***********)

(******* The parabola x = t^2/6 *************)

let f_par_m =
 fun m (t, x) -> t / 3
;;

let grand_N = (function m -> (2*(expo 3 m)))
;;

draw_function beta zero_om zero_om f_par_m grand_N 
  [0; 1; 2; 3; 7] [dark_green; dark_yellow; dark_cyan; red4; black] 128 [grey1; grey2; grey3; white; white]
;;

wait_next_event [Key_pressed]
;;

clear_graph ()
;;

(******* End The parabola x = t^2/6 *************)

(******* The cubic x = t^3/6 *************)

let f_cub_m =
 fun m (t, x) ->  
   let t_r = ((float_of_int t) /. (float_of_int (eval m beta2)))
   in 
     (int_of_float ((float_of_int (eval m beta2)) *.
		       (3. *. t_r *. t_r))) / 6
;;

let grand_N = (function m -> (expo 3 m))
;;

resize_window 800 750
;;

draw_function beta zero_om zero_om f_cub_m grand_N 
  [0; 1; 2; 3; 5] [dark_green; dark_yellow; dark_cyan; red4; black] 64 [grey1; grey2; grey3; white; white]
;;

wait_next_event [Key_pressed]
;;

clear_graph ()
;;

(******* End The cubic x = t^3/6 *************)


(******* The expontial function x = e^t ********)

let grand_N = (function m -> (expo 3 m))
;;

let f_exp_m = 
 fun m (t, x) -> x / 3
;;

resize_window 600 750
;;

draw_function beta zero_om beta2 f_exp_m grand_N 
  [1; 2; 3; 4] [dark_cyan; pink; dark_green; black] 128 [grey1; grey2; white; white]
;;

wait_next_event [Key_pressed]
;;

clear_graph ()
;;

draw_function beta zero_om beta2 f_exp_m grand_N 
  [1; 2; 3; 5; 6] [dark_cyan; pink; dark_green; dark_yellow; black] 64 [grey1; grey2; white; white; white]
;;

wait_next_event [Key_pressed]
;;

clear_graph ()
;;

resize_window 900 750
;;

draw_function beta zero_om beta2 f_exp_m grand_N 
  [1; 2; 3; 5; 6] [dark_cyan; pink; dark_green; dark_yellow; black] 128 [grey1; grey2; white; white; white]
;;

wait_next_event [Key_pressed]
;;

clear_graph ()
;;

(******* End The expontial function x = e^t ********)


(********** Cosine ************)

let f_cosine_m =
 fun m (t, x) ->  (int_of_float ((float_of_int (eval m beta2)) *.
   (-.sin ((float_of_int t) /. (float_of_int (eval m beta2))))))
;;

let grand_N = (function m -> (expo 3 m))
;;

resize_window 1280 600
;;

draw_function beta zero_om (plusA (plusA beta2 beta2) beta2) f_cosine_m grand_N 
  [3; 4; 5; 7] [dark_cyan; pink; dark_green; black] 128 [grey1; white; white; white]
;;

wait_next_event [Key_pressed]
;;

clear_graph ()
;;

(********** End Cosine ************)

(************* Logarithm **********)

let f_log_m =
 fun m (t, x) ->  (int_of_float ((float_of_int (eval m beta2)) *.
   (2. /. ((float_of_int t) /. (float_of_int (eval m beta2))))))
;;

let grand_N = (function m -> (expo 3 m))
;;

resize_window 1280 600
;;

draw_function beta beta2 zero_om f_log_m grand_N 
  [3; 4; 5; 7] [dark_cyan; pink; dark_green; black] 128 [grey1; white; white; white]
;;

wait_next_event [Key_pressed]
;;

clear_graph ()
;;

(********** End Logarithm *********)

(******** End drawing **************)   

close_graph () 
;;

(***********************************)
