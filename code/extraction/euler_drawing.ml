open Euler
;;

open Graphics
;;

open Draw
;;

(** Utilities **)
let eval n u = u n;;

let extract_list l = 
  List.map (function (a, b, c) -> (a, b)) l
;;

let rec xnat_of_int n =
if (n=0) then O else S (xnat_of_int (n-1));;

let n x= List.map (function l -> (List.map (function ((a,b),c ) -> (a,b,c)) l)) x;;

let rec n2b x = match x with O -> 0 | S n -> (n2b n)+1;;

(** to draw the functions **)
let euler_it beta a b f k_om l_prof = euler_it_coq beta a b f (function y -> xnat_of_int (k_om (n2b y))) (List.map xnat_of_int l_prof);;

let draw_function beta a b f k_om l_prof colors scale scale_colors =
  let result = n (euler_it beta a b f k_om l_prof)
  and scales = (List.map (fun m -> (scale / (eval m beta))) (List.map xnat_of_int l_prof))
  in
    List.iter2 (fun f l -> (f (extract_list l))) (List.map2 (fun c s -> tracer c s) colors scales) result ;
    List.iter2 (fun c s -> (if (c = white) then () else (grid c s))) (List.rev scale_colors) (List.rev scales)
;;
