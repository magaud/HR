
open Graphics 
;;

(* To draw a list of pixels at a scale with a given color *)
let tracer color scale l =
  let draw_pixel c w (x, y) = 
    ( set_color c ; fill_rect (x-w) (y-w) (2*w) (2*w) )
  and half = scale/2
  in List.iter (function (x, y) -> (draw_pixel color half (scale*x+half, scale*y+half))) l
;;

(* To draw a grid of a given step with color c *)
let grid c step = 
  let rec v_grid n step =
    match n with
	0 -> moveto 0 0
      | r -> ( lineto (current_x ()) (size_y()) ;
	       moveto (current_x() + step) 0 ; 
	       v_grid (n-1) step )
  and  h_grid n step =
    match n with
	0 -> moveto 0 0
      | r -> ( lineto (size_x ()) (current_y()) ;
	       moveto 0 (current_y() + step) ; 
	       h_grid (n-1) step )
  in
    ( set_color c ; (v_grid ((size_x() / step)+1) step) ; (h_grid ((size_y() / step)+1) step) )	  
;;
