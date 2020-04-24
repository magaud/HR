Require Export Bridges_order2_LS.

Module lub_spec_LS.

Module Export UU := mBridges2_LS.

Definition least_upper_bound_weak (S:subset) (tau:HRw) : Prop := 
  (forall v:HRw,  v [>] tau -> exists b, upper_bound S b /\ v [>] b /\  b [>=] tau) /\ 
  (forall mu:HRw, tau [>] mu -> exists o:HRw, S o/\ o [>] mu).

Definition has_least_upper_bound_weak (s:subset) : Prop := exists tau, least_upper_bound_weak s tau.

End lub_spec_LS.



