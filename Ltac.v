Require Export List.

Ltac add_to_distinct_list x xs := 
match xs with
 | nil     => constr:(x::xs)
 | x::_    => fail 1
 | ?y::?ys => let zs := add_to_distinct_list x ys in constr:(y::zs)
end.

Ltac collect_nats_list xs :=
match goal with
 | [ N : nat |- _ ] => let ys := add_to_distinct_list N xs
                       in collect_nats_list ys
 | _                => xs
end.

Ltac collect_nats := collect_nats_list (@nil nat).

Fixpoint sum_plus1 (l:list nat) : nat :=
match l with
nil => 1
|  x::xs => x+(sum_plus1 xs)
end.

Ltac destruct_one_ex :=
  let tac H := let ph := fresh "H" in (destruct H as [H ph]) in
  let tac2 H := let ph := fresh "H" in let ph' := fresh "H" in
    (destruct H as [H ph ph'])
  in
  let tacT H := let ph := fresh "X" in (destruct H as [H ph]) in
  let tacT2 H := let ph := fresh "X" in let ph' := fresh "X" in
    (destruct H as [H ph ph'])
  in
    match goal with
      | [H : (ex _) |- _] => tac H
      | [H : (sig ?P) |- _ ] => tac H
      | [H : (sigT ?P) |- _ ] => tacT H
      | [H : (ex2 _ _) |- _] => tac2 H
      | [H : (sig2 ?P _) |- _ ] => tac2 H
      | [H : (sigT2 ?P _) |- _ ] => tacT2 H
    end.

Ltac destruct_exists := repeat (destruct_one_ex).

Definition Q:nat->Prop := fun (n:nat) => True.

Goal forall n m k : nat, n=m -> m=k -> n=k -> exists p:nat,Q p.
Proof.
intros.
(*let l := collect_nats in idtac l.*)
let l:= collect_nats in exists (sum_plus1 l).
simpl.
unfold Q; auto.
Qed.